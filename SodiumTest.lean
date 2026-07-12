import Sodium.Crypto.Box
import Sodium.Crypto.Sign
import Sodium.Theory.Ristretto

namespace SodiumTest

open Sodium Sodium.Crypto Sodium.Theory

def obvEq {n : Nat} (x y : Option (ByteVector n)) : Bool :=
  x.map (·.toByteArray) == y.map (·.toByteArray)

structure Suite where
  name : String
  cases : List (String × Bool)

def Suite.run (s : Suite) : IO Bool := do
  let failures := s.cases.filter fun (_, ok) => !ok
  if failures.isEmpty then
    IO.println s!"  ✓ {s.name} — {s.cases.length} cases"
    return true
  else
    IO.eprintln s!"  ✗ {s.name} — {failures.length}/{s.cases.length} FAILED"
    for (desc, _) in failures.take 10 do
      IO.eprintln s!"      · {desc}"
    return false

def runAll (suites : List Suite) : IO Unit := do
  IO.println "lawful-axiom property tests"
  let mut ok := true
  let mut total := 0
  for s in suites do
    ok := (← s.run) && ok
    total := total + s.cases.length
  if ok then
    IO.println s!"OK — {total} cases across {suites.length} suites"
  else
    IO.eprintln "FAILED"
    IO.Process.exit 1

private def keys : List (ByteVector 32) := [1, 2, 7, 255].map (ByteVector.replicate 32 ·)
private def msgs : List ByteArray :=
  [ByteArray.empty, "a".toUTF8, "attack at dawn".toUTF8, ⟨Array.replicate 200 (0x41 : UInt8)⟩]
private def ads : List ByteArray := [ByteArray.empty, "context-string".toUTF8]

private def aeadCases (A : Aead) (keys : List (ByteVector A.keyBytes))
    (nonces : List (ByteVector A.nonceBytes)) : List (String × Bool) := Id.run do
  let mut cs := []
  for key in keys do
    for nonce in nonces do
      for ad in ads do
        for msg in msgs do
          let ct := A.encrypt key nonce ad msg
          cs := (s!"decrypt?_encrypt (|msg|={msg.size})", A.decrypt? key nonce ad ct == some msg)
              :: (s!"size_encrypt (|msg|={msg.size})", ct.size == msg.size + A.tagBytes) :: cs
  pure cs

def aeadSuites : List Suite :=
  [ { name := "xsalsa20poly1305.Lawful",
      cases := aeadCases xsalsa20poly1305 keys ([1, 5, 9].map (ByteVector.replicate 24 ·)) },
    { name := "xchacha20poly1305.Lawful",
      cases := aeadCases xchacha20poly1305 keys ([1, 5, 9].map (ByteVector.replicate 24 ·)) },
    { name := "aegis256.Lawful",
      cases := aeadCases aegis256 keys ([1, 5, 9].map (ByteVector.replicate 32 ·)) } ]

private def cScalars : List (ByteVector 32) := [1, 2, 3, 7, 42, 255].map (ByteVector.replicate 32 ·)

private def curveDhCases : List (String × Bool) := Id.run do
  let C : DhFunction := curve25519
  let mut cs := []
  for a in cScalars do
    for b in cScalars do
      match C.mulBase a, C.mulBase b with
      | some pa, some pb =>
        cs := ("mul_comm", obvEq (C.mul a pb) (C.mul b pa))
            :: ("mul_isSome", (C.mul a pb).isSome) :: cs
      | _, _ => cs := ("mulBase_isSome", false) :: cs
  pure cs

def curve25519Suites : List Suite :=
  [ { name := "curve25519.Lawful (DhFunction)", cases := curveDhCases } ]

private def R : PrimeOrderGroup := ristretto255
private def rScalars : List (ByteVector 32) :=
  [1, 3, 7, 42, 200].map fun v => R.scalarReduce (ByteVector.replicate 64 v)
private def rPoints : List (ByteVector 32) := rScalars.filterMap R.mulBase
private def rUniforms : List (ByteVector 64) := [1, 2, 7, 128].map (ByteVector.replicate 64 ·)

private def ristrettoDhCases : List (String × Bool) := Id.run do
  let mut cs := []
  for a in rScalars do
    for b in rScalars do
      match R.mulBase a, R.mulBase b with
      | some pa, some pb =>
        cs := ("mul_comm", obvEq (R.mul a pb) (R.mul b pa))
            :: ("mul_isSome", (R.mul a pb).isSome) :: cs
      | _, _ => cs := ("mulBase_isSome", false) :: cs
  pure cs

private def addCommCases : List (String × Bool) := Id.run do
  let mut cs := []
  for p in rPoints do
    for q in rPoints do
      cs := ("add_comm", obvEq (R.add p q) (R.add q p)) :: cs
  pure cs

private def fromUniformCases : List (String × Bool) :=
  rUniforms.map fun u => ("validPoint_fromUniform", R.validPoint (R.fromUniform u) == true)

private def mulBaseScalarMulCases : List (String × Bool) := Id.run do
  let mut cs := []
  for c in rScalars do
    for x in rScalars do
      match R.mulBase x with
      | some px => cs := ("mulBase_scalarMul", obvEq (R.mulBase (R.scalarMul c x)) (R.mul c px)) :: cs
      | none => cs := ("mulBase_isSome", false) :: cs
  pure cs

private def addMulBaseCases : List (String × Bool) := Id.run do
  let mut cs := []
  for a in rScalars do
    for b in rScalars do
      match R.mulBase a, R.mulBase b, R.mulBase (R.scalarAdd a b) with
      | some pa, some pb, some pc => cs := ("add_mulBase", obvEq (R.add pa pb) (some pc)) :: cs
      | _, _, _ => cs := ("add_mulBase_isSome", false) :: cs
  pure cs

private def scalarMulCommCases : List (String × Bool) := Id.run do
  let mut cs := []
  for a in rScalars do
    for b in rScalars do
      cs := ("scalarMul_comm", (R.scalarMul a b).toByteArray == (R.scalarMul b a).toByteArray) :: cs
  pure cs

private def mulScalarAddCases : List (String × Bool) := Id.run do
  let mut cs := []
  for a in rScalars do
    for b in rScalars do
      for p in rPoints do
        match R.mul a p, R.mul b p, R.mul (R.scalarAdd a b) p with
        | some x, some y, some z => cs := ("mul_scalarAdd", obvEq (R.add x y) (some z)) :: cs
        | _, _, _ => pure ()
  pure cs

private def scalarReducedCases : List (String × Bool) := Id.run do
  let mut cs := []
  for u in rUniforms do
    cs := ("scalarReduced_scalarReduce", R.scalarReduced (R.scalarReduce u) == true) :: cs
  for a in rScalars do
    for b in rScalars do
      cs := ("scalarReduced_scalarAdd", R.scalarReduced (R.scalarAdd a b) == true)
          :: ("scalarReduced_scalarMul", R.scalarReduced (R.scalarMul a b) == true) :: cs
  pure cs

private def schnorrCases : List (String × Bool) := Id.run do
  let S := Crypto.signRistretto255
  let seeds : List (ByteVector 64) :=
    [1, 42, 128, 200, 255].map (ByteVector.replicate 64 ·)
  let mut cs := []
  for seed in seeds do
    for msg in msgs do
      match S.keypair seed with
      | some (pk, sk) =>
        match S.sign msg sk with
        | some sig => cs := (s!"verify_sign (|msg|={msg.size})", S.verify sig msg pk) :: cs
        | none => cs := ("sign_isSome", false) :: cs
      | none => cs := ("keypair_isSome", false) :: cs
  pure cs

def ristretto255Suites : List Suite :=
  [ { name := "ristretto255.Lawful — dh (DhFunction)", cases := ristrettoDhCases },
    { name := "ristretto255.Lawful — add_comm", cases := addCommCases },
    { name := "ristretto255.Lawful — validPoint_fromUniform", cases := fromUniformCases },
    { name := "ristretto255.Lawful — scalarMul_comm", cases := scalarMulCommCases },
    { name := "ristretto255.Lawful — scalarReduced closure", cases := scalarReducedCases },
    { name := "ristretto255.Lawful — mulBase_scalarMul", cases := mulBaseScalarMulCases },
    { name := "ristretto255.Lawful — add_mulBase", cases := addMulBaseCases },
    { name := "ristretto255.Lawful — mul_scalarAdd", cases := mulScalarAddCases },
    { name := "signRistretto255 — verify_sign", cases := schnorrCases } ]

private def natToBV (k x : Nat) : ByteVector k :=
  ⟨⟨(Array.range k).map fun i => UInt8.ofNat (x >>> (8 * i))⟩, by simp [ByteArray.size]⟩

private def M : PrimeOrderGroup := Theory.Ristretto.spec
private def L : Nat := Theory.Ristretto.order

private def bvEq {n : Nat} (x y : ByteVector n) : Bool := x.toByteArray == y.toByteArray

private def modelScalars : List Nat :=
  [0, 1, 2, 7, L - 1, L, L + 1, 2 ^ 255 - 1, 2 ^ 255, 2 ^ 255 + 5, 2 ^ 256 - 1, 123456789]
private def modelNonReduced : List Nat :=
  [0, 1, L, L * L + 42, 2 ^ 512 - 1, 2 ^ 400 + 987654321]

private def modelCases : List (String × Bool) := Id.run do
  let mut cs := []
  for a in modelScalars do
    let va := natToBV 32 a
    cs := (s!"mulBase parity ({a})", (R.mulBase va).isSome == (M.mulBase va).isSome)
        :: (s!"scalarNeg ({a})", bvEq (R.scalarNeg va) (M.scalarNeg va)) :: cs
    for b in modelScalars do
      let vb := natToBV 32 b
      cs := (s!"scalarAdd ({a},{b})", bvEq (R.scalarAdd va vb) (M.scalarAdd va vb))
          :: (s!"scalarMul ({a},{b})", bvEq (R.scalarMul va vb) (M.scalarMul va vb)) :: cs
  for s in modelNonReduced do
    let vs := natToBV 64 s
    cs := (s!"scalarReduce ({s})", bvEq (R.scalarReduce vs) (M.scalarReduce vs)) :: cs
  pure cs

def modelSuites : List Suite :=
  [ { name := "ristretto255 model — matches libsodium FFI", cases := modelCases } ]

end SodiumTest

def main : IO Unit :=
  SodiumTest.runAll (SodiumTest.aeadSuites ++ SodiumTest.curve25519Suites ++
    SodiumTest.ristretto255Suites ++ SodiumTest.modelSuites)
