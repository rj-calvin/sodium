import Sodium.Data.ByteVector

namespace Sodium.Theory

def SpecName := Lean.Name

instance : Inhabited SpecName := ⟨@default Lean.Name _⟩

structure Aead where
  name : SpecName
  keyBytes : Nat
  nonceBytes : Nat
  tagBytes : Nat
  encrypt : ByteVector keyBytes → ByteVector nonceBytes → (ad msg : ByteArray) → ByteArray
  decrypt? : ByteVector keyBytes → ByteVector nonceBytes → (ad ct : ByteArray) → Option ByteArray

structure Aead.Lawful (A : Aead) : Prop where
  decrypt?_encrypt : ∀ key nonce ad msg,
    A.decrypt? key nonce ad (A.encrypt key nonce ad msg) = some msg
  size_encrypt : ∀ key nonce ad msg, (A.encrypt key nonce ad msg).size = msg.size + A.tagBytes

structure Hash where
  name : SpecName
  outBytes : Nat
  keyBytes : Nat
  hash : ByteArray → Option (ByteVector keyBytes) → ByteVector outBytes

structure Kdf where
  name : SpecName
  keyBytes : Nat
  contextBytes : Nat
  derive : (n : Nat) → UInt64 → ByteVector contextBytes → ByteVector keyBytes → ByteVector n

structure DhFunction where
  name : SpecName
  scalarBytes : Nat
  pointBytes : Nat
  mulBase : ByteVector scalarBytes → Option (ByteVector pointBytes)
  mul : ByteVector scalarBytes → ByteVector pointBytes → Option (ByteVector pointBytes)

structure DhFunction.Lawful (G : DhFunction) : Prop where
  mul_comm : ∀ a b pa pb, G.mulBase a = some pa → G.mulBase b = some pb →
    G.mul a pb = G.mul b pa
  mul_isSome : ∀ a b pa pb, G.mulBase a = some pa → G.mulBase b = some pb →
    (G.mul a pb).isSome

structure PrimeOrderGroup extends DhFunction where
  uniformBytes : Nat
  nonReducedBytes : Nat
  add : ByteVector pointBytes → ByteVector pointBytes → Option (ByteVector pointBytes)
  sub : ByteVector pointBytes → ByteVector pointBytes → Option (ByteVector pointBytes)
  fromUniform : ByteVector uniformBytes → ByteVector pointBytes
  validPoint : ByteVector pointBytes → Bool
  scalarReduce : ByteVector nonReducedBytes → ByteVector scalarBytes
  scalarAdd : ByteVector scalarBytes → ByteVector scalarBytes → ByteVector scalarBytes
  scalarMul : ByteVector scalarBytes → ByteVector scalarBytes → ByteVector scalarBytes
  scalarNeg : ByteVector scalarBytes → ByteVector scalarBytes

structure PrimeOrderGroup.Lawful (G : PrimeOrderGroup) : Prop where
  dh : G.toDhFunction.Lawful
  add_comm : ∀ p q, G.add p q = G.add q p
  validPoint_fromUniform : ∀ u, G.validPoint (G.fromUniform u) = true
  mul_scalarAdd : ∀ a b p, G.validPoint p = true →
    G.mul (G.scalarAdd a b) p = (G.mul a p).bind fun x => (G.mul b p).bind fun y => G.add x y

structure Box where
  name : SpecName
  publicKeyBytes : Nat
  secretKeyBytes : Nat
  seedBytes : Nat
  nonceBytes : Nat
  macBytes : Nat
  keypair : ByteVector seedBytes → Option (ByteVector publicKeyBytes × ByteVector secretKeyBytes)
  easy : ByteArray → ByteVector nonceBytes → ByteVector publicKeyBytes →
    ByteVector secretKeyBytes → Option ByteArray
  open? : ByteArray → ByteVector nonceBytes → ByteVector publicKeyBytes →
    ByteVector secretKeyBytes → Option ByteArray

structure Box.Lawful (B : Box) : Prop where
  open?_easy : ∀ seedA seedB pkA skA pkB skB nonce msg,
    B.keypair seedA = some (pkA, skA) → B.keypair seedB = some (pkB, skB) →
    (B.easy msg nonce pkB skA).bind (fun ct => B.open? ct nonce pkA skB) = some msg

structure Kx where
  name : SpecName
  publicKeyBytes : Nat
  secretKeyBytes : Nat
  seedBytes : Nat
  sessionKeyBytes : Nat
  keypair : ByteVector seedBytes → Option (ByteVector publicKeyBytes × ByteVector secretKeyBytes)
  clientKeys : ByteVector publicKeyBytes → ByteVector secretKeyBytes →
    ByteVector publicKeyBytes → Option (ByteVector sessionKeyBytes × ByteVector sessionKeyBytes)
  serverKeys : ByteVector publicKeyBytes → ByteVector secretKeyBytes →
    ByteVector publicKeyBytes → Option (ByteVector sessionKeyBytes × ByteVector sessionKeyBytes)

structure Kx.Lawful (K : Kx) : Prop where
  session_agree : ∀ seedC seedS pkC skC pkS skS,
    K.keypair seedC = some (pkC, skC) → K.keypair seedS = some (pkS, skS) →
    (K.clientKeys pkC skC pkS).map Prod.swap = K.serverKeys pkS skS pkC

structure Sign where
  name : SpecName
  publicKeyBytes : Nat
  secretKeyBytes : Nat
  seedBytes : Nat
  sigBytes : Nat
  keypair : ByteVector seedBytes → Option (ByteVector publicKeyBytes × ByteVector secretKeyBytes)
  sign : ByteArray → ByteVector secretKeyBytes → ByteVector sigBytes
  verify : ByteVector sigBytes → ByteArray → ByteVector publicKeyBytes → Bool

structure Sign.Lawful (S : Sign) : Prop where
  verify_sign : ∀ seed pk sk msg, S.keypair seed = some (pk, sk) →
    S.verify (S.sign msg sk) msg pk = true

def dhBox (G : DhFunction) (A : Aead)
    (kdf : ByteVector G.pointBytes → ByteVector A.keyBytes) : Box where
  name := Lean.Name.append G.name A.name
  publicKeyBytes := G.pointBytes
  secretKeyBytes := G.scalarBytes
  seedBytes := G.scalarBytes
  nonceBytes := A.nonceBytes
  macBytes := A.tagBytes
  keypair seed := (G.mulBase seed).map fun pk => (pk, seed)
  easy msg nonce pk sk := (G.mul sk pk).map fun q => A.encrypt (kdf q) nonce .empty msg
  open? ct nonce pk sk := (G.mul sk pk).bind fun q => A.decrypt? (kdf q) nonce .empty ct

def dhKx (G : DhFunction) (n : Nat)
    (kdf : ByteVector G.pointBytes → ByteVector G.pointBytes → ByteVector G.pointBytes →
      ByteVector n × ByteVector n) : Kx where
  name := G.name
  publicKeyBytes := G.pointBytes
  secretKeyBytes := G.scalarBytes
  seedBytes := G.scalarBytes
  sessionKeyBytes := n
  keypair seed := (G.mulBase seed).map fun pk => (pk, seed)
  clientKeys pk sk spk := (G.mul sk spk).map fun q => kdf q pk spk
  serverKeys pk sk cpk := (G.mul sk cpk).map fun q => (kdf q cpk pk).swap

def schnorr (G : PrimeOrderGroup) (H : Hash) : Sign where
  name := Lean.Name.str G.name "schnorr"
  publicKeyBytes := G.pointBytes
  secretKeyBytes := G.scalarBytes
  seedBytes := G.scalarBytes
  sigBytes := G.pointBytes + G.scalarBytes
  keypair := sorry
  sign := sorry
  verify := sorry

theorem dhBox_lawful (G : DhFunction) (A : Aead) (kdf : ByteVector G.pointBytes → ByteVector A.keyBytes)
    (hG : G.Lawful) (hA : A.Lawful) : (dhBox G A kdf).Lawful := by
  constructor
  intro seedA seedB pkA skA pkB skB nonce msg hkA hkB
  simp only [dhBox] at hkA hkB ⊢
  obtain ⟨pa, hpa, rfl, rfl⟩ := Option.map_eq_some_iff.mp hkA
  obtain ⟨pb, hpb, rfl, rfl⟩ := Option.map_eq_some_iff.mp hkB
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hG.mul_isSome seedA seedB pkA pkB hpa hpb)
  have hcomm := hG.mul_comm seedA seedB pkA pkB hpa hpb
  rw [hq] at hcomm
  simp [hq, ← hcomm, hA.decrypt?_encrypt]

private def dhBoxCx : DhFunction where
  name := `cx
  scalarBytes := 32
  pointBytes := 32
  mulBase _ := some default
  mul _ _ := none

private def dhBoxCxAead : Aead where
  name := `cx
  keyBytes := 32
  nonceBytes := 24
  tagBytes := 0
  encrypt _ _ _ msg := msg
  decrypt? _ _ _ ct := some ct

theorem dhBox_mul_comm_insufficient :
    ∃ (G : DhFunction) (A : Aead) (kdf : ByteVector G.pointBytes → ByteVector A.keyBytes),
      (∀ a b pa pb, G.mulBase a = some pa → G.mulBase b = some pb → G.mul a pb = G.mul b pa) ∧
      A.Lawful ∧ ¬ (dhBox G A kdf).Lawful := by
  refine ⟨dhBoxCx, dhBoxCxAead, id, fun _ _ _ _ _ _ => rfl,
    ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩, fun h => ?_⟩
  have hx := h.open?_easy default default default default default default default .empty rfl rfl
  simp [dhBox, dhBoxCx, dhBoxCxAead] at hx

theorem dhKx_lawful (G : DhFunction) (n : Nat)
    (kdf : ByteVector G.pointBytes → ByteVector G.pointBytes → ByteVector G.pointBytes →
      ByteVector n × ByteVector n)
    (hG : G.Lawful) : (dhKx G n kdf).Lawful := by
  constructor
  intro seedC seedS pkC skC pkS skS hkC hkS
  simp only [dhKx] at hkC hkS ⊢
  cases hpc : G.mulBase seedC with
  | none => simp [hpc] at hkC
  | some pc =>
    cases hps : G.mulBase seedS with
    | none => simp [hps] at hkS
    | some ps =>
      obtain ⟨rfl, rfl⟩ : pc = pkC ∧ seedC = skC := by simpa [hpc] using hkC
      obtain ⟨rfl, rfl⟩ : ps = pkS ∧ seedS = skS := by simpa [hps] using hkS
      rw [← hG.mul_comm seedC seedS pc ps hpc hps]
      simp only [Option.map_map]
      rfl

theorem schnorr_lawful (G : PrimeOrderGroup) (H : Hash) (hG : G.Lawful) :
    (schnorr G H).Lawful := sorry

def xsalsa20poly1305 : Aead where
  name := `xsalsa20poly1305
  keyBytes := 32
  nonceBytes := 24
  tagBytes := 16
  encrypt := sorry
  decrypt? := sorry

def xchacha20poly1305 : Aead where
  name := `xchacha20poly1305
  keyBytes := 32
  nonceBytes := 24
  tagBytes := 16
  encrypt := sorry
  decrypt? := sorry

def aegis256 : Aead where
  name := `aegis256
  keyBytes := 32
  nonceBytes := 32
  tagBytes := 32
  encrypt := sorry
  decrypt? := sorry

def blake2b : Hash where
  name := `blake2b
  outBytes := 64
  keyBytes := 32
  hash := sorry

def kdfBlake2b : Kdf where
  name := `blake2b
  keyBytes := 32
  contextBytes := 8
  derive := sorry

def curve25519 : DhFunction where
  name := `curve25519
  scalarBytes := 32
  pointBytes := 32
  mulBase := sorry
  mul := sorry

def ristretto255 : PrimeOrderGroup where
  name := `ristretto255
  scalarBytes := 32
  pointBytes := 32
  uniformBytes := 64
  nonReducedBytes := 64
  mulBase := sorry
  mul := sorry
  add := sorry
  sub := sorry
  fromUniform := sorry
  validPoint := sorry
  scalarReduce := sorry
  scalarAdd := sorry
  scalarMul := sorry
  scalarNeg := sorry

def hsalsa20 : ByteVector 32 → ByteVector 32 := sorry
def hchacha20 : ByteVector 32 → ByteVector 32 := sorry
def blake2b32 : ByteVector 32 → ByteVector 32 := sorry

theorem curve25519_lawful : curve25519.Lawful := sorry
theorem ristretto255_lawful : ristretto255.Lawful := sorry
theorem xsalsa20poly1305_lawful : xsalsa20poly1305.Lawful := sorry

def box : Box := dhBox curve25519 xsalsa20poly1305 hsalsa20
def boxXchacha20poly1305 : Box := dhBox curve25519 xchacha20poly1305 hchacha20
def boxRistretto255 : Box := dhBox ristretto255.toDhFunction xchacha20poly1305 blake2b32
def kx : Kx := dhKx curve25519 32 sorry
def signRistretto255 : Sign := schnorr ristretto255 blake2b

theorem box_lawful : box.Lawful :=
  dhBox_lawful curve25519 xsalsa20poly1305 hsalsa20 curve25519_lawful xsalsa20poly1305_lawful

end Sodium.Theory
