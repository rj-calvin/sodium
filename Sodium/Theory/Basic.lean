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
  scalarReduced : ByteVector scalarBytes → Bool
  scalarReduce : ByteVector nonReducedBytes → ByteVector scalarBytes
  scalarAdd : ByteVector scalarBytes → ByteVector scalarBytes → ByteVector scalarBytes
  scalarMul : ByteVector scalarBytes → ByteVector scalarBytes → ByteVector scalarBytes
  scalarNeg : ByteVector scalarBytes → ByteVector scalarBytes

structure PrimeOrderGroup.Lawful (G : PrimeOrderGroup) : Prop where
  mul_comm : ∀ a b pa pb, G.mulBase a = some pa → G.mulBase b = some pb →
    G.mul a pb = G.mul b pa
  mul_isSome : ∀ a b pa pb, G.mulBase a = some pa → G.mulBase b = some pb →
    (G.mul a pb).isSome
  scalarMul_comm : ∀ a b, G.scalarMul a b = G.scalarMul b a
  add_comm : ∀ p q, G.add p q = G.add q p
  validPoint_fromUniform : ∀ u, G.validPoint (G.fromUniform u) = true
  scalarReduced_scalarReduce : ∀ s, G.scalarReduced (G.scalarReduce s) = true
  scalarReduced_scalarAdd : ∀ a b, G.scalarReduced a = true → G.scalarReduced b = true →
    G.scalarReduced (G.scalarAdd a b) = true
  scalarReduced_scalarMul : ∀ a b, G.scalarReduced a = true → G.scalarReduced b = true →
    G.scalarReduced (G.scalarMul a b) = true
  mul_scalarAdd : ∀ a b p x y z, G.scalarReduced a = true → G.scalarReduced b = true →
    G.mul a p = some x → G.mul b p = some y → G.mul (G.scalarAdd a b) p = some z →
    G.add x y = some z
  mulBase_scalarMul : ∀ c x px, G.scalarReduced c = true → G.scalarReduced x = true →
    G.mulBase x = some px → G.mulBase (G.scalarMul c x) = G.mul c px
  add_mulBase : ∀ a b pa pb pc, G.scalarReduced a = true → G.scalarReduced b = true →
    G.mulBase a = some pa → G.mulBase b = some pb → G.mulBase (G.scalarAdd a b) = some pc →
    G.add pa pb = some pc

theorem PrimeOrderGroup.Lawful.dh {G : PrimeOrderGroup} (h : G.Lawful) : G.toDhFunction.Lawful where
  mul_comm := h.mul_comm
  mul_isSome := h.mul_isSome

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
  sign : ByteArray → ByteVector secretKeyBytes → Option (ByteVector sigBytes)
  verify : ByteVector sigBytes → ByteArray → ByteVector publicKeyBytes → Bool

structure Sign.Lawful (S : Sign) : Prop where
  verify_sign : ∀ seed pk sk msg sig, S.keypair seed = some (pk, sk) →
    S.sign msg sk = some sig → S.verify sig msg pk = true

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

def schnorr (G : PrimeOrderGroup) (H : Hash) (hH : H.outBytes = G.nonReducedBytes) : Sign where
  name := Lean.Name.str G.name "schnorr"
  publicKeyBytes := G.pointBytes
  secretKeyBytes := G.scalarBytes
  seedBytes := G.nonReducedBytes
  sigBytes := G.pointBytes + G.scalarBytes
  keypair seed := (G.mulBase (G.scalarReduce seed)).map fun pk => (pk, G.scalarReduce seed)
  sign msg sk := do
    let pk ← G.mulBase sk
    let k := G.scalarReduce ((H.hash (sk.toByteArray ++ msg) none).cast hH)
    let R ← G.mulBase k
    let c := G.scalarReduce ((H.hash (R.toByteArray ++ pk.toByteArray ++ msg) none).cast hH)
    let s := G.scalarAdd k (G.scalarMul c sk)
    let _ ← G.mul c pk
    let _ ← G.mulBase s
    return R.append s
  verify sig msg pk :=
    let R := sig.take G.pointBytes (Nat.le_add_right _ _)
    let s := (sig.drop G.pointBytes).cast (by omega)
    let c := G.scalarReduce ((H.hash (R.toByteArray ++ pk.toByteArray ++ msg) none).cast hH)
    match G.mulBase s, G.mul c pk with
    | some sP, some cP => decide (G.add R cP = some sP)
    | _, _ => false

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

theorem schnorr_lawful (G : PrimeOrderGroup) (H : Hash) (hH : H.outBytes = G.nonReducedBytes)
    (hG : G.Lawful) : (schnorr G H hH).Lawful := by
  constructor
  intro seed pk sk msg sig hkp hsig
  simp only [schnorr, Option.pure_def] at hkp hsig ⊢
  obtain ⟨pk0, hpk, rfl, rfl⟩ := Option.map_eq_some_iff.mp hkp
  obtain ⟨pk1, hpk1, hsig⟩ := Option.bind_eq_some_iff.mp hsig
  obtain rfl := Option.some_inj.mp (hpk.symm.trans hpk1)
  obtain ⟨R, hR, hsig⟩ := Option.bind_eq_some_iff.mp hsig
  obtain ⟨cP, hcP, hsig⟩ := Option.bind_eq_some_iff.mp hsig
  obtain ⟨sP, hsP, hsig⟩ := Option.bind_eq_some_iff.mp hsig
  obtain rfl := Option.some_inj.mp hsig
  rw [ByteVector.take_append, ByteVector.drop_append]
  have hsk := hG.scalarReduced_scalarReduce seed
  have hk := hG.scalarReduced_scalarReduce ((H.hash ((G.scalarReduce seed).toByteArray ++ msg) none).cast hH)
  have hc := hG.scalarReduced_scalarReduce ((H.hash (R.toByteArray ++ pk.toByteArray ++ msg) none).cast hH)
  have h2 := (hG.mulBase_scalarMul _ (G.scalarReduce seed) _ hc hsk hpk).trans hcP
  have hadd := hG.add_mulBase _ _ _ _ _ hk (hG.scalarReduced_scalarMul _ _ hc hsk) hR h2 hsP
  simp [hsP, hcP, hadd]

end Sodium.Theory
