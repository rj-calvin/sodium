import Sodium.Data.ByteArray
import Sodium.FFI.KeyDeriv
import Sodium.Crypto.Spec

open Lean Std Sodium

namespace Sodium.Crypto

open FFI

variable {spec : Spec}

def MetaSpec : Spec where
  name := `meta
  nonceBytes := 8
  seedBytes := 32
  secretKeyBytes := 32
  sessionKeyBytes := 32

structure ContextId where
  name : Name
  deriving BEq, DecidableEq, Ord, Inhabited, Hashable, ToJson, FromJson

namespace ContextId

def index (ctx : ContextId) : UInt64 × UInt64 :=
  match ctx.name with
  | .num p n => (p.hash, n + 1)
  | x => (x.hash, 0)

def ofMVarId (mvarId : MVarId) : ContextId := ⟨mvarId.name⟩

end ContextId

namespace NonceId

def hash : NonceId spec → UInt64 := ByteArray.hash ∘ NonceId.bytes
instance : Hashable (NonceId spec) := ⟨hash⟩

def toContextId (nonce : NonceId spec) :=
  ContextId.mk (.num spec.name nonce.hash.toNat)

/--
  Create a "unique" MVarId.

  Uniqueness is obviously not guaranteed in a purist sense, but can still be useful for
  creating synthetic goals.
-/
def toMVarId (nonce : NonceId MetaSpec) :=
  MVarId.mk (.num spec.name nonce.hash.toNat)

end NonceId

variable {α σ : Type}

private structure EntropyState (τ : Sodium σ) where
  entropy : EntropyArray τ
  nonces : NameMap (Σ spec, NonceId spec) := ∅

structure CryptoState (τ : Sodium σ) where
  private mtx : Mutex (EntropyState τ)
  ctx : ContextId
  mkey : SecretKey τ MetaSpec
  pkeys : NameMap (Σ spec, PublicKey spec) := ∅
  skeys : NameMap (Σ spec, SecretKey τ spec) := ∅
  sessions : NameMap (Σ spec, SessionKey τ spec) := ∅
  secrets : NameMap (Σ spec, SharedSecret τ spec) := ∅
  seeds : NameMap (Σ spec, Seed τ spec) := ∅

inductive CryptoMessage
  | insufficientEntropy (bytes : Nat)
  | invariantFailure (decl : Name)
  deriving BEq, Hashable, Inhabited

@[coe] def CryptoMessage.toMessageData : CryptoMessage → MessageData
  | .insufficientEntropy bytes => m!"insufficient entropy bytes allocated (expected at least {bytes} bytes)"
  | .invariantFailure decl => m!"invariant failure in {decl}"

instance : ToMessageData CryptoMessage := ⟨CryptoMessage.toMessageData⟩

@[coe] def CryptoMessage.toException (e : CryptoMessage) : Exception :=
  .error .missing (e.toMessageData)

instance : Coe CryptoMessage Exception := ⟨CryptoMessage.toException⟩

abbrev CryptoM (τ : Sodium σ) := StateRefT (CryptoState τ) CoreM

variable {τ : Sodium σ}

def throwInsufficientEntropy (bytes : Nat) : CryptoM τ α :=
  throw (CryptoMessage.insufficientEntropy bytes).toException

def throwInvariantFailure (decl : Name := by exact decl_name%) : CryptoM τ α :=
  throw (CryptoMessage.invariantFailure decl).toException

namespace CryptoM

register_option crypto.entropyBytes : Nat := {
  defValue := 24 * 256
  descr := "The number of random bytes to allocate for entropy."
}

def toCoreM (x : {σ : Type} → (τ : Sodium σ) → CryptoM τ α) (ctx : ContextId := ⟨.anonymous⟩) : CoreM α := do
  let τ ← init Unit
  let entropy ← EntropyArray.new τ (crypto.entropyBytes.get (← getOptions)).toUSize
  let key ← KeyDeriv.keygen τ
  let mtx ← Mutex.new {entropy}
  if h : key.size = MetaSpec.secretKeyBytes then
    StateRefT'.run' (x τ) {mtx, ctx, mkey := ⟨key, h⟩}
  else throwError (CryptoMessage.invariantFailure decl_name%).toMessageData

def toIO (ctx : Elab.ContextInfo) (x : {σ : Type} → (τ : Sodium σ) → CryptoM τ α) : IO α := do
  ctx.runCoreM <| toCoreM x (ctx := ⟨ctx.currNamespace⟩)

def resetNonces : CryptoM τ Unit := do
  let mtx := (← get).mtx
  mtx.atomically <| modify ({· with nonces := ∅})

def mkFreshNonceId (spec : Spec := MetaSpec) : CryptoM τ (NonceId spec) := do
  if h : spec.nonceBytes = 0 then
    return ⟨.empty, by simp [ByteArray.empty, ByteArray.size, ByteArray.emptyWithCapacity, h]⟩
  let mtx := (← get).mtx
  mtx.atomically fun ref => do
    let st ← ref.get
    if let some ⟨_, stale⟩ := st.nonces.find? spec.name then
      let nonce := stale.bytes.succ
      if h : !nonce.isZero ∧ nonce.size = spec.nonceBytes then
        let nonces := st.nonces.insert spec.name ⟨spec, ⟨nonce, h.2⟩⟩
        ref.set {st with nonces}
        return ⟨nonce, h.2⟩
    let (nonce, st) ← next st
    ref.set st
    return nonce
where
  next (st : EntropyState τ) : CryptoM τ (NonceId spec × EntropyState τ) := do
    let {nonces, entropy, ..} := st

    let (nonce, entropy) ←
      if entropy.size - entropy.off < spec.nonceBytes then
        let entropy ← entropy.refresh τ
        entropy.extract τ spec.nonceBytes
      else
        entropy.extract τ spec.nonceBytes

    if h : nonce.size = spec.nonceBytes then
      let nonces := nonces.insert spec.name ⟨spec, ⟨nonce, h⟩⟩
      return (⟨nonce, h⟩, {st with nonces, entropy})
    else throwInsufficientEntropy spec.nonceBytes

def mkFreshSeed : CryptoM τ (Seed τ spec) := do
  let seed ← SecureArray.new τ spec.seedBytes
  if h : seed.size = spec.seedBytes then
    return ⟨seed, h⟩
  else throwInvariantFailure

def withMetaKey (ctx : ContextId) (x : {σ : Type} → (τ : Sodium σ) → CryptoM τ α) : CryptoM τ α := do
  let st ← get
  let idx := ctx.index
  let key ← KeyDeriv.derive τ MetaSpec.secretKeyBytes idx.1 idx.2 st.mkey.bytes
  if h : key.size = MetaSpec.secretKeyBytes then
    liftM (StateRefT'.run' (x τ) {st with ctx, mkey := ⟨key, h⟩})
  else throwInvariantFailure

def findSeed? (name : Name) : CryptoM τ (Option (Seed τ spec)) := do
  let {seeds, ..} ← get
  let some seed := seeds.find? name | return none
  if h : spec = seed.1 then
    return some (h ▸ seed.2)
  else return none

def findSession? (name : Name) : CryptoM τ (Option (SessionKey τ spec)) := do
  let {sessions, ..} ← get
  let some session := sessions.find? name | return none
  if h : spec = session.1 then
    return some (h ▸ session.2)
  else return none

def findSecret? (name : Name) : CryptoM τ (Option (SharedSecret τ spec)) := do
  let {secrets, ..} ← get
  let some secret := secrets.find? name | return none
  if h : spec = secret.1 then
    return some (h ▸ secret.2)
  else return none

def findKeyPair? (name : Name) : CryptoM τ (Option (KeyPair τ spec)) := do
  let {pkeys, skeys, ..} ← get
  let some public := pkeys.find? name | return none
  let some secret := skeys.find? name | return none
  if h : spec = public.1 ∧ spec = secret.1 then
    return some ⟨h.1 ▸ public.2, h.2 ▸ secret.2⟩
  else return none

def findPublicKey? (name : Name) : CryptoM τ (Option (PublicKey spec)) := do
  let {pkeys, ..} ← get
  let some public := pkeys.find? name | return none
  if h : spec = public.1 then
    return some (h ▸ public.2)
  else return none

def findSecretKey? (name : Name) : CryptoM τ (Option (SecretKey τ spec)) := do
  let {skeys, ..} ← get
  let some secret := skeys.find? name | return none
  if h : spec = secret.1 then
    return some (h ▸ secret.2)
  else return none

instance : MonadNameGenerator (CryptoM τ) where
  getNGen := do
    let nonce ← mkFreshNonceId
    return {namePrefix := MetaSpec.name, idx := nonce.hash.toNat}
  setNGen _ :=
    return () -- not allowed, so we ignore.

end CryptoM

export CryptoM
  (mkFreshNonceId mkFreshSeed withMetaKey resetNonces
    findSeed? findSession? findSecret? findKeyPair? findPublicKey? findSecretKey?)

end Sodium.Crypto
