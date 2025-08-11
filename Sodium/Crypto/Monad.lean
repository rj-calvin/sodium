import Sodium.Data.ByteArray
import Sodium.FFI.KeyDeriv
import Sodium.FFI.KeyExch
import Sodium.Crypto.Spec

open Lean Std Sodium

namespace Sodium.Crypto

open FFI

variable {spec : Spec}

open KeyExch in
def MetaSpec : Spec where
  name := `curve25519
  nonceBytes := 8
  seedBytes := SEEDBYTES
  publicKeyBytes := PUBLICKEYBYTES
  secretKeyBytes := SECRETKEYBYTES
  sessionKeyBytes := SESSIONKEYBYTES
  sharedBytes := SESSIONKEYBYTES

abbrev MetaSpecSupport := SpecSupport MetaSpec

instance {sα sβ : Spec} {m : Spec → Type} [mα : MetaSpecSupport m sα] [mβ : MetaSpecSupport m sβ]
    : SpecSupport sα m sβ where
  liftSpec x := liftSpec (mα.withSpec x)
  withSpec x := liftSpec (mβ.withSpec x)

structure ContextId where
  name : Name
  deriving BEq, DecidableEq, Ord, Inhabited, Hashable, ToJson, FromJson

namespace ContextId

def index (ctx : ContextId) : UInt64 × UInt64 :=
  match ctx.name with
  | .num p n => (n + 1, p.hash)
  | x => (0, x.hash)

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
  MVarId.mk (.num MetaSpec.name nonce.bytes.toUInt64LE!.toNat)

end NonceId

structure PeerId (spec : Spec := MetaSpec) where
  name : Name
  pkey : PublicKey spec

variable {α σ : Type}

private structure EntropyState (τ : Sodium σ) where
  entropy : EntropyArray τ
  nonces : NameMap (Σ spec, NonceId spec) := ∅

structure CryptoState (τ : Sodium σ) where
  private mtx : Mutex (EntropyState τ)
  ctx : ContextId
  mkey : SecretKey τ MetaSpec

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
  let mtx ← Mutex.new {entropy}
  let key ← KeyDeriv.keygen τ
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

def mkStaleSeed : CryptoM τ (Seed τ spec) := do
  let {mkey, ctx, ..} ← get
  let idx := ctx.index
  let seed ← KeyDeriv.derive τ spec.seedBytes idx.1 idx.2 mkey.bytes
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

instance : MonadNameGenerator (CryptoM τ) where
  getNGen := do
    let nonce ← mkFreshNonceId MetaSpec
    return {namePrefix := MetaSpec.name, idx := nonce.bytes.toUInt64LE!.toNat}
  setNGen _ :=
    return () -- not allowed, so we ignore.

end CryptoM

export CryptoM
  (mkFreshNonceId mkFreshSeed mkStaleSeed withMetaKey resetNonces)

end Sodium.Crypto
