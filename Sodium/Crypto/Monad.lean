import Init.Control.StateRef
import Sodium.Data.ByteArray
import Sodium.FFI.Basic
import Sodium.Crypto.Spec

open Lean Std Sodium

namespace Sodium.Crypto

/-- Nonce (number used only once) type for uniqueness tracking -/
structure NonceId (spec : Spec) where
  bytes : ByteArray
  size_eq_nonce_bytes : bytes.size = spec.nonceBytes

namespace NonceId

variable {spec : Spec}

def hash : NonceId spec → UInt64 := ByteArray.hash ∘ NonceId.bytes
instance : Hashable (NonceId spec) := ⟨hash⟩

/--
  Create a "unique" MVarId.

  Uniqueness is obviously not guaranteed in a purist sense, but can still be useful for
  creating synthetic goals.
-/
def toMVarId! (nonce : NonceId spec) := MVarId.mk (.num spec.name nonce.hash.toNat)

/--
  Create a "unique" FVarId.

  Uniqueness is obviously not guaranteed in a purist sense, but can still be useful for
  creating synthetic free variables.
-/
def toFVarId! (nonce : NonceId spec) := FVarId.mk (.num spec.name nonce.hash.toNat)

end NonceId

variable {σ : Type}

structure CryptoState (τ : Sodium σ) where
  private entropy : EntropyArray τ
  private nonces : NameMap ByteArray := ∅

inductive CryptoMessage
  | outOfFuel
  deriving BEq, Hashable, Inhabited

@[coe] def CryptoMessage.toMessageData : CryptoMessage → MessageData
  | .outOfFuel => m!"ran out of fuel"

instance : ToMessageData CryptoMessage := ⟨CryptoMessage.toMessageData⟩

@[coe] def CryptoMessage.toException (e : CryptoMessage) : Exception :=
  .error .missing (e.toMessageData)

instance : Coe CryptoMessage Exception := ⟨CryptoMessage.toException⟩

abbrev CryptoM (τ : Sodium σ) := StateRefT (Mutex (CryptoState τ)) CoreM

def throwOutOfFuel {α : Type} {τ : Sodium σ}: CryptoM τ α :=
  throw CryptoMessage.outOfFuel.toException

private instance {τ : Sodium σ} : MonadStateOf (CryptoState τ) (CryptoM τ) where
  get := do (← get).atomically get
  set st := do (← get).atomically (set st)
  modifyGet f := do (← get).atomically (modifyGet f)

namespace CryptoM

register_option crypto.defaultFuelSize : Nat := {
  defValue := 24 * 4096
  descr := "The number of random bytes to allocate for entropy."
}

def toCoreM {α : Type} (x : {σ : Type} → (τ : Sodium σ) → CryptoM τ α) (fuel? : Option Nat := none) : CoreM α := do
  let fuel := fuel?.getD <| crypto.defaultFuelSize.get (← getOptions)
  let τ ← init Unit
  let entropy ← EntropyArray.new τ fuel
  StateRefT'.run' (x τ) (← Mutex.new {entropy})

def toIO {α : Type} (ctx : Elab.ContextInfo)
    (x : {σ : Type} → (τ : Sodium σ) → CryptoM τ α) (fuel? : Option Nat := none) : IO α := do
  ctx.runCoreM <| toCoreM x fuel?

variable {τ : Sodium σ}

def getStatus : CryptoM τ (Nat × Nat) := do
  let st ← get
  return (st.entropy.off.toNat, st.entropy.size - st.entropy.off |>.toNat)

def getFuel : CryptoM τ Nat :=
  getStatus >>= pure ∘ Prod.snd

def reset : CryptoM τ Unit :=
  modify ({· with nonces := ∅})

def refuel : CryptoM τ Unit := do
  let mtx ← getThe (Mutex (CryptoState τ))
  mtx.atomically fun ref => do
    let st ← ref.get
    let entropy ← st.entropy.refresh
    ref.set {st with entropy}

def realloc (fuel : USize) : CryptoM τ Unit := do
  let mtx ← getThe (Mutex (CryptoState τ))
  mtx.atomically fun ref => do
    let entropy ← EntropyArray.new τ fuel
    ref.set {entropy}

def mkFreshNonceId (spec : Spec := NameGeneratorSpec) : CryptoM τ (NonceId spec) := do
  if h : spec.nonceBytes = 0 then
    return ⟨.empty, by simp [ByteArray.empty, ByteArray.size, ByteArray.emptyWithCapacity, h]⟩
  let mtx ← getThe (Mutex (CryptoState τ))
  let nonce? ← mtx.atomically fun ref => do
    let st ← ref.get
    match st.nonces.find? spec.name with
    | some stale =>
      let nonce := stale.succ
      if h : !nonce.isZero ∧ nonce.size = spec.nonceBytes then
        let nonces := st.nonces.insert spec.name nonce
        ref.set {st with nonces}
        return some ⟨nonce, h.2⟩
      else
        let (nonce?, st) ← next st
        ref.set st
        return nonce?
    | _ =>
      let (nonce?, st) ← next st
      ref.set st
      return nonce?
  match nonce? with
  | some nonce => return nonce
  | _ => throwOutOfFuel
where
  next (st : CryptoState τ) : BaseIO (Option (NonceId spec) × CryptoState τ) := do
    let {nonces, entropy} := st
    let (buf, entropy) ← entropy.extract τ spec.nonceBytes
    if h : buf.size = spec.nonceBytes then
      let nonces := nonces.insert spec.name buf
      return (some ⟨buf, h⟩, {st with nonces, entropy})
    else
      return (none, st)

def extractEntropy (size : USize) : CryptoM τ ByteArray := do
  let mtx ← getThe (Mutex (CryptoState τ))
  mtx.atomically fun ref => do
    let st ← ref.get
    let (buf, entropy) ← st.entropy.extract τ size
    ref.set {st with entropy}
    return buf

instance {τ : Sodium σ} : MonadNameGenerator (CryptoM τ) where
  getNGen := do
    let nonce ← mkFreshNonceId
    return {namePrefix := NameGeneratorSpec.name, idx := nonce.hash.toNat}
  setNGen _ :=
    return () -- not allowed, so we ignore.

end CryptoM

export CryptoM (mkFreshNonceId getFuel refuel reset realloc extractEntropy)

end Sodium.Crypto
