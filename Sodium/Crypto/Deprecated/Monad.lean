/-
The CryptoM monad using StateRefT for safe cryptographic operations.

This module provides a stateful monad that:
- Ensures sodium initialization before any crypto operations
- Tracks nonce generation to prevent reuse
- Manages cryptographic resource lifecycle
- Provides compile-time and runtime safety guarantees
-/
import Init.Meta
import Init.Control.StateRef
import Std.Data.HashMap
import Sodium.Data.ByteArray
import Sodium.FFI.Basic
import Sodium.Crypto.Types

open Lean Std Sodium

namespace Sodium.Crypto

variable {spec : AlgorithmSpec}

namespace NonceId

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

structure CryptoState where
  private entropyOff : Nat := 0
  private entropy : ByteArray
  private nonces : NameMap ByteArray := ∅

structure CryptoContext where
  startingFuel : USize

inductive CryptoMessage
  | outOfFuel
  | ioError (e : IO.Error)
  | ofData (e : MessageData)
  | ofLazy (f : Option PPContext → BaseIO Dynamic) (hasSyntheticSorry : MetavarContext → Bool)
  deriving Inhabited

@[coe] def CryptoMessage.toMessageData : CryptoMessage → MessageData
  | .outOfFuel => m!"ran out of fuel"
  | .ofData e => e
  | .ioError e => instToMessageDataOfToFormat.toMessageData e
  | .ofLazy f s => .ofLazy f s

instance : ToMessageData CryptoMessage := ⟨CryptoMessage.toMessageData⟩

@[coe] def CryptoMessage.toException (e : CryptoMessage) : Exception :=
  .error .missing (e.toMessageData)

instance : Coe CryptoMessage Exception := ⟨CryptoMessage.toException⟩

abbrev CryptoM := ReaderT CryptoContext <| StateRefT (Mutex CryptoState) CoreM

variable {α : Type}

def throwOutOfFuel : CryptoM α :=
  throw CryptoMessage.outOfFuel.toException

def throwMessage {ε : Type} [ToMessageData ε] (msg : ε) : CryptoM α :=
  throw (CryptoMessage.ofData <| toMessageData msg).toException

def throwLazy (f : Option PPContext → BaseIO Dynamic) (hasSyntheticSorry : MetavarContext → Bool) : CryptoM α :=
  throw (CryptoMessage.ofLazy f hasSyntheticSorry).toException

private instance : MonadStateOf CryptoState CryptoM where
  get := do (← get).atomically get
  set st := do (← get).atomically (set st)
  modifyGet f := do (← get).atomically (modifyGet f)

namespace CryptoM

register_option crypto.defaultFuelSize : Nat := {
  defValue := 24 * 4096
  descr := "The number of random bytes to allocate for entropy."
}

/--
  Initialize the crypto monad, ensuring sodium is initialized before computation begins.
  Uses `crypto.defaultFuelSize if fuel is not provided.
-/
def run {α : Type} (action : CryptoM α) (fuel? : Option USize := none) : CoreM α := do
  let fuel := fuel?.getD <| crypto.defaultFuelSize.get (← getOptions) |> Nat.toUSize
  discard FFI.sodiumInit
  let entropy ← FFI.randomBytes fuel
  StateRefT'.run' (action {startingFuel := fuel}) (← Mutex.new {entropy})

/--
  Get the remaining fuel of the environment - i.e. the remaining bytes of entropy that can be
  used to securely generate nonces.
-/
def getFuel : CryptoM Nat := do
  let st ← get
  return st.entropy.size - st.entropyOff

/--
  Get the number of bytes used and the number of bytes remaining.
-/
def getEntropyStatus : CryptoM (Nat × Nat) := do
  let st ← get
  return (st.entropyOff, st.entropy.size - st.entropyOff)

/--
  Reinitialize the entropy of the current cryptographic environment. Uses the starting fuel if not provided.

  Note: refueling will not reset active nonces. Use `reset` for this purpose.
-/
def refuel (fuel? : Option USize := none) : CryptoM Unit := do
  let fuel := fuel?.getD (← read).startingFuel
  let entropy ← FFI.randomBytes fuel
  modify ({· with entropyOff := 0, entropy})

/--
  Reset the nonces of the current cryptographic environment.

  Note: resetting does not allocate new entropy. Use `refuel` for this purpose.
-/
def reset : CryptoM Unit :=
  modify ({· with nonces := ∅})

/-- Get or initialize nonce counter for an algorithm. -/
def mkFreshNonceId (spec : AlgorithmSpec := NameGeneratorSpec) : CryptoM (NonceId spec) := do
  if h : spec.nonceBytes = 0 then
    return ⟨.empty, by simp [ByteArray.empty, ByteArray.size, ByteArray.emptyWithCapacity, h]⟩
  let nonce? ← modifyGet fun st@{nonces, ..} =>
    match nonces.find? spec.name with
    | some n =>
      let n := n.succ!
      if h : n.size = spec.nonceBytes then
        let nonces := nonces.insert spec.name n
        (some ⟨n, h⟩, {st with nonces})
      else
        nextNonce st
    | none => nextNonce st
  match nonce? with
  | some n => return n
  | _ => throwOutOfFuel
where
  nextNonce (st : CryptoState) : Option (NonceId spec) × CryptoState :=
    let {nonces, entropy, entropyOff} := st

    let front := entropy.copySlice
      (srcOff := entropyOff)
      (dest := ⟨.emptyWithCapacity spec.nonceBytes⟩)
      (destOff := 0)
      (len := spec.nonceBytes)
      (exact := true)

    if h : front.size = spec.nonceBytes then
      let nonce := ⟨front, h⟩
      let nonces := nonces.insert spec.name nonce.bytes
      (some nonce, {st with entropyOff := entropyOff + spec.nonceBytes, nonces})
    else
      (none, st)

/--
  Extract entropy of at most `size` number of bytes, draining fuel in the process.
-/
def drainEntropy (size : Nat) : CryptoM ByteArray := do
  if size == 0 then return .empty else
  modifyGet fun st@{entropyOff, entropy, ..} =>
    let data := entropy.copySlice
      (srcOff := entropyOff)
      (dest := ⟨.emptyWithCapacity size⟩)
      (destOff := 0)
      (len := size)
      (exact := true)
    (data, {st with entropyOff := entropyOff + size})

instance : MonadNameGenerator CryptoM where
  getNGen := do
    let nonce ← mkFreshNonceId
    return {namePrefix := NameGeneratorSpec.name, idx := nonce.hash.toNat}
  setNGen _ :=
    return () -- not allowed, so we ignore.

end CryptoM

export CryptoM (mkFreshNonceId getFuel refuel reset drainEntropy)

instance : MonadLift CryptoM CoreM where
  monadLift := CryptoM.run

end Sodium.Crypto
