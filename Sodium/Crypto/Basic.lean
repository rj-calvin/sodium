import Lean.Meta
import Std.Sync.Mutex
import Sodium.Data.SecretVector
import Sodium.Data.Digest
import Sodium.Data.Decrypt

open Lean

namespace Sodium

def SpecName := Name

instance : Inhabited SpecName := ⟨@default Name _⟩

def ContextName := ByteVector 8

def ContextName.ofString (s : String) (h : s.utf8ByteSize = 8 := by rfl) : ContextName :=
  ⟨s.toUTF8, h⟩

instance : Inhabited ContextName := ⟨.ofString "standard"⟩

def Nonce := ByteVector 24
def Seed := ByteVector 32
def Hash := ByteVector 64

structure Auth (_ : SpecName) where
  raw : ByteVector 16

structure Element (_ : SpecName) where
  raw : ByteVector 32

structure Scalar (τ : Sodium σ) (_ : SpecName) where
  raw : τ.SecretVector 32

structure KeyPair (τ : Sodium σ) (nm : SpecName) where
  skey : τ.Scalar nm
  pkey : Element nm

structure Session (τ : Sodium σ) (nm : SpecName) where
  rx : τ.Scalar nm
  tx : τ.Scalar nm

structure State (τ : Sodium σ) where
  entropy : τ.Entropy
  nonces : NameMap Nonce := ∅

structure Context (τ : Sodium σ) where
  private mk ::
  private mtx : Std.Mutex τ.State
  ctx : ContextName
  mkey : τ.Scalar `blake2b

abbrev CryptoM (τ : Sodium σ) := ReaderT τ.Context MetaM

register_option crypto.entropyBytes : Nat := {
  defValue := 24 * 256
  descr := "The number of random bytes to allocate for entropy."
}

def CryptoM.run (x : (τ : Sodium σ) → τ.CryptoM α) (ctx : ContextName := default) (seed : Option Seed := none) : MetaM α := do
  let τ ← sodium σ
  let entropy ← Entropy.randomBytes (τ := τ) (crypto.entropyBytes.get (← getOptions)).toUSize
  let mkey ←
    if h : seed.isSome then SecretVector.seededBytes (τ := τ) 32 (seed.get h)
    else SecretVector.randomBytes (τ := τ) 32
  let mtx ← Std.Mutex.new {entropy}
  x τ {mtx, ctx, mkey := ⟨mkey⟩}

variable {τ : Sodium σ}

def withMetaKey (mkey : τ.Scalar `blake2b) (x : τ.CryptoM α) : τ.CryptoM α := do
  Meta.withNewMCtxDepth <| x {← read with mkey}

def mkFreshNonce (spec : SpecName := default) : τ.CryptoM Nonce := do
  let mtx := (← read).mtx
  mtx.atomically fun ref => do
    let st ← ref.get
    match st.nonces.get? spec with
    | some stale =>
      let nonce ← stale.succ
      let nonces := st.nonces.insert spec nonce
      ref.modifyGet fun st => (nonce, {st with nonces})
    | none =>
      let (nonce, entropy) ← do
        if st.entropy.usize - st.entropy.uoff < 24 then
          discard st.entropy.refresh
        st.entropy.extractSlice 24
      if h : nonce.size = 24 then
        let nonces := st.nonces.insert spec ⟨nonce, h⟩
        ref.modifyGet fun st => (⟨nonce, h⟩, {st with nonces, entropy})
      else throwError "insufficient entropy for allocating nonce"

def mkFreshSecret : τ.CryptoM (τ.Scalar `blake2b) := return ⟨← SecretVector.randomBytes 32⟩

@[extern "lean_sodium_kdf_derive_from_key"]
private opaque mkStaleSecret.impl (idx : UInt64) (ctx : @& ContextName) (key : @& τ.Scalar `blake2b) : IO (τ.SecretVector 32)

def mkStaleSecret : τ.CryptoM (τ.Scalar `blake2b) := do
  let {mkey, ctx, ..} ← read
  let mctx ← getMCtx
  return ⟨← mkStaleSecret.impl mctx.depth.toUInt64 ctx mkey⟩

@[extern "lean_sodium_ristretto255_scalar_random"]
private opaque mkFreshScalar.impl : IO (τ.SecretVector 32)

def mkFreshScalar : τ.CryptoM (τ.Scalar `ristretto255) := return ⟨← mkFreshScalar.impl⟩

@[extern "lean_sodium_ristretto255_scalar_reduce"]
private opaque mkStaleScalar.impl (hash : @& Hash) : IO (τ.SecretVector 32)

def mkStaleScalar (x : α) (seed : Option Seed := none) [Encodable α] : τ.CryptoM (τ.Scalar `ristretto255) :=
  return ⟨← mkStaleScalar.impl <| digest x seed⟩

end Sodium
