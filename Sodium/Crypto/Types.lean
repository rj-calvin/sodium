import Sodium.Crypto.Spec

open Lean

namespace Sodium.Crypto

variable {σ : Type}

inductive DecryptError
  | refused
  | invalidEncoding (data : ByteArray)
  | invalidString (utf8 : String)
  | invalidJson (json : Json) (expected : String)
  deriving TypeName, Hashable, Inhabited

inductive DecryptResult (α : Type) [FromJson α]
  | refused
  | mangled (data : ByteArray)
  | unknown (string : String)
  | almost (json : Json) (expected : String)
  | accepted (a : α)

namespace DecryptResult

variable {α : Type} [FromJson α]

@[coe] def toExcept : DecryptResult α → Except DecryptError α
| .refused => .error .refused
| .mangled data => .error (.invalidEncoding data)
| .unknown string => .error (.invalidString string)
| .almost json expected => .error (.invalidJson json expected)
| .accepted a => .ok a

@[coe] def ofExcept : Except DecryptError α → DecryptResult α
| .ok a => .accepted a
| .error .refused => .refused
| .error (.invalidEncoding data) => .mangled data
| .error (.invalidString string) => .unknown string
| .error (.invalidJson json expected) => .almost json expected

instance : Coe (DecryptResult α) (Except DecryptError α) := ⟨toExcept⟩
instance : Coe (Except DecryptError α) (DecryptResult α) := ⟨ofExcept⟩

@[simp]
theorem toExcept_inj : ∀ r : Except DecryptError α, toExcept (ofExcept r) = r := by
  intro
  unfold toExcept ofExcept
  aesop

@[simp]
theorem ofExcept_inj : ∀ r : DecryptResult α, ofExcept (toExcept r) = r := by
  intro
  unfold ofExcept toExcept
  aesop

@[simp]
theorem toExcept_ok_iff {a : α} : ∀ r : DecryptResult α, toExcept r = .ok a ↔ r = .accepted a := by
  intro
  unfold toExcept
  aesop

def toOption : DecryptResult α → Option α
| .accepted a => some a
| _ => none

@[simp]
theorem toOption_some_iff {a : α} : ∀ r : DecryptResult α, toOption r = some a ↔ r = .accepted a := by
  intro
  unfold toOption
  aesop

end DecryptResult

structure Nonce (spec : Spec) [spec.HasValidShape `nonce] where
  data : ByteVector spec[`nonce]
  deriving BEq, ToJson, FromJson

structure Seed (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `seed] where
  data : SecureVector τ <| USize.ofNatLT spec[`seed] (by simp [h.shape_is_valid])
  deriving BEq

structure SymmKey (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `symmkey] where
  data : SecureVector τ <| USize.ofNatLT spec[`symmkey] (by simp [h.shape_is_valid])
  deriving BEq

structure SecretKey (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `secretkey] where
  data : SecureVector τ <| USize.ofNatLT spec[`secretkey] (by simp [h.shape_is_valid])
  deriving BEq

structure PublicKey (spec : Spec) [spec.HasValidShape `publickey] where
  data : ByteVector spec[`publickey]
  deriving BEq, ToJson, FromJson

structure SharedKey (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `sharedkey] where
  data : SecureVector τ <| USize.ofNatLT spec[`sharedkey] (by simp [h.shape_is_valid])
  deriving BEq

structure KeyPair (τ : Sodium σ) (spec : Spec) [spec.HasValidShape `publickey] [spec.HasValidShape `secretkey] where
  pkey : PublicKey spec
  skey : SecretKey τ spec

structure Session (τ : Sodium σ) (spec : Spec) [spec.HasValidShape `symmkey] where
  rx : SymmKey τ spec
  tx : SymmKey τ spec

structure Mac (spec : Spec) [spec.HasValidShape `mac] where
  data : ByteVector spec[`mac]
  deriving BEq, ToJson, FromJson

structure Hash (spec : Spec) [spec.HasValidShape `minhash] [spec.HasValidShape `maxhash] where
  size : Nat
  data : ByteVector size
  shapeOf_minhash_le_size : spec[`minhash] ≤ size
  shapeOf_maxhash_ge_size : spec[`maxhash] ≥ size
  deriving BEq

namespace Hash

variable {spec : Spec} [spec.HasValidShape `minhash] [spec.HasValidShape `maxhash]

instance : ToJson (Hash spec) where
  toJson hash := json% {
    size : $hash.size,
    data : $hash.data
  }

instance : FromJson (Hash spec) where
  fromJson? json := do
    let size ← json.getObjValAs? Nat "size"
    let data ← json.getObjValAs? (ByteVector size) "data"
    if h1 : spec[`minhash] ≤ size then
      if h2 : spec[`maxhash] ≥ size then
        return ⟨size, data, h1, h2⟩
      else
        throw "expected data size to be at most maxhash"
    else
      throw "expected data size to be at least minhash"

end Hash

structure Salt (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `salt] where
  data : SecureVector τ <| USize.ofNatLT spec[`salt] (by simp [h.shape_is_valid])
  deriving BEq

structure Context (spec : Spec) [spec.HasValidShape `context] where
  data : ByteVector spec[`context]
  deriving BEq, ToJson, FromJson

structure Header (spec : Spec) [spec.HasValidShape `header] where
  data : ByteVector spec[`header]
  deriving BEq, ToJson, FromJson

structure CipherText (spec : Spec) [spec.HasValidShape `nonce] [spec.HasValidShape `mac] where
  size : Nat
  data : ByteVector size
  nonce : Nonce spec
  shapeOf_mac_le_size : spec[`mac] ≤ size

namespace CipherText

variable {spec : Spec} [spec.HasValidShape `nonce] [spec.HasValidShape `mac]

instance : ToJson (CipherText spec) where
  toJson cipher := json% {
    size : $cipher.size,
    data : $cipher.data,
    nonce : $cipher.nonce
  }

instance : FromJson (CipherText spec) where
  fromJson? json := do
    let size ← json.getObjValAs? Nat "size"
    let data ← json.getObjValAs? (ByteVector size) "data"
    let nonce ← json.getObjValAs? (Nonce spec) "nonce"
    if h : spec.shapeOf `mac ≤ size then
      return ⟨size, data, nonce, h⟩
    else
      throw "expected data to contain embedded mac"

end CipherText

structure SealedCipherText (spec : Spec) [spec.HasValidShape `seal] where
  size : Nat
  data : ByteVector size
  shapeOf_seal_le_size : spec[`seal] ≤ size

namespace SealedCipherText

variable {spec : Spec} [spec.HasValidShape `seal]

instance : ToJson (SealedCipherText spec) where
  toJson cipher := json% {
    size : $cipher.size,
    data : $cipher.data
  }

instance : FromJson (SealedCipherText spec) where
  fromJson? json := do
    let size ← json.getObjValAs? Nat "size"
    let data ← json.getObjValAs? (ByteVector size) "data"
    if h : spec.shapeOf `seal ≤ size then
      return ⟨size, data, h⟩
    else
      throw "expected data to contain embedded seal"

end SealedCipherText

structure CipherChunk (spec : Spec) [spec.HasValidShape `mac] where
  size : Nat
  data : ByteVector size
  shapeOf_mac_le_size : spec[`mac] ≤ size

namespace CipherChunk

variable {spec : Spec} [spec.HasValidShape `mac]

instance : ToJson (CipherChunk spec) where
  toJson cipher := json% {
    size : $cipher.size,
    data : $cipher.data
  }

instance : FromJson (CipherChunk spec) where
  fromJson? json := do
    let size ← json.getObjValAs? Nat "size"
    let data ← json.getObjValAs? (ByteVector size) "data"
    if h : spec.shapeOf `mac ≤ size then
      return ⟨size, data, h⟩
    else
      throw "expected data to contain embedded mac"

end CipherChunk

end Sodium.Crypto
