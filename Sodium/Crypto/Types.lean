import Sodium.Data.Encodable.Basic
import Sodium.Crypto.Spec

open Lean

namespace Sodium.Crypto

variable {σ : Type}

inductive DecryptError
  | refused
  | invalidEncoding (data : ByteArray)
  | invalidString (utf8 : String)
  | invalidJson (json : Json)
  deriving TypeName, Hashable, Inhabited

inductive DecryptResult (α : Type)
  | refused
  | mangled (data : ByteArray)
  | unknown (string : String)
  | almost (json : Json)
  | accepted (a : α)

namespace DecryptResult

variable {α : Type}

@[coe] def toExcept : DecryptResult α → Except DecryptError α
| .refused => .error .refused
| .mangled data => .error (.invalidEncoding data)
| .unknown string => .error (.invalidString string)
| .almost json => .error (.invalidJson json)
| .accepted a => .ok a

@[coe] def ofExcept : Except DecryptError α → DecryptResult α
| .ok a => .accepted a
| .error .refused => .refused
| .error (.invalidEncoding data) => .mangled data
| .error (.invalidString string) => .unknown string
| .error (.invalidJson json) => .almost json

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

abbrev Nonce (spec : Spec) [spec.HasValidShape `nonce] :=
  ByteVector spec[`nonce]

abbrev Salt (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `salt] :=
  SecureVector τ <| USize.ofNatLT spec[`salt] (by simp [h.shape_is_valid])

abbrev SymmKey (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `symmkey] :=
  SecureVector τ <| USize.ofNatLT spec[`symmkey] (by simp [h.shape_is_valid])

abbrev SecretKey (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `secretkey] :=
  SecureVector τ <| USize.ofNatLT spec[`secretkey] (by simp [h.shape_is_valid])

abbrev PublicKey (spec : Spec) [spec.HasValidShape `publickey] :=
  ByteVector spec[`publickey]

abbrev SharedKey (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `sharedkey] :=
  SecureVector τ <| USize.ofNatLT spec[`sharedkey] (by simp [h.shape_is_valid])

structure KeyPair (τ : Sodium σ) (spec : Spec) [spec.HasValidShape `publickey] [spec.HasValidShape `secretkey] where
  pkey : PublicKey spec
  skey : SecretKey τ spec

structure Session (τ : Sodium σ) (spec : Spec) [spec.HasValidShape `symmkey] where
  rx : SymmKey τ spec
  tx : SymmKey τ spec

abbrev Hash (spec : Spec) [spec.HasValidShape `hash] :=
  ByteVector spec[`hash]

abbrev Context (spec : Spec) [spec.HasValidShape `context] :=
  ByteVector spec[`context]

abbrev Header (spec : Spec) [spec.HasValidShape `header] :=
  ByteVector spec[`header]

abbrev Signature (spec : Spec) [spec.HasValidShape `signature] :=
  ByteVector spec[`signature]

structure SignedJson (spec : Spec) [spec.HasValidShape `signature] [spec.HasValidShape `publickey] where
  protected toJson : Json
  sig : Signature spec
  pkey : PublicKey spec
  deriving ToJson, FromJson

namespace SignedJson

variable {spec : Spec} [spec.HasValidShape `signature] [spec.HasValidShape `publickey]

instance : Encodable (SignedJson spec) :=
  Encodable.ofEquiv (α := Json × Signature spec × PublicKey spec)
    (fun ⟨json, sig, pkey⟩ => ⟨json, sig, pkey⟩)
    (fun ⟨json, sig, pkey⟩ => ⟨json, sig, pkey⟩)
    (fun _ => rfl)

end SignedJson

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

instance : Encodable (CipherText spec) :=
  Encodable.ofLeftInj (α := Σ n, ByteVector n × Nonce spec)
    (fun ⟨size, data, nonce, _⟩ => ⟨size, ⟨data, nonce⟩⟩)
    (fun ⟨size, ⟨data, nonce⟩⟩ =>
      if h : spec[`mac] ≤ size then
        some ⟨size, data, nonce, h⟩
      else
        none)
    (fun x => by
      simp only [getElem, Option.dite_none_right_eq_some, exists_prop, and_true]
      exact x.shapeOf_mac_le_size)

end CipherText

structure SealedCipherText (spec : Spec) [spec.HasValidShape `publickey] [spec.HasValidShape `mac] where
  size : Nat
  data : ByteVector size
  shapeOf_seal_le_size : spec[`publickey] + spec[`mac] ≤ size

namespace SealedCipherText

variable {spec : Spec} [spec.HasValidShape `publickey] [spec.HasValidShape `mac]

instance : ToJson (SealedCipherText spec) where
  toJson cipher := json% {
    size : $cipher.size,
    data : $cipher.data
  }

instance : FromJson (SealedCipherText spec) where
  fromJson? json := do
    let size ← json.getObjValAs? Nat "size"
    let data ← json.getObjValAs? (ByteVector size) "data"
    if h : spec.shapeOf `publickey + spec.shapeOf `mac ≤ size then
      return ⟨size, data, h⟩
    else
      throw "expected data to contain embedded seal"

instance : Encodable (SealedCipherText spec) :=
  Encodable.ofLeftInj (α := Σ n, ByteVector n)
    (fun ⟨size, data, _⟩ => ⟨size, data⟩)
    (fun ⟨size, data⟩ =>
      if h : spec[`publickey] + spec[`mac] ≤ size then
        some ⟨size, data, h⟩
      else
        none)
    (fun x => by
      simp only [getElem, Option.dite_none_right_eq_some, exists_prop, and_true]
      exact x.shapeOf_seal_le_size)

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

instance : Encodable (CipherChunk spec) :=
  Encodable.ofLeftInj (α := Σ n, ByteVector n)
    (fun ⟨size, data, _⟩ => ⟨size, data⟩)
    (fun ⟨size, data⟩ =>
      if h : spec[`mac] ≤ size then
        some ⟨size, data, h⟩
      else
        none)
    (fun x => by
      simp only [getElem, Option.dite_none_right_eq_some, exists_prop, and_true]
      exact x.shapeOf_mac_le_size)

end CipherChunk

end Sodium.Crypto
