import Sodium.Data.Encodable.WType
import Sodium.Crypto.Spec

universe u

open Lean

namespace Sodium.Crypto

variable {σ : Type u}

inductive DecryptError
  | refused
  | invalidEncoding (data : ByteArray)
  | invalidString (utf8 : String)
  | invalidJson (json : Json)
  deriving TypeName, Hashable, Inhabited

inductive Decrypt (α : Type)
  | refused
  | mangled (data : ByteArray)
  | unknown (string : String)
  | almost (json : Json)
  | accepted (a : α)

namespace Decrypt

variable {α : Type}

@[coe] def toExcept : Decrypt α → Except DecryptError α
| .refused => .error .refused
| .mangled data => .error (.invalidEncoding data)
| .unknown string => .error (.invalidString string)
| .almost json => .error (.invalidJson json)
| .accepted a => .ok a

@[coe] def ofExcept : Except DecryptError α → Decrypt α
| .ok a => .accepted a
| .error .refused => .refused
| .error (.invalidEncoding data) => .mangled data
| .error (.invalidString string) => .unknown string
| .error (.invalidJson json) => .almost json

instance : Coe (Decrypt α) (Except DecryptError α) := ⟨toExcept⟩
instance : Coe (Except DecryptError α) (Decrypt α) := ⟨ofExcept⟩

def ofJson (α : Type) [Encodable α] (json : Json) : Decrypt α :=
  match decode? (α := α) json with
  | .some a => .accepted a
  | _ => .almost json

def ofString (α : Type) [Encodable α] (msg : String) : Decrypt α :=
  match Json.parse msg with
  | .ok json => ofJson α json
  | _ => .unknown msg

def ofByteArray (α : Type) [Encodable α] (data : ByteArray) : Decrypt α :=
  match String.fromUTF8? data with
  | .some msg => ofString α msg
  | _ => .mangled data

@[simp]
theorem toExcept_inj : ∀ r : Except DecryptError α, toExcept (ofExcept r) = r := by
  intro
  unfold toExcept ofExcept
  split <;> next _ _ h => split at h <;> simp_all

@[simp]
theorem ofExcept_inj : ∀ r : Decrypt α, ofExcept (toExcept r) = r := by
  intro
  unfold ofExcept toExcept
  split <;> next _ _ h => split at h <;> simp_all

@[simp]
theorem toExcept_ok_iff {a : α} : ∀ r : Decrypt α, toExcept r = .ok a ↔ r = .accepted a := by
  intro
  unfold toExcept
  constructor
  · intro a
    split at a <;> next _ _ => simp_all
  · intro a
    subst a
    simp_all only

def toOption : Decrypt α → Option α
| .accepted a => some a
| _ => none

@[simp]
theorem toOption_some_iff {a : α} : ∀ r : Decrypt α, toOption r = some a ↔ r = .accepted a := by
  intro
  unfold toOption
  constructor
  · intro a
    split at a <;> next _ _ => simp_all
  · intro a
    subst a
    simp_all only

end Decrypt

abbrev Nonce (spec : Spec) [spec.HasValidShape `nonce] :=
  ByteVector spec[`nonce]

structure NonceId (spec : Spec) where
  get : (h : spec.HasValidShape `nonce) → Nonce spec

abbrev Salt (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `salt] :=
  SecretVector τ <| USize.ofNatLT spec[`salt] (by simp [h.shape_is_valid])

abbrev SymmKey (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `symmkey] :=
  SecretVector τ <| USize.ofNatLT spec[`symmkey] (by simp [h.shape_is_valid])

abbrev SecretKey (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `secretkey] :=
  SecretVector τ <| USize.ofNatLT spec[`secretkey] (by simp [h.shape_is_valid])

abbrev PublicKey (spec : Spec) [spec.HasValidShape `publickey] :=
  ByteVector spec[`publickey]

structure PublicKeyId (spec : Spec) where
  get : (h : spec.HasValidShape `publickey) → PublicKey spec

structure KeyPair (τ : Sodium σ) (spec : Spec) [spec.HasValidShape `publickey] [spec.HasValidShape `secretkey] where
  pkey : PublicKey spec
  skey : SecretKey τ spec

structure Session (τ : Sodium σ) (spec : Spec) [spec.HasValidShape `symmkey] where
  rx : SymmKey τ spec
  tx : SymmKey τ spec

abbrev Hash (spec : Spec) [spec.HasValidShape `hash] :=
  ByteVector spec[`hash]

structure HashId (spec : Spec) where
  get : (h : spec.HasValidShape `hash) → Hash spec

abbrev Context (spec : Spec) [spec.HasValidShape `context] :=
  ByteVector spec[`context]

structure ContextId (spec : Spec) where
  get : (h : spec.HasValidShape `context) → Context spec

abbrev Header (spec : Spec) [spec.HasValidShape `header] :=
  ByteVector spec[`header]

structure HeaderId (spec : Spec) where
  get : (h : spec.HasValidShape `header) → Header spec

abbrev Signature (spec : Spec) [spec.HasValidShape `signature] :=
  ByteVector spec[`signature]

structure SignatureId (spec : Spec) where
  get : (h : spec.HasValidShape `signature) → Signature spec

structure SignedJson (spec : Spec) [spec.HasValidShape `signature] [spec.HasValidShape `publickey] where
  json : Json
  sig : Signature spec
  pkey : PublicKey spec
  deriving ToJson, FromJson

structure SignedJsonId (spec : Spec) where
  get : (h_sig : spec.HasValidShape `signature) → (h_key : spec.HasValidShape `publickey) → SignedJson spec

namespace SignedJson

variable {spec : Spec} [spec.HasValidShape `signature] [spec.HasValidShape `publickey]

instance : Encodable (SignedJson spec) :=
  have : Encodable.Equiv (SignedJson spec) (Json × Signature spec × PublicKey spec) := {
    push := fun ⟨json, sig, pkey⟩ => ⟨json, sig, pkey⟩
    pull := fun ⟨json, sig, pkey⟩ => ⟨json, sig, pkey⟩
  }
  Encodable.ofEquiv _ this

end SignedJson

structure CipherText (spec : Spec) [spec.HasValidShape `nonce] [spec.HasValidShape `mac] where
  size : Nat
  data : ByteVector size
  nonce : Nonce spec
  mac_le_size : spec[`mac] ≤ size

namespace CipherText

variable {spec : Spec} [spec.HasValidShape `nonce] [spec.HasValidShape `mac]

instance : ToJson (CipherText spec) where
  toJson cipher := json% {
    data : $cipher.data,
    nonce : $cipher.nonce
  }

instance : FromJson (CipherText spec) where
  fromJson? json := do
    let nonce ← json.getObjValAs? (Nonce spec) "nonce"
    let data ← json.getObjValAs? ByteArray "data"
    if h : spec[`mac] ≤ data.size then return ⟨data.size, data.toVector, nonce, h⟩
    throw "expected data to contain embedded mac"

instance : Encodable (CipherText spec) :=
  Encodable.ofLeftInj (α := Σ n, Nonce spec × ByteVector n)
    (fun ⟨size, data, nonce, _⟩ => ⟨size, ⟨nonce, data⟩⟩)
    (fun ⟨size, ⟨nonce, data⟩⟩ => if h : spec[`mac] ≤ size then some ⟨size, data, nonce, h⟩ else none)
    fun x => by
      simp only [getElem, Option.dite_none_right_eq_some, exists_prop, and_true]
      exact x.mac_le_size

end CipherText

structure SealedCipherText (spec : Spec) [spec.HasValidShape `publickey] [spec.HasValidShape `mac] where
  size : Nat
  data : ByteVector size
  seal_le_size : spec[`publickey] + spec[`mac] ≤ size

namespace SealedCipherText

variable {spec : Spec} [spec.HasValidShape `publickey] [spec.HasValidShape `mac]

instance : ToJson (SealedCipherText spec) where
  toJson cipher := json% {
    data : $cipher.data
  }

instance : FromJson (SealedCipherText spec) where
  fromJson? json := do
    let data ← json.getObjValAs? ByteArray "data"
    if h : spec[`publickey] + spec[`mac] ≤ data.size then return ⟨data.size, data.toVector, h⟩
    throw "expected data to contain embedded seal"

instance : Encodable (SealedCipherText spec) :=
  Encodable.ofLeftInj (α := Σ n, ByteVector n)
    (fun ⟨size, data, _⟩ => ⟨size, data⟩)
    (fun ⟨size, data⟩ => if h : spec[`publickey] + spec[`mac] ≤ size then some ⟨size, data, h⟩ else none)
    fun x => by
      simp only [getElem, Option.dite_none_right_eq_some, exists_prop, and_true]
      exact x.seal_le_size

end SealedCipherText

structure CipherChunk (spec : Spec) [spec.HasValidShape `mac] where
  size : Nat
  data : ByteVector size
  mac_le_size : spec[`mac] ≤ size

namespace CipherChunk

variable {spec : Spec} [spec.HasValidShape `mac]

instance : ToJson (CipherChunk spec) where
  toJson cipher := json% $cipher.data

instance : FromJson (CipherChunk spec) where
  fromJson? json := do
    let data ← fromJson? (α := ByteArray) json
    if h : spec[`mac] ≤ data.size then return ⟨data.size, data.toVector, h⟩
    throw "expected data to contain embedded mac"

instance : Encodable (CipherChunk spec) :=
  Encodable.ofLeftInj (α := ByteArray)
    (fun ⟨_, data, _⟩ => data.toArray)
    (fun data => if h : spec[`mac] ≤ data.toVector.size then some ⟨data.size, data.toVector, h⟩ else none)
    fun x => by
      obtain ⟨size, data, h⟩ := x
      simp only [getElem, ByteVector.toArray_inj, ByteArray.toVector_size, ByteVector.size_toArray,
        Option.dite_none_right_eq_some, Option.some.injEq]
      constructor
      . simp only [mk.injEq, ByteVector.size_toArray, true_and]
        exact ByteVector.instHEqCast _
      . exact h

end CipherChunk

end Sodium.Crypto
