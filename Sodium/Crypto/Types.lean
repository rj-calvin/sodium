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

structure Nonce (spec : Spec) [h : spec.HasValidShape `nonce] where
  data : ByteVector (spec.shapeOf `nonce)

structure SymmKey (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `symmkey] where
  data : SecureVector τ <| USize.ofNatLT (spec.shapeOf `symmkey) (by simp [h.shape_is_valid])

structure SecretKey (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `secretkey] where
  data : SecureVector τ <| USize.ofNatLT (spec.shapeOf `secretkey) (by simp [h.shape_is_valid])

structure PublicKey (spec : Spec) [h : spec.HasValidShape `publickey] where
  data : ByteVector (spec.shapeOf `publickey)

structure SharedKey (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `sharedkey] where
  data : SecureVector τ <| USize.ofNatLT (spec.shapeOf `sharedkey) (by simp [h.shape_is_valid])

structure SessionKey (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `sessionkey] where
  data : SecureVector τ <| USize.ofNatLT (spec.shapeOf `sessionkey) (by simp [h.shape_is_valid])

structure KeyPair (τ : Sodium σ) (spec : Spec) [spec.HasValidShape `publickey] [spec.HasValidShape `secretkey] where
  pkey : PublicKey spec
  skey : SecretKey τ spec

structure Session (τ : Sodium σ) (spec : Spec) [spec.HasValidShape `sessionkey] where
  rx : SessionKey τ spec
  tx : SessionKey τ spec

structure MetaKey (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `metakey] where
  data : SecureVector τ <| USize.ofNatLT (spec.shapeOf `metakey) (by simp [h.shape_is_valid])

structure Seed (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `seed] where
  data : SecureVector τ <| USize.ofNatLT (spec.shapeOf `seed) (by simp [h.shape_is_valid])

structure Mac (spec : Spec) [h : spec.HasValidShape `mac] where
  data : ByteVector (spec.shapeOf `mac)

structure AuthTag (spec : Spec) where
  data : ByteVector (spec.shapeOf `tag)

structure HashOutput (spec : Spec) where
  data : ByteVector (spec.shapeOf `hash)

structure Salt (τ : Sodium σ) (spec : Spec) [h : spec.HasValidShape `salt] where
  data : SecureVector τ <| USize.ofNatLT (spec.shapeOf `salt) (by simp [h.shape_is_valid])

structure Context (spec : Spec) [h : spec.HasValidShape `context] where
  data : ByteVector (spec.shapeOf `context)

structure StreamHeader (spec : Spec) where
  data : ByteVector (spec.shapeOf `header)

structure Signature (spec : Spec) where
  data : ByteVector (spec.shapeOf `signature)

structure CipherText (spec : Spec) [spec.HasValidShape `nonce] where
  size : Nat
  data : ByteVector size
  nonce : Nonce spec
  shapeOf_mac_le_size : spec.shapeOf `mac ≤ size

structure DetachedCipherText (spec : Spec) [spec.HasValidShape `mac] [spec.HasValidShape `nonce] where
  data : ByteArray
  mac : Mac spec
  nonce : Nonce spec

structure TaggedCipherText (spec : Spec) where
  data : ByteArray
  size_ge_shapeOf_tag : data.size ≥ spec.shapeOf `tag

structure SealedCipherText (spec : Spec) where
  size : Nat
  data : ByteVector size
  shapeOf_seal_le_size : spec.shapeOf `seal ≤ size

structure Message (α : Type) [ToJson α] where
  val : α
  json_shape_is_valid : Spec.IsValidShape (toJson val).compress.toUTF8.size

instance {α : Type} [ToJson α] : ToJson (Message α) where
  toJson x := toJson x.val

end Sodium.Crypto
