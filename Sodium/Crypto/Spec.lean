import Aesop
import Sodium.FFI

open Lean

namespace Sodium.Crypto

private instance : Ord Name := ⟨Name.quickCmp⟩

structure Spec where
  name : Name
  shapes : NameMap Nat := ∅
  deriving TypeName, Inhabited, ToJson, FromJson

namespace Spec

abbrev toJson (spec : Spec) : Json := instToJsonSpec.toJson spec
abbrev fromJson? (json : Json) : Except String Spec := instFromJsonSpec.fromJson? json

@[inline, always_inline]
def shapeOf (spec : Spec) (name : Name) : Nat := spec.shapes.findD name 0

instance : Membership Name Spec where
  mem spec name := spec.shapes.contains name

instance {spec : Spec} {name : Name} : Decidable (name ∈ spec) :=
  inferInstanceAs <| Decidable (spec.shapes.contains name)

def addShape (spec : Spec) (name : Name) (size : Nat) : Spec :=
  { spec with shapes := spec.shapes.insert name size }

def removeShape (spec : Spec) (name : Name) : Spec :=
  { spec with shapes := spec.shapes.erase name }

def merge (fn : Name → Nat → Nat → Nat) (inl : Spec) (inr : Spec) : Spec where
  name := inl.name ++ inr.name
  shapes := RBMap.mergeBy fn inl.shapes inr.shapes

instance : Append Spec where
  append inl inr := merge (fun _ n m => max n m) inl inr

def isEmpty (spec : Spec) : Bool := spec.shapes.isEmpty

def size (spec : Spec) : Nat := spec.shapes.size

def IsValidShape (size : Nat) : Prop := 0 < size ∧ size < USize.size

@[simp]
theorem valid_shape_lt_usizeSize : ∀ n, IsValidShape n → n < USize.size := by
  intros _ h
  obtain ⟨_, hsize⟩ := h
  exact hsize

@[simp]
theorem valid_shape_pos : ∀ n, IsValidShape n → 0 < n := by
  intros _ h
  obtain ⟨hpos, _⟩ := h
  exact hpos

@[simp]
theorem valid_shape_elim_usize : ∀ (n : Nat), (h : IsValidShape n) → n = USize.ofNatLT n (by simp [h]) := by
  intros n _
  exact (USize.ofNatLT_eq_ofNat n).symm

instance (size : Nat) : Decidable (IsValidShape size) := by exact instDecidableAnd
instance : DecidablePred IsValidShape := by infer_instance

class HasValidShape (spec : Spec) (name : Name) : Prop where
  shape_is_valid : IsValidShape (spec.shapeOf name)

@[simp]
theorem has_valid_shape_iff : ∀ (s : Spec) n, s.HasValidShape n ↔ IsValidShape (s.shapeOf n) := by
  intros s n
  constructor <;> intro h
  . exact h.shape_is_valid
  . exact ⟨h⟩

instance {spec : Spec} {name : Name} : Decidable (spec.HasValidShape name) := by
  simp only [has_valid_shape_iff]
  infer_instance

instance : GetElem? Spec Name Nat (fun s n => s.HasValidShape n) where
  getElem spec name _ := spec.shapeOf name
  getElem? spec name :=
    let shape := spec.shapeOf name
    if IsValidShape shape then some shape
    else none

attribute [simp, grind] GetElem.getElem
attribute [simp, grind] GetElem?.getElem!
attribute [simp, grind] GetElem?.getElem?

@[simp]
theorem getElem?_eq_some_iff : ∀ (s : Spec) n m, s[n]? = some m ↔ m = s.shapeOf n ∧ IsValidShape m := by
  intros s n m
  simp only [getElem?, Option.ite_none_right_eq_some, Option.some.injEq]
  constructor <;> intro ⟨ha, hb⟩
  . simp only [true_and, hb] at ha ⊢
    exact ha
  . simp only [ha, and_true] at hb ⊢
    exact hb

end Spec

open FFI KeyExch in
def UniqId : Spec where
  name := `_uniq
  shapes := RBMap.empty
    |>.insert `nonce 8
    |>.insert `seed SEEDBYTES

open FFI KeyExch in
def Curve25519 : Spec where
  name := `curve25519
  shapes := RBMap.empty
    |>.insert `publickey PUBLICKEYBYTES
    |>.insert `secretkey SECRETKEYBYTES

open FFI Sign in
def Ed25519 : Spec where
  name := `ed25519
  shapes := RBMap.empty
    |>.insert `publickey PUBLICKEYBYTES
    |>.insert `secretkey SECRETKEYBYTES
    |>.insert `signature BYTES

open FFI KeyDeriv in
def Blake2b : Spec where
  name := `blake2b
  shapes := RBMap.empty
    |>.insert `context CONTEXTBYTES
    |>.insert `symmkey KEYBYTES
    |>.insert `hash BYTES_DEFAULT

open FFI SecretBox in
def XSalsa20 : Spec where
  name := `xsalsa20
  shapes := RBMap.empty
    |>.insert `nonce NONCEBYTES
    |>.insert `symmkey KEYBYTES

open FFI Box in
def HSalsa20 : Spec where
  name := `hsalsa20
  shapes := RBMap.empty
    |>.insert `sharedkey SHAREDBYTES

open FFI Box in
def Poly1305 : Spec where
  name := `poly1305
  shapes := RBMap.empty
    |>.insert `mac MACBYTES

open FFI Aead in
def XChaCha20 : Spec where
  name := `xchacha20
  shapes := RBMap.empty
    |>.insert `symmkey KEYBYTES
    |>.insert `nonce NONCEBYTES
    |>.insert `header SecretStream.HEADERBYTES

abbrev XSalsa20Poly1305 := XSalsa20 ++ Poly1305
abbrev XChaCha20Poly1305 := XChaCha20 ++ Poly1305
abbrev Curve25519HSalsa20 := Curve25519 ++ HSalsa20
abbrev Curve25519XSalsa20Poly1305 := Curve25519 ++ XSalsa20Poly1305
abbrev Curve25519Blake2b := Curve25519 ++ Blake2b

@[simp] theorem uniqid_nonce_eq : UniqId.shapeOf `nonce = 8 := by native_decide
@[simp] theorem uniqid_nonce_valid : Spec.IsValidShape <| UniqId.shapeOf `nonce := by native_decide
@[simp] theorem uniqid_nonce_support : Spec.IsValidShape 8 := by
  rw [← uniqid_nonce_eq]
  exact uniqid_nonce_valid

@[simp] theorem uniqid_seed_eq : UniqId.shapeOf `seed = FFI.KeyExch.SEEDBYTES := by native_decide
@[simp] theorem uniqid_seed_valid : Spec.IsValidShape <| UniqId.shapeOf `seed := by native_decide
@[simp] theorem uniqid_seed_support : Spec.IsValidShape FFI.KeyExch.SEEDBYTES := by
  rw [← uniqid_seed_eq]
  exact uniqid_seed_valid

instance : UniqId.HasValidShape `nonce := by
  simp only [Spec.has_valid_shape_iff, uniqid_nonce_eq, uniqid_nonce_support]

instance : UniqId.HasValidShape `seed := by
  simp only [Spec.has_valid_shape_iff, uniqid_seed_eq, uniqid_seed_support]

@[simp] theorem curve25519_publickey_eq : Curve25519.shapeOf `publickey = FFI.KeyExch.PUBLICKEYBYTES := by native_decide
@[simp] theorem curve25519_publickey_valid : Spec.IsValidShape <| Curve25519.shapeOf `publickey := by native_decide
@[simp] theorem curve25519_publickey_support : Spec.IsValidShape FFI.KeyExch.PUBLICKEYBYTES := by
  rw [← curve25519_publickey_eq]
  exact curve25519_publickey_valid

@[simp] theorem curve25519_secretkey_eq : Curve25519.shapeOf `secretkey = FFI.KeyExch.SECRETKEYBYTES := by native_decide
@[simp] theorem curve25519_secretkey_valid : Spec.IsValidShape <| Curve25519.shapeOf `secretkey := by native_decide
@[simp] theorem curve25519_secretkey_support : Spec.IsValidShape FFI.KeyExch.SECRETKEYBYTES := by
  rw [← curve25519_secretkey_eq]
  exact curve25519_secretkey_valid

instance : Curve25519.HasValidShape `publickey := by
  simp only [Spec.has_valid_shape_iff, curve25519_publickey_eq, curve25519_publickey_support]

instance : Curve25519.HasValidShape `secretkey := by
  simp only [Spec.has_valid_shape_iff, curve25519_secretkey_eq, curve25519_secretkey_support]

@[simp] theorem ed25519_publickey_eq : Ed25519.shapeOf `publickey = FFI.Sign.PUBLICKEYBYTES := by native_decide
@[simp] theorem ed25519_publickey_valid : Spec.IsValidShape <| Ed25519.shapeOf `publickey := by native_decide
@[simp] theorem ed25519_publickey_support : Spec.IsValidShape FFI.Sign.PUBLICKEYBYTES := by
  rw [← ed25519_publickey_eq]
  exact ed25519_publickey_valid

@[simp] theorem ed25519_secretkey_eq : Ed25519.shapeOf `secretkey = FFI.Sign.SECRETKEYBYTES := by native_decide
@[simp] theorem ed25519_secretkey_valid : Spec.IsValidShape <| Ed25519.shapeOf `secretkey := by native_decide
@[simp] theorem ed25519_secretkey_support : Spec.IsValidShape FFI.Sign.SECRETKEYBYTES := by
  rw [← ed25519_secretkey_eq]
  exact ed25519_secretkey_valid

@[simp] theorem ed25519_signature_eq : Ed25519.shapeOf `signature = FFI.Sign.BYTES := by native_decide
@[simp] theorem ed25519_signature_valid : Spec.IsValidShape <| Ed25519.shapeOf `signature := by native_decide
@[simp] theorem ed25519_signature_support : Spec.IsValidShape FFI.Sign.BYTES := by
  rw [← ed25519_signature_eq]
  exact ed25519_signature_valid

instance : Ed25519.HasValidShape `publickey := by
  simp only [Spec.has_valid_shape_iff, ed25519_publickey_eq, ed25519_publickey_support]

instance : Ed25519.HasValidShape `secretkey := by
  simp only [Spec.has_valid_shape_iff, ed25519_secretkey_eq, ed25519_secretkey_support]

instance : Ed25519.HasValidShape `signature := by
  simp only [Spec.has_valid_shape_iff, ed25519_signature_eq, ed25519_signature_support]

@[simp] theorem blake2b_symmkey_eq : Blake2b.shapeOf `symmkey = FFI.KeyDeriv.KEYBYTES := by native_decide
@[simp] theorem blake2b_symmkey_valid : Spec.IsValidShape <| Blake2b.shapeOf `symmkey := by native_decide
@[simp] theorem blake2b_symmkey_support : Spec.IsValidShape FFI.KeyDeriv.KEYBYTES := by
  rw [← blake2b_symmkey_eq]
  exact blake2b_symmkey_valid

@[simp] theorem blake2b_context_eq : Blake2b.shapeOf `context = FFI.KeyDeriv.CONTEXTBYTES := by native_decide
@[simp] theorem blake2b_context_valid : Spec.IsValidShape <| Blake2b.shapeOf `context := by native_decide
@[simp] theorem blake2b_context_support : Spec.IsValidShape FFI.KeyDeriv.CONTEXTBYTES := by
  rw [← blake2b_context_eq]
  exact blake2b_context_valid

@[simp] theorem blake2b_hash_eq : Blake2b.shapeOf `hash = FFI.KeyDeriv.BYTES_DEFAULT := by native_decide
@[simp] theorem blake2b_hash_valid : Spec.IsValidShape <| Blake2b.shapeOf `hash := by native_decide
@[simp] theorem blake2b_hash_support : Spec.IsValidShape FFI.KeyDeriv.BYTES_DEFAULT := by
  rw [← blake2b_hash_eq]
  exact blake2b_hash_valid

instance : Blake2b.HasValidShape `symmkey := by
  simp only [Spec.has_valid_shape_iff, blake2b_symmkey_eq, blake2b_symmkey_support]

instance : Blake2b.HasValidShape `context := by
  simp only [Spec.has_valid_shape_iff, blake2b_context_eq, blake2b_context_support]

instance : Blake2b.HasValidShape `hash := by
  simp only [Spec.has_valid_shape_iff, blake2b_hash_eq, blake2b_hash_support]

@[simp] theorem xsalsa20_nonce_eq : XSalsa20.shapeOf `nonce = FFI.SecretBox.NONCEBYTES := by native_decide
@[simp] theorem xsalsa20_nonce_valid : Spec.IsValidShape <| XSalsa20.shapeOf `nonce := by native_decide
@[simp] theorem xsalsa20_nonce_support : Spec.IsValidShape FFI.SecretBox.NONCEBYTES := by
  rw [← xsalsa20_nonce_eq]
  exact xsalsa20_nonce_valid

@[simp] theorem xsalsa20_symmkey_eq : XSalsa20.shapeOf `symmkey = FFI.SecretBox.KEYBYTES := by native_decide
@[simp] theorem xsalsa20_symmkey_valid : Spec.IsValidShape <| XSalsa20.shapeOf `symmkey := by native_decide
@[simp] theorem xsalsa20_symmkey_support : Spec.IsValidShape FFI.SecretBox.KEYBYTES := by
  rw [← xsalsa20_symmkey_eq]
  exact xsalsa20_symmkey_valid

instance : XSalsa20.HasValidShape `nonce := by
  simp only [Spec.has_valid_shape_iff, xsalsa20_nonce_eq, xsalsa20_nonce_support]

instance : XSalsa20.HasValidShape `symmkey := by
  simp only [Spec.has_valid_shape_iff, xsalsa20_symmkey_eq, xsalsa20_symmkey_support]

@[simp] theorem hsalsa20_sharedkey_eq : HSalsa20.shapeOf `sharedkey = FFI.Box.SHAREDBYTES := by native_decide
@[simp] theorem hsalsa20_sharedkey_valid : Spec.IsValidShape <| HSalsa20.shapeOf `sharedkey := by native_decide
@[simp] theorem hsalsa20_sharedkey_support : Spec.IsValidShape FFI.Box.SHAREDBYTES := by
  rw [← hsalsa20_sharedkey_eq]
  exact hsalsa20_sharedkey_valid

instance : HSalsa20.HasValidShape `sharedkey := by
  simp only [Spec.has_valid_shape_iff, hsalsa20_sharedkey_eq, hsalsa20_sharedkey_support]

@[simp] theorem poly1305_mac_eq : Poly1305.shapeOf `mac = FFI.Box.MACBYTES := by native_decide
@[simp] theorem poly1305_mac_valid : Spec.IsValidShape <| Poly1305.shapeOf `mac := by native_decide
@[simp] theorem poly1305_mac_support : Spec.IsValidShape FFI.Box.MACBYTES := by
  rw [← poly1305_mac_eq]
  exact poly1305_mac_valid

@[simp]
theorem curve25519xsalsa20poly1305_seal_eq :
    FFI.Box.SEALBYTES =
      Curve25519XSalsa20Poly1305.shapeOf `publickey +
      Curve25519XSalsa20Poly1305.shapeOf `mac := by
  native_decide

instance : Poly1305.HasValidShape `mac := by
  simp only [Spec.has_valid_shape_iff, poly1305_mac_eq, poly1305_mac_support]

@[simp] theorem xchacha20_symmkey_eq : XChaCha20.shapeOf `symmkey = FFI.Aead.KEYBYTES := by native_decide
@[simp] theorem xchacha20_symmkey_valid : Spec.IsValidShape <| XChaCha20.shapeOf `symmkey := by native_decide
@[simp] theorem xchacha20_symmkey_support : Spec.IsValidShape FFI.Aead.KEYBYTES := by
  rw [← xchacha20_symmkey_eq]
  exact xchacha20_symmkey_valid

@[simp] theorem xchacha20_nonce_eq : XChaCha20.shapeOf `nonce = FFI.Aead.NONCEBYTES := by native_decide
@[simp] theorem xchacha20_nonce_valid : Spec.IsValidShape <| XChaCha20.shapeOf `nonce := by native_decide
@[simp] theorem xchacha20_nonce_support : Spec.IsValidShape FFI.Aead.NONCEBYTES := by
  rw [← xchacha20_nonce_eq]
  exact xchacha20_nonce_valid

@[simp] theorem xchacha20_header_eq : XChaCha20.shapeOf `header = FFI.SecretStream.HEADERBYTES := by native_decide
@[simp] theorem xchacha20_header_valid : Spec.IsValidShape <| XChaCha20.shapeOf `header := by native_decide
@[simp] theorem xchacha20_header_support : Spec.IsValidShape FFI.SecretStream.HEADERBYTES := by
  rw [← xchacha20_header_eq]
  exact xchacha20_header_valid

instance : XChaCha20.HasValidShape `symmkey := by
  simp only [Spec.has_valid_shape_iff, xchacha20_symmkey_eq, xchacha20_symmkey_support]

instance : XChaCha20.HasValidShape `nonce := by
  simp only [Spec.has_valid_shape_iff, xchacha20_nonce_eq, xchacha20_nonce_support]

instance : XChaCha20.HasValidShape `header := by
  simp only [Spec.has_valid_shape_iff, xchacha20_header_eq, xchacha20_header_support]

instance : XSalsa20Poly1305.HasValidShape `nonce := by native_decide
instance : XSalsa20Poly1305.HasValidShape `symmkey := by native_decide
instance : XSalsa20Poly1305.HasValidShape `mac := by native_decide

instance : XChaCha20Poly1305.HasValidShape `symmkey := by native_decide
instance : XChaCha20Poly1305.HasValidShape `nonce := by native_decide
instance : XChaCha20Poly1305.HasValidShape `header := by native_decide
instance : XChaCha20Poly1305.HasValidShape `mac := by native_decide

instance : Curve25519HSalsa20.HasValidShape `publickey := by native_decide
instance : Curve25519HSalsa20.HasValidShape `secretkey := by native_decide
instance : Curve25519HSalsa20.HasValidShape `sharedkey := by native_decide

instance : Curve25519XSalsa20Poly1305.HasValidShape `nonce := by native_decide
instance : Curve25519XSalsa20Poly1305.HasValidShape `mac := by native_decide
instance : Curve25519XSalsa20Poly1305.HasValidShape `symmkey := by native_decide
instance : Curve25519XSalsa20Poly1305.HasValidShape `publickey := by native_decide
instance : Curve25519XSalsa20Poly1305.HasValidShape `secretkey := by native_decide

instance : Curve25519Blake2b.HasValidShape `publickey := by native_decide
instance : Curve25519Blake2b.HasValidShape `secretkey := by native_decide
instance : Curve25519Blake2b.HasValidShape `symmkey := by native_decide
instance : Curve25519Blake2b.HasValidShape `context := by native_decide

end Sodium.Crypto
