/-
Type-safe AEAD (Authenticated Encryption with Associated Data) operations using the CryptoM monad.

This module provides high-level, fuel-managed wrappers around LibSodium AEAD operations,
ensuring proper nonce management and type safety for authenticated encryption with associated data.
Supports ChaCha20-Poly1305 (IETF and Original), XChaCha20-Poly1305 IETF variants.
-/
import Sodium.FFI.Deprecated.Aead
import Sodium.Crypto.Monad
import Sodium.Crypto.Utils

open Lean

namespace Sodium.Crypto.Aead

open Utils

variable {α : Type}


/- ChaCha20-Poly1305 Original Functions -/

/--
Generate a new ChaCha20-Poly1305 Original secret key using LibSodium's secure random number generator.
This operation does not consume fuel as it uses LibSodium's internal entropy.
-/
def genKey : CryptoM ChaCha20Poly1305SecretKey := do
  let keyBytes ← FFI.chacha20poly1305Keygen
  if h : keyBytes.size = ChaCha20Poly1305Spec.secretKeyBytes then
    return ⟨keyBytes, h⟩
  else
    throwMessage m!"invariant failed in {decl_name%} - invalid key size"

/--
Encrypt a message using ChaCha20-Poly1305 Original with automatically generated nonce.
Returns the nonce and authenticated ciphertext.
May consume fuel for nonce generation.
-/
def encrypt [ToJson α] (key : ChaCha20Poly1305SecretKey) (msg : α) (ad : ByteArray := ByteArray.empty)
    : CryptoM (ChaCha20Poly1305Nonce × TaggedCipherText ChaCha20Poly1305Spec) := do
  let nonce ← mkFreshNonceId ChaCha20Poly1305Spec
  let payload := toJson msg |>.compress.toUTF8
  let bytes ← FFI.chacha20poly1305Encrypt payload ad nonce key
  if h : bytes.size ≥ ChaCha20Poly1305Spec.tagBytes then
    let result := ⟨bytes, h⟩
    return (nonce, result)
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Encrypt a message using ChaCha20-Poly1305 Original with an explicitly provided nonce.
This operation does not consume fuel as no nonce generation is required.
-/
def encryptWith [ToJson α] (nonce : ChaCha20Poly1305Nonce) (key : ChaCha20Poly1305SecretKey)
    (msg : α) (ad : ByteArray := ByteArray.empty) : CryptoM (TaggedCipherText ChaCha20Poly1305Spec) := do
  let payload := toJson msg |>.compress.toUTF8
  let bytes ← FFI.chacha20poly1305Encrypt payload ad nonce key
  if h : bytes.size ≥ ChaCha20Poly1305Spec.tagBytes then
    return ⟨bytes, h⟩
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Decrypt a ChaCha20-Poly1305 Original ciphertext using the provided nonce and key.
Returns the original message if authentication succeeds.
Returns an error if authentication fails or decryption is not possible.
-/
def decrypt [FromJson α] (nonce : ChaCha20Poly1305Nonce) (key : ChaCha20Poly1305SecretKey)
    (ciphertext : TaggedCipherText ChaCha20Poly1305Spec) (ad : ByteArray := ByteArray.empty) : CryptoM (Except ByteArray α) := do
  let bytes ← FFI.chacha20poly1305Decrypt ciphertext ad nonce key
  return match String.fromUTF8? bytes with
  | none => .error bytes
  | some utf8 => Json.parse utf8 >>= fromJson? |>.mapError (·.toUTF8)

namespace Ietf

/--
Generate a new ChaCha20-Poly1305 IETF secret key using LibSodium's secure random number generator.
This operation does not consume fuel as it uses LibSodium's internal entropy.
-/
def genKey : CryptoM ChaCha20Poly1305IetfSecretKey := do
  let keyBytes ← FFI.chacha20poly1305IetfKeygen
  if h : keyBytes.size = ChaCha20Poly1305IetfSpec.secretKeyBytes then
    return ⟨keyBytes, h⟩
  else
    throwMessage m!"invariant failed in {decl_name%} - invalid key size"

/--
Encrypt a message using ChaCha20-Poly1305 IETF with automatically generated nonce.
Returns the nonce and authenticated ciphertext.
May consume fuel for nonce generation.
-/
def encrypt [ToJson α] (key : ChaCha20Poly1305IetfSecretKey) (msg : α) (ad : ByteArray := ByteArray.empty)
    : CryptoM (ChaCha20Poly1305IetfNonce × TaggedCipherText ChaCha20Poly1305IetfSpec) := do
  let nonce ← mkFreshNonceId ChaCha20Poly1305IetfSpec
  let payload := toJson msg |>.compress.toUTF8
  let bytes ← FFI.chacha20poly1305IetfEncrypt payload ad nonce key
  if h : bytes.size ≥ ChaCha20Poly1305IetfSpec.tagBytes then
    let result := ⟨bytes, h⟩
    return (nonce, result)
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Encrypt a message using ChaCha20-Poly1305 IETF with an explicitly provided nonce.
This operation does not consume fuel as no nonce generation is required.
-/
def encryptWith [ToJson α] (nonce : ChaCha20Poly1305IetfNonce) (key : ChaCha20Poly1305IetfSecretKey)
    (msg : α) (ad : ByteArray := ByteArray.empty) : CryptoM (TaggedCipherText ChaCha20Poly1305IetfSpec) := do
  let payload := toJson msg |>.compress.toUTF8
  let bytes ← FFI.chacha20poly1305IetfEncrypt payload ad nonce key
  if h : bytes.size ≥ ChaCha20Poly1305IetfSpec.tagBytes then
    return ⟨bytes, h⟩
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Decrypt a ChaCha20-Poly1305 IETF ciphertext using the provided nonce and key.
Returns the original message if authentication succeeds.
Returns an error if authentication fails or decryption is not possible.
-/
def decrypt [FromJson α] (nonce : ChaCha20Poly1305IetfNonce) (key : ChaCha20Poly1305IetfSecretKey)
    (ciphertext : TaggedCipherText ChaCha20Poly1305IetfSpec) (ad : ByteArray := ByteArray.empty) : CryptoM (Except ByteArray α) := do
  let bytes ← FFI.chacha20poly1305IetfDecrypt ciphertext ad nonce key
  return match String.fromUTF8? bytes with
  | none => .error bytes
  | some utf8 => Json.parse utf8 >>= fromJson? |>.mapError (·.toUTF8)

end Ietf

namespace XIetf

/--
Generate a new XChaCha20-Poly1305 IETF secret key using LibSodium's secure random number generator.
This operation does not consume fuel as it uses LibSodium's internal entropy.
-/
def genKey : CryptoM XChaCha20Poly1305IetfSecretKey := do
  let keyBytes ← FFI.xchacha20poly1305IetfKeygen
  if h : keyBytes.size = XChaCha20Poly1305IetfSpec.secretKeyBytes then
    return ⟨keyBytes, h⟩
  else
    throwMessage m!"invariant failed in {decl_name%} - invalid key size"

/--
Encrypt a message using XChaCha20-Poly1305 IETF with automatically generated nonce.
Returns the nonce and authenticated ciphertext.
May consume fuel for nonce generation.
-/
def encrypt [ToJson α] (key : XChaCha20Poly1305IetfSecretKey) (msg : α) (ad : ByteArray := ByteArray.empty)
    : CryptoM (XChaCha20Poly1305IetfNonce × TaggedCipherText XChaCha20Poly1305IetfSpec) := do
  let nonce ← mkFreshNonceId XChaCha20Poly1305IetfSpec
  let payload := toJson msg |>.compress.toUTF8
  let bytes ← FFI.xchacha20poly1305IetfEncrypt payload ad nonce key
  if h : bytes.size ≥ XChaCha20Poly1305IetfSpec.tagBytes then
    let result := ⟨bytes, h⟩
    return (nonce, result)
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Encrypt a message using XChaCha20-Poly1305 IETF with an explicitly provided nonce.
This operation does not consume fuel as no nonce generation is required.
-/
def encryptWith [ToJson α] (nonce : XChaCha20Poly1305IetfNonce) (key : XChaCha20Poly1305IetfSecretKey)
    (msg : α) (ad : ByteArray := ByteArray.empty) : CryptoM (TaggedCipherText XChaCha20Poly1305IetfSpec) := do
  let payload := toJson msg |>.compress.toUTF8
  let bytes ← FFI.xchacha20poly1305IetfEncrypt payload ad nonce key
  if h : bytes.size ≥ XChaCha20Poly1305IetfSpec.tagBytes then
    return ⟨bytes, h⟩
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Decrypt a XChaCha20-Poly1305 IETF ciphertext using the provided nonce and key.
Returns the original message if authentication succeeds.
Returns an error if authentication fails or decryption is not possible.
-/
def decrypt [FromJson α] (nonce : XChaCha20Poly1305IetfNonce) (key : XChaCha20Poly1305IetfSecretKey)
    (ciphertext : TaggedCipherText XChaCha20Poly1305IetfSpec) (ad : ByteArray := ByteArray.empty) : CryptoM (Except ByteArray α) := do
  let bytes ← FFI.xchacha20poly1305IetfDecrypt ciphertext ad nonce key
  return match String.fromUTF8? bytes with
  | none => .error bytes
  | some utf8 => Json.parse utf8 >>= fromJson? |>.mapError (·.toUTF8)

end XIetf

end Sodium.Crypto.Aead
