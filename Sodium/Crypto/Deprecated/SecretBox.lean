/-
Type-safe SecretBox cryptography operations using the CryptoM monad.

This module provides high-level, fuel-managed wrappers around the LibSodium secretbox
operations, ensuring proper nonce management and type safety.
-/
import Sodium.FFI.Deprecated.SecretBox
import Sodium.Crypto.Monad
import Sodium.Crypto.Utils

open Lean

namespace Sodium.Crypto.SecretBox

open Utils

abbrev SecretBoxKey := SecretKey SecretBoxSpec
abbrev SecretBoxNonce := NonceId SecretBoxSpec
abbrev SecretBoxCipherText := CipherText SecretBoxSpec
abbrev SecretBoxMac := Mac SecretBoxSpec
abbrev SecretBoxDetachedCipherText := DetachedCipherText SecretBoxSpec

/--
Generate a new SecretBox key using LibSodium's secure random number generator.
This operation does not consume fuel as it uses LibSodium's internal entropy.
-/
def genKey : CryptoM SecretBoxKey := do
  let keyBytes ← FFI.secretBoxKeygen
  -- FFI guarantees exactly SECRETBOX_KEYBYTES (32) bytes
  if h : keyBytes.size = SecretBoxSpec.secretKeyBytes then
    return ⟨keyBytes, h⟩
  else
    -- This should never happen if FFI is implemented correctly
    throwMessage m!"invariant failed in {decl_name%}"

variable {α : Type}

/--
Encrypt a message using SecretBox with automatically generated nonce.
Returns both the nonce and ciphertext for complete operation information.
May consume fuel for nonce generation.
-/
def encrypt [ToJson α] (key : SecretBoxKey) (msg : α) : CryptoM (SecretBoxNonce × SecretBoxCipherText) := do
  let nonce ← mkFreshNonceId SecretBoxSpec
  let payload := toJson msg |>.compress.toUTF8
  let bytes ← FFI.secretBoxEasy payload nonce key
  -- FFI guarantees ciphertext length = message length + MAC bytes
  if h : bytes.size ≥ SecretBoxSpec.macBytes then
    let ciphertext := ⟨bytes, h⟩
    return (nonce, ciphertext)
  else
    -- This should never happen if FFI is implemented correctly
    throwMessage m!"invariant failed in {decl_name%}"

/--
Encrypt a message using SecretBox with an explicitly provided nonce.
This operation does not consume fuel as no nonce generation is required.
Use this for deterministic encryption or when managing nonces externally.
-/
def encryptWith [ToJson α] (nonce : SecretBoxNonce) (key : SecretBoxKey) (msg : α) : CryptoM SecretBoxCipherText := do
  let payload := toJson msg |>.compress.toUTF8
  let cipherBytes ← FFI.secretBoxEasy payload nonce key
  -- FFI guarantees ciphertext length = message length + MAC bytes
  if h : cipherBytes.size ≥ SecretBoxSpec.macBytes then
    return ⟨cipherBytes, h⟩
  else
    -- This should never happen if FFI is implemented correctly
    throwMessage m!"invariant failed in {decl_name%}"

/--
Decrypt a SecretBox ciphertext using the provided nonce and key.
Returns the original message if authentication succeeds.
Returns an error if authentication fails or decryption is not possible.
-/
def decrypt [FromJson α] (nonce : SecretBoxNonce) (key : SecretBoxKey) (ct : SecretBoxCipherText) : CryptoM (Except ByteArray α) := do
  let bytes ← FFI.secretBoxOpenEasy ct nonce key
  return match String.fromUTF8? bytes with
  | none => .error bytes
  | some utf8 => Json.parse utf8 >>= fromJson? |>.mapError (·.toUTF8)

/-- Result type for detached mode encryption -/
structure DetachedResult where
  ciphertext : SecretBoxDetachedCipherText
  mac : SecretBoxMac

/--
Encrypt a message using SecretBox detached mode with automatically generated nonce.
Returns the nonce, ciphertext, and MAC separately for protocols that need granular control.
May consume fuel for nonce generation.
-/
def encryptDetached [ToJson α] (key : SecretBoxKey) (msg : α) : CryptoM (SecretBoxNonce × DetachedResult) := do
  let nonce ← mkFreshNonceId SecretBoxSpec
  let payload := toJson msg |>.compress.toUTF8

  -- Validate message size
  if !(← validateMessageSize payload.size) then
    throwMessage m!"invariant failed in {decl_name%} - message too large for SecretBox encryption"

  let (cipherBytes, macBytes) ← FFI.secretBoxDetached payload nonce key

  -- Type-safe construction with size validation
  if h1 : macBytes.size = SecretBoxSpec.macBytes then
    let mac := ⟨macBytes, h1⟩
    let ciphertext := ⟨cipherBytes⟩
    return (nonce, ⟨ciphertext, mac⟩)
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Encrypt a message using SecretBox detached mode with an explicitly provided nonce.
This operation does not consume fuel as no nonce generation is required.
-/
def encryptDetachedWith [ToJson α] (nonce : SecretBoxNonce) (key : SecretBoxKey) (msg : α) : CryptoM DetachedResult := do
  let payload := toJson msg |>.compress.toUTF8

  if !(← validateMessageSize payload.size) then
    throwMessage m!"invariant failed in {decl_name%} - message too large for SecretBox encryption"

  let (cipherBytes, macBytes) ← FFI.secretBoxDetached payload nonce key

  -- Type-safe construction with size validation
  if h1 : macBytes.size = SecretBoxSpec.macBytes then
    let mac := ⟨macBytes, h1⟩
    let ciphertext := ⟨cipherBytes⟩
    return ⟨ciphertext, mac⟩
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Decrypt a SecretBox detached mode ciphertext using the provided nonce, key, and MAC.
Returns the original message if authentication succeeds.
Uses constant-time MAC verification for security.
-/
def decryptDetached [FromJson α] (nonce : SecretBoxNonce) (key : SecretBoxKey)
    (mac : SecretBoxMac) (ciphertext : SecretBoxDetachedCipherText) : CryptoM (Except ByteArray α) := do
  let bytes ← FFI.secretBoxOpenDetached ciphertext mac nonce key
  return match String.fromUTF8? bytes with
  | none => .error bytes
  | some utf8 => Json.parse utf8 >>= fromJson? |>.mapError (·.toUTF8)

end Sodium.Crypto.SecretBox
