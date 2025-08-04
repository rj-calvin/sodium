/-
Type-safe Box (public-key authenticated encryption) operations using the CryptoM monad.

This module provides high-level, fuel-managed wrappers around the LibSodium box
operations, ensuring proper nonce management and type safety for public-key cryptography.
-/
import Sodium.FFI.Box
import Sodium.Crypto.Monad
import Sodium.Crypto.Utils

open Lean

namespace Sodium.Crypto.Box

open Utils

abbrev BoxPublicKey := PublicKey BoxSpec
abbrev BoxSecretKey := SecretKey BoxSpec
abbrev BoxNonce := NonceId BoxSpec
abbrev BoxKeyPair := KeyPair BoxSpec
abbrev BoxCipherText := CipherText BoxSpec
abbrev BoxMac := Mac BoxSpec
abbrev BoxDetachedCipherText := DetachedCipherText BoxSpec
abbrev BoxSealedCipherText := SealedCipherText BoxSpec

/-- Precomputed shared secret for performance optimization -/
structure SharedSecret where
  bytes : ByteArray
  size_eq : bytes.size = BoxSpec.beforeNmBytes

/--
Generate a new Box key pair using LibSodium's secure random number generator.
This operation does not consume fuel as it uses LibSodium's internal entropy.
-/
def genKeyPair : CryptoM BoxKeyPair := do
  let (publicBytes, secretBytes) ← FFI.boxKeypair
  -- FFI guarantees exact sizes
  if h1 : publicBytes.size = BoxSpec.publicKeyBytes then
    if h2 : secretBytes.size = BoxSpec.secretKeyBytes then
      let publicKey := ⟨publicBytes, h1⟩
      let secretKey := ⟨secretBytes, h2⟩
      return ⟨publicKey, secretKey⟩
    else
      throwMessage m!"invariant failed in {decl_name%} - invalid secret key size"
  else
    throwMessage m!"invariant failed in {decl_name%} - invalid public key size"

/--
Generate a Box key pair from a seed for deterministic key generation.
This operation does not consume fuel as it uses the provided seed.
-/
def genKeyPairFromSeed (seed : Seed BoxSpec) : CryptoM BoxKeyPair := do
  let (publicBytes, secretBytes) ← FFI.boxSeedKeypair seed
  -- FFI guarantees exact sizes
  if h1 : publicBytes.size = BoxSpec.publicKeyBytes then
    if h2 : secretBytes.size = BoxSpec.secretKeyBytes then
      let publicKey := ⟨publicBytes, h1⟩
      let secretKey := ⟨secretBytes, h2⟩
      return ⟨publicKey, secretKey⟩
    else
      throwMessage m!"invariant failed in {decl_name%} - invalid secret key size"
  else
    throwMessage m!"invariant failed in {decl_name%} - invalid public key size"

variable {α : Type}

/--
Encrypt a message using Box with automatically generated nonce.
Returns the nonce and ciphertext for complete operation information.
May consume fuel for nonce generation.
-/
def encrypt [ToJson α] (keyPair : BoxKeyPair) (msg : α) : CryptoM (BoxNonce × BoxCipherText) := do
  let nonce ← mkFreshNonceId BoxSpec
  let payload := toJson msg |>.compress.toUTF8
  let bytes ← FFI.boxEasy payload nonce keyPair.public keyPair.secret
  -- FFI guarantees ciphertext length = message length + MAC bytes
  if h : bytes.size ≥ BoxSpec.macBytes then
    let ciphertext := ⟨bytes, h⟩
    return (nonce, ciphertext)
  else
    -- This should never happen if FFI is implemented correctly
    throwMessage m!"invariant failed in {decl_name%}"

/--
Encrypt a message using Box with an explicitly provided nonce.
This operation does not consume fuel as no nonce generation is required.
Use this for deterministic encryption or when managing nonces externally.
-/
def encryptWith [ToJson α] (nonce : BoxNonce) (keyPair : BoxKeyPair) (msg : α) : CryptoM BoxCipherText := do
  let payload := toJson msg |>.compress.toUTF8
  let bytes ← FFI.boxEasy payload nonce keyPair.public keyPair.secret
  -- FFI guarantees ciphertext length = message length + MAC bytes
  if h : bytes.size ≥ BoxSpec.macBytes then
    return ⟨bytes, h⟩
  else
    -- This should never happen if FFI is implemented correctly
    throwMessage m!"invariant failed in {decl_name%}"

/--
Decrypt a Box ciphertext using the provided nonce and key pair.
Returns the original message if authentication succeeds.
Returns an error if authentication fails or decryption is not possible.
-/
def decrypt [FromJson α] (nonce : BoxNonce) (keyPair : BoxKeyPair) (ct : BoxCipherText) : CryptoM (Except ByteArray α) := do
  let bytes ← FFI.boxOpenEasy ct nonce keyPair.public keyPair.secret
  return match String.fromUTF8? bytes with
  | none => .error bytes
  | some utf8 => Json.parse utf8 >>= fromJson? |>.mapError (·.toUTF8)

/-- Result type for detached mode encryption -/
structure DetachedResult where
  ciphertext : BoxDetachedCipherText
  mac : BoxMac

/--
Encrypt a message using Box detached mode with automatically generated nonce.
Returns the nonce, ciphertext, and MAC separately for protocols that need granular control.
May consume fuel for nonce generation.
-/
def encryptDetached [ToJson α] (keyPair : BoxKeyPair) (msg : α) : CryptoM (BoxNonce × DetachedResult) := do
  let nonce ← mkFreshNonceId BoxSpec
  let payload := toJson msg |>.compress.toUTF8

  if !(← validateMessageSize payload.size) then
    throwMessage m!"invariant failed in {decl_name%} - message too large for Box encryption"

  let (cipherBytes, macBytes) ← FFI.boxDetached payload nonce keyPair.public keyPair.secret

  -- Type-safe construction with size validation
  if h1 : macBytes.size = BoxSpec.macBytes then
    let mac := ⟨macBytes, h1⟩
    let ciphertext := ⟨cipherBytes⟩
    return (nonce, ⟨ciphertext, mac⟩)
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Encrypt a message using Box detached mode with an explicitly provided nonce.
This operation does not consume fuel as no nonce generation is required.
-/
def encryptDetachedWith [ToJson α] (nonce : BoxNonce) (keyPair : BoxKeyPair) (msg : α) : CryptoM DetachedResult := do
  let payload := toJson msg |>.compress.toUTF8

  if !(← validateMessageSize payload.size) then
    throwMessage m!"invariant failed in {decl_name%} - message too large for Box encryption"

  let (cipherBytes, macBytes) ← FFI.boxDetached payload nonce keyPair.public keyPair.secret

  -- Type-safe construction with size validation
  if h1 : macBytes.size = BoxSpec.macBytes then
    let mac := ⟨macBytes, h1⟩
    let ciphertext := ⟨cipherBytes⟩
    return ⟨ciphertext, mac⟩
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Decrypt a Box detached mode ciphertext using the provided nonce, key pair, and MAC.
Returns the original message if authentication succeeds.
Uses constant-time MAC verification for security.
-/
def decryptDetached [FromJson α] (nonce : BoxNonce) (keyPair : BoxKeyPair)
    (mac : BoxMac) (ciphertext : BoxDetachedCipherText) : CryptoM (Except ByteArray α) := do
  let bytes ← FFI.boxOpenDetached ciphertext mac nonce keyPair.public keyPair.secret
  return match String.fromUTF8? bytes with
  | none => .error bytes
  | some utf8 => Json.parse utf8 >>= fromJson? |>.mapError (·.toUTF8)

/--
Precompute the shared secret between a public key and secret key for performance.
This is useful when multiple operations will be performed with the same key pair.
-/
def precompute (publicKey : BoxPublicKey) (secretKey : BoxSecretKey) : CryptoM SharedSecret := do
  let sharedBytes ← FFI.boxBeforenm publicKey secretKey
  if h : sharedBytes.size = BoxSpec.beforeNmBytes then
    return ⟨sharedBytes, h⟩
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Encrypt a message using a precomputed shared secret with automatically generated nonce.
This is more efficient when performing multiple operations with the same key pair.
May consume fuel for nonce generation.
-/
def postEncrypt [ToJson α] (sharedSecret : SharedSecret) (msg : α) : CryptoM (BoxNonce × BoxCipherText) := do
  let nonce ← mkFreshNonceId BoxSpec
  let payload := toJson msg |>.compress.toUTF8
  let bytes ← FFI.boxEasyAfternm payload nonce sharedSecret.bytes
  if h : bytes.size ≥ BoxSpec.macBytes then
    let ciphertext := ⟨bytes, h⟩
    return (nonce, ciphertext)
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Encrypt a message using a precomputed shared secret with an explicitly provided nonce.
This operation does not consume fuel as no nonce generation is required.
-/
def postEncryptWith [ToJson α] (nonce : BoxNonce) (sharedSecret : SharedSecret) (msg : α) : CryptoM BoxCipherText := do
  let payload := toJson msg |>.compress.toUTF8
  let bytes ← FFI.boxEasyAfternm payload nonce sharedSecret.bytes
  if h : bytes.size ≥ BoxSpec.macBytes then
    return ⟨bytes, h⟩
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Decrypt a Box ciphertext using a precomputed shared secret.
Returns the original message if authentication succeeds.
-/
def postDecrypt [FromJson α] (nonce : BoxNonce) (sharedSecret : SharedSecret) (ct : BoxCipherText) : CryptoM (Except ByteArray α) := do
  let bytes ← FFI.boxOpenEasyAfternm ct nonce sharedSecret.bytes
  return match String.fromUTF8? bytes with
  | none => .error bytes
  | some utf8 => Json.parse utf8 >>= fromJson? |>.mapError (·.toUTF8)

/--
Encrypt a message using detached mode with a precomputed shared secret and automatically generated nonce.
May consume fuel for nonce generation.
-/
def postEncryptDetached [ToJson α] (sharedSecret : SharedSecret) (msg : α) : CryptoM (BoxNonce × DetachedResult) := do
  let nonce ← mkFreshNonceId BoxSpec
  let payload := toJson msg |>.compress.toUTF8

  if !(← validateMessageSize payload.size) then
    throwMessage m!"invariant failed in {decl_name%} - message too large for Box encryption"

  let (cipherBytes, macBytes) ← FFI.boxDetachedAfternm payload nonce sharedSecret.bytes

  if h1 : macBytes.size = BoxSpec.macBytes then
    let mac := ⟨macBytes, h1⟩
    let ciphertext := ⟨cipherBytes⟩
    return (nonce, ⟨ciphertext, mac⟩)
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Encrypt a message using detached mode with a precomputed shared secret and explicitly provided nonce.
This operation does not consume fuel as no nonce generation is required.
-/
def postEncryptDetachedWith [ToJson α] (nonce : BoxNonce) (sharedSecret : SharedSecret) (msg : α) : CryptoM DetachedResult := do
  let payload := toJson msg |>.compress.toUTF8

  if !(← validateMessageSize payload.size) then
    throwMessage m!"invariant failed in {decl_name%} - message too large for Box encryption"

  let (cipherBytes, macBytes) ← FFI.boxDetachedAfternm payload nonce sharedSecret.bytes

  if h1 : macBytes.size = BoxSpec.macBytes then
    let mac := ⟨macBytes, h1⟩
    let ciphertext := ⟨cipherBytes⟩
    return ⟨ciphertext, mac⟩
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Decrypt a Box detached mode ciphertext using a precomputed shared secret.
Returns the original message if authentication succeeds.
-/
def postDecryptDetached [FromJson α] (nonce : BoxNonce) (sharedSecret : SharedSecret)
    (mac : BoxMac) (ciphertext : BoxDetachedCipherText) : CryptoM (Except ByteArray α) := do
  let bytes ← FFI.boxOpenDetachedAfternm ciphertext mac nonce sharedSecret.bytes
  return match String.fromUTF8? bytes with
  | none => .error bytes
  | some utf8 => Json.parse utf8 >>= fromJson? |>.mapError (·.toUTF8)

/--
Anonymously encrypt a message using sealed box (ephemeral key pair).
The recipient only needs to know their own keypair to decrypt.
This operation does not consume fuel as LibSodium generates the ephemeral key internally.
-/
def enclose [ToJson α] (publicKey : BoxPublicKey) (msg : α) : CryptoM BoxSealedCipherText := do
  let payload := toJson msg |>.compress.toUTF8
  let bytes ← FFI.boxSeal payload publicKey
  if h : bytes.size ≥ BoxSpec.sealBytes then
    return ⟨bytes, h⟩
  else
    throwMessage m!"invariant failed in {decl_name%}"

/--
Decrypt a sealed box ciphertext using the recipient's key pair.
Returns the original message if authentication succeeds.
-/
def declose [FromJson α] (keyPair : BoxKeyPair) (ct : BoxSealedCipherText) : CryptoM (Except ByteArray α) := do
  let bytes ← FFI.boxSealOpen ct keyPair.public keyPair.secret
  return match String.fromUTF8? bytes with
  | none => .error bytes
  | some utf8 => Json.parse utf8 >>= fromJson? |>.mapError (·.toUTF8)

end Sodium.Crypto.Box
