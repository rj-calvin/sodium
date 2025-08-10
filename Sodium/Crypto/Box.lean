import Lean.Data.Json
import Sodium.FFI.Box
import Sodium.Crypto.Monad

open Lean

/-!
# Box Authenticated Encryption

This module provides type-safe wrappers around LibSodium's Box authenticated encryption.

Box uses:
- **Curve25519** for key exchange (ECDH)
- **XSalsa20** for encryption
- **Poly1305** for authentication

## Usage Patterns

**Basic encryption/decryption:**
```lean
let myKeyPair ← mkFreshKeyPair
let theirPublicKey := -- obtained from other party
let ciphertext ← encrypt myKeyPair theirPublicKey message  -- nonce embedded in result
let .ok plaintext ← decrypt myKeyPair theirPublicKey ciphertext | throw "decryption failed"
```

**Optimized for multiple messages (shared secret):**
```lean
let shared ← mkSharedSecret myKeyPair theirPublicKey
let ciphertext ← encryptWithShared shared message  -- nonce embedded in result
let .ok plaintext ← decryptWithShared shared ciphertext | throw "decryption failed"
```

**Detached operations (separate MAC):**
```lean
let detachedCipher ← encryptDetached myKeyPair theirPublicKey message  -- nonce + MAC embedded
let .ok plaintext ← decryptDetached myKeyPair theirPublicKey detachedCipher | throw "decryption failed"
```

## Security Considerations

- **Nonce uniqueness**: Never reuse nonces with the same keypair
- **Key generation**: Use `mkFreshKeyPair` for random keys or `mkDetKeyPair` for deterministic
- **Shared secrets**: Cache shared secrets for better performance with multiple messages
- **Memory safety**: Secret keys and shared secrets are automatically stored in secure memory
-/

namespace Sodium.Crypto.Box

open FFI Box

-- ================================
-- Specification and Type Aliases
-- ================================

def BoxSpec : Spec where
  name := `curve25519xsalsa20poly1305
  secretKeyBytes := SECRETKEYBYTES
  publicKeyBytes := PUBLICKEYBYTES
  nonceBytes := NONCEBYTES
  macBytes := MACBYTES
  seedBytes := SEEDBYTES
  sharedBytes := SHAREDBYTES
  sealBytes := SEALBYTES

variable {α σ : Type} (τ : Sodium σ)

/-- Convenient aliases for Box operations -/
abbrev BoxKeyPair := KeyPair τ BoxSpec
abbrev BoxPublicKey := PublicKey BoxSpec
abbrev BoxNonce := NonceId BoxSpec
abbrev BoxCipherText := CipherText BoxSpec
abbrev BoxSharedSecret := SharedSecret τ BoxSpec
abbrev BoxSeed := Seed τ BoxSpec

variable {τ}

-- ================================
-- Key Generation Operations
-- ================================

/-- Generate a fresh Box keypair with compile-time size validation -/
def mkFreshKeyPair : CryptoM τ (BoxKeyPair τ) := do
  let (pub, sec) ← keypair τ
  if h : pub.size = BoxSpec.publicKeyBytes ∧ sec.size = BoxSpec.secretKeyBytes then
    let publicKey := ⟨pub, h.1⟩
    let secretKey := ⟨sec, h.2⟩
    return ⟨publicKey, secretKey⟩
  else throwInvariantFailure

/-- Generate a deterministic Box keypair from seed with compile-time size validation -/
def mkDetKeyPair (seed : BoxSeed τ) : CryptoM τ (BoxKeyPair τ) := do
  let (pub, sec) ← seedKeypair τ seed.bytes
  if h : pub.size = BoxSpec.publicKeyBytes ∧ sec.size = BoxSpec.secretKeyBytes then
    let publicKey := ⟨pub, h.1⟩
    let secretKey := ⟨sec, h.2⟩
    return ⟨publicKey, secretKey⟩
  else throwInvariantFailure

-- ================================
-- Shared Secret Operations
-- ================================

/-- Precompute shared secret for Box operations with compile-time size validation.

    **Performance**: Use this for encrypting multiple messages to the same recipient.
    The expensive Curve25519 scalar multiplication is done once upfront. -/
def mkSharedSecret (keyPair : BoxKeyPair τ) (theirPublicKey : BoxPublicKey) : CryptoM τ (BoxSharedSecret τ) := do
  let shared ← beforenm τ theirPublicKey.bytes keyPair.secret.bytes
  if h : shared.size = BoxSpec.sharedBytes then
    return ⟨shared, h⟩
  else throwInvariantFailure

-- ================================
-- Authenticated Encryption (Easy API)
-- ================================

/-- Encrypt message using Box with keypair and their public key.

    **Security**: Fresh nonce is automatically generated to prevent reuse. -/
def encrypt [ToJson α] (keyPair : BoxKeyPair τ) (theirPublicKey : BoxPublicKey) (message : α) : CryptoM τ BoxCipherText := do
  let nonce ← mkFreshNonceId BoxSpec
  let data := toJson message |>.compress.toUTF8
  let cipher ← easy τ data nonce.bytes theirPublicKey.bytes keyPair.secret.bytes
  if h : cipher.size ≥ BoxSpec.macBytes then
    return ⟨cipher, nonce, h⟩
  else throwInvariantFailure

/-- Encrypt message using precomputed shared secret.

    **Performance**: More efficient than `encrypt` for multiple messages to same recipient. -/
def encryptWithShared [ToJson α] (sharedSecret : BoxSharedSecret τ) (message : α) : CryptoM τ BoxCipherText := do
  let nonce ← mkFreshNonceId BoxSpec
  let data := toJson message |>.compress.toUTF8
  let cipher ← easyAfternm τ data nonce.bytes sharedSecret.bytes
  if h : cipher.size ≥ BoxSpec.macBytes then
    return ⟨cipher, nonce, h⟩
  else throwInvariantFailure

/-- Decrypt message using Box with keypair and their public key.

    **Security**: Uses embedded nonce from ciphertext for decryption. -/
def decrypt [FromJson α] (keyPair : BoxKeyPair τ) (theirPublicKey : BoxPublicKey)
    (ciphertext : BoxCipherText) : CryptoM τ (Except DecryptError α) := do
  try
    let bytes ←
      openEasy τ
        ciphertext.bytes
        ciphertext.nonce.bytes
        theirPublicKey.bytes
        keyPair.secret.bytes
    let some msg := String.fromUTF8? bytes | return .error (.invalidEncoding bytes)
    let .ok json := Json.parse msg | return .error (.invalidString msg)
    let .ok a := fromJson? json | return .error (.invalidJson json)
    return .ok a
  catch _ => return .error .refused

/-- Decrypt message using precomputed shared secret.

    **Performance**: More efficient than `decrypt` when shared secret is precomputed. -/
def decryptWithShared [FromJson α] (sharedSecret : BoxSharedSecret τ)
    (ciphertext : BoxCipherText) : CryptoM τ (Except DecryptError α) := do
  try
    let bytes ← openEasyAfternm τ ciphertext.bytes ciphertext.nonce.bytes sharedSecret.bytes
    let some msg := String.fromUTF8? bytes | return .error (.invalidEncoding bytes)
    let .ok json := Json.parse msg | return .error (.invalidString msg)
    let .ok a := fromJson? json | return .error (.invalidJson json)
    return .ok a
  catch _ => return .error .refused

-- ================================
-- Detached Operations (Separate MAC)
-- ================================

/-- Encrypt message with separate ciphertext and MAC using keypair.

    **Use case**: When MAC needs to be stored or transmitted separately from ciphertext. -/
def encryptDetached [ToJson α] (keyPair : BoxKeyPair τ) (theirPublicKey : BoxPublicKey)
    (message : α) : CryptoM τ (DetachedCipherText BoxSpec) := do
  let nonce ← mkFreshNonceId BoxSpec
  let data := toJson message |>.compress.toUTF8
  let (cipher, mac) ← detached τ data nonce.bytes theirPublicKey.bytes keyPair.secret.bytes
  if h : mac.size = BoxSpec.macBytes then
    return {bytes := cipher, mac := ⟨mac, h⟩, nonce}
  else throwInvariantFailure

/-- Decrypt message with separate ciphertext and MAC using keypair.

    **Security**: Uses embedded nonce and MAC from detached ciphertext. -/
def decryptDetached [FromJson α] (keyPair : BoxKeyPair τ) (theirPublicKey : BoxPublicKey)
    (ciphertext : DetachedCipherText BoxSpec) : CryptoM τ (Except DecryptError α) := do
  try
    let bytes ←
      openDetached τ
        ciphertext.bytes
        ciphertext.mac.bytes
        ciphertext.nonce.bytes
        theirPublicKey.bytes
        keyPair.secret.bytes
    let some msg := String.fromUTF8? bytes | return .error (.invalidEncoding bytes)
    let .ok json := Json.parse msg | return .error (.invalidString msg)
    let .ok a := fromJson? json | return .error (.invalidJson json)
    return .ok a
  catch _ => return .error .refused

/-- Encrypt message with separate ciphertext and MAC using precomputed shared secret.

    **Performance**: More efficient than `encryptDetached` for multiple messages. -/
def encryptDetachedWithShared [ToJson α] (sharedSecret : BoxSharedSecret τ)
    (message : α) : CryptoM τ (DetachedCipherText BoxSpec) := do
  let nonce ← mkFreshNonceId BoxSpec
  let data := toJson message |>.compress.toUTF8
  let (cipher, mac) ← detachedAfternm τ data nonce.bytes sharedSecret.bytes
  if h : mac.size = BoxSpec.macBytes then
    return {bytes := cipher, mac := ⟨mac, h⟩, nonce}
  else throwInvariantFailure

/-- Decrypt message with separate ciphertext and MAC using precomputed shared secret.

    **Performance**: More efficient than `decryptDetached` when shared secret is precomputed. -/
def decryptDetachedWithShared [FromJson α] (sharedSecret : BoxSharedSecret τ)
    (ciphertext : DetachedCipherText BoxSpec) : CryptoM τ (Except DecryptError α) := do
  try
    let bytes ←
      openDetachedAfternm τ
        ciphertext.bytes
        ciphertext.mac.bytes
        ciphertext.nonce.bytes
        sharedSecret.bytes
    let some msg := String.fromUTF8? bytes | return .error (.invalidEncoding bytes)
    let .ok json := Json.parse msg | return .error (.invalidString msg)
    let .ok a := fromJson? json | return .error (.invalidJson json)
    return .ok a
  catch _ => return .error .refused

-- ================================
-- Sealed Box Operations (Anonymous)
-- ================================

/-- Anonymous encryption to a public key (no sender authentication).

    **Security**: Recipient cannot verify sender identity - use for anonymous communication.
    **No nonce needed**: Uses ephemeral keypair internally for perfect forward secrecy. -/
def sealTo [ToJson α] (theirPublicKey : BoxPublicKey) (message : α) : CryptoM τ (SealedCipherText BoxSpec) := do
  let data := toJson message |>.compress.toUTF8
  let sealed ← «seal» τ data theirPublicKey.bytes
  if h : sealed.size ≥ BoxSpec.sealBytes then
    return ⟨sealed, h⟩
  else throwInvariantFailure

/-- Decrypt sealed box using recipient's keypair.

    **Security**: Authenticates message integrity but not sender identity. -/
def openSealed [FromJson α] (keyPair : BoxKeyPair τ) (sealed : SealedCipherText BoxSpec) : CryptoM τ (Except DecryptError α) := do
  try
    let bytes ← sealOpen τ sealed.bytes keyPair.public.bytes keyPair.secret.bytes
    let some msg := String.fromUTF8? bytes | return .error (.invalidEncoding bytes)
    let .ok json := Json.parse msg | return .error (.invalidString msg)
    let .ok a := fromJson? json | return .error (.invalidJson json)
    return .ok a
  catch _ => return .error .refused

end Sodium.Crypto.Box
