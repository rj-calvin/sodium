import Sodium.FFI.KeyDeriv
import Sodium.FFI.SecretBox
import Sodium.Crypto.Monad

open Lean

/-!
# SecretBox Authenticated Encryption

This module provides type-safe wrappers around LibSodium's SecretBox authenticated encryption.

SecretBox uses:
- **XSalsa20** for encryption
- **Poly1305** for authentication

## Usage Patterns

**Basic encryption/decryption with symmetric key:**
```lean
let secretKey ← mkFreshKey
let ciphertext ← encrypt secretKey message  -- nonce embedded in result
let .ok plaintext ← decrypt secretKey ciphertext | throw "decryption failed"
```

**Detached operations (separate MAC):**
```lean
let detachedCipher ← encryptDetached secretKey message  -- nonce + MAC embedded
let .ok plaintext ← decryptDetached secretKey detachedCipher | throw "decryption failed"
```

## Security Considerations

- **Nonce uniqueness**: Never reuse nonces with the same secret key
- **Key generation**: Use `mkFreshKey` for random keys
- **Key storage**: Secret keys are automatically stored in secure memory with proper protection
- **Perfect secrecy**: Single secret key provides both confidentiality and authenticity
- **Performance**: Faster than Box (no elliptic curve operations) when key exchange is already done

## When to Use SecretBox vs Box

- **Use SecretBox**: When you already have a shared secret key (pre-shared key, derived from key exchange, etc.)
- **Use Box**: When you need to establish secure communication without pre-shared secrets (public key crypto)
-/

namespace Sodium.Crypto.SecretBox

open FFI SecretBox

-- ================================
-- Specification and Type Aliases
-- ================================

def SecretBoxSpec : Spec where
  name := `xsalsa20poly1305
  secretKeyBytes := KEYBYTES
  nonceBytes := NONCEBYTES
  macBytes := MACBYTES

variable {α σ : Type} (τ : Sodium σ)

/-- Convenient aliases for SecretBox operations -/
abbrev SecretBoxKey := SecretKey τ SecretBoxSpec
abbrev SecretBoxNonce := NonceId SecretBoxSpec
abbrev SecretBoxCipherText := CipherText SecretBoxSpec
abbrev SecretBoxSeed := Seed τ SecretBoxSpec

variable {τ}

-- ================================
-- Key Generation
-- ================================

/-- Generate a fresh SecretBox key with compile-time size validation -/
def mkFreshKey : CryptoM τ (SecretBoxKey τ) := do
  let key ← keygen τ
  if h : key.size = SecretBoxSpec.secretKeyBytes then
    return ⟨key, h⟩
  else throwInvariantFailure

def mkSubKey : CryptoM τ (SecretBoxKey τ) := do
  let st ← get
  let idx := st.ctx.index
  let key ← KeyDeriv.derive τ SecretBoxSpec.secretKeyBytes idx.1 idx.2 st.mkey.bytes
  if h : key.size = SecretBoxSpec.secretKeyBytes then
    return ⟨key, h⟩
  else throwInvariantFailure

-- ================================
-- Authenticated Encryption (Easy API)
-- ================================

/-- Encrypt message using SecretBox with secret key.

    **Security**: Fresh nonce is automatically generated to prevent reuse. -/
def encrypt [ToJson α] (secretKey : SecretBoxKey τ) (message : α) : CryptoM τ SecretBoxCipherText := do
  let nonce ← mkFreshNonceId SecretBoxSpec
  let data := toJson message |>.compress.toUTF8
  let cipher ← easy τ data nonce.bytes secretKey.bytes
  if h : cipher.size ≥ SecretBoxSpec.macBytes then
    return ⟨cipher, nonce, h⟩
  else throwInvariantFailure

/-- Decrypt message using SecretBox with secret key.

    **Security**: Uses embedded nonce from ciphertext for decryption. -/
def decrypt [FromJson α] (secretKey : SecretBoxKey τ)
    (ciphertext : SecretBoxCipherText) : CryptoM τ (Except DecryptError α) := do
  try
    let bytes ←
      openEasy τ
        ciphertext.bytes
        ciphertext.nonce.bytes
        secretKey.bytes
    let some msg := String.fromUTF8? bytes | return .error (.invalidEncoding bytes)
    let .ok json := Json.parse msg | return .error (.invalidString msg)
    let .ok a := fromJson? json | return .error (.invalidJson json)
    return .ok a
  catch _ => return .error .refused

-- ================================
-- Detached Operations (Separate MAC)
-- ================================

/-- Encrypt message with separate ciphertext and MAC using secret key.

    **Use case**: When MAC needs to be stored or transmitted separately from ciphertext. -/
def encryptDetached [ToJson α] (secretKey : SecretBoxKey τ)
    (message : α) : CryptoM τ (DetachedCipherText SecretBoxSpec) := do
  let nonce ← mkFreshNonceId SecretBoxSpec
  let data := toJson message |>.compress.toUTF8
  let (cipher, mac) ← detached τ data nonce.bytes secretKey.bytes
  if h : mac.size = SecretBoxSpec.macBytes then
    return {bytes := cipher, mac := ⟨mac, h⟩, nonce}
  else throwInvariantFailure

/-- Decrypt message with separate ciphertext and MAC using secret key.

    **Security**: Uses embedded nonce and MAC from detached ciphertext. -/
def decryptDetached [FromJson α] (secretKey : SecretBoxKey τ)
    (ciphertext : DetachedCipherText SecretBoxSpec) : CryptoM τ (Except DecryptError α) := do
  try
    let bytes ←
      openDetached τ
        ciphertext.bytes
        ciphertext.mac.bytes
        ciphertext.nonce.bytes
        secretKey.bytes
    let some msg := String.fromUTF8? bytes | return .error (.invalidEncoding bytes)
    let .ok json := Json.parse msg | return .error (.invalidString msg)
    let .ok a := fromJson? json | return .error (.invalidJson json)
    return .ok a
  catch _ => return .error .refused

end Sodium.Crypto.SecretBox
