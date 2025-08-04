/-
Refined types for cryptographic primitives with compile-time safety guarantees.

This module provides type-safe wrappers around raw cryptographic data structures,
using dependent types to enforce size constraints and prevent misuse at compile time.
-/
import Lean.Server.Rpc.Basic
import «Sodium».FFI.SecretBox
import «Sodium».FFI.Box
import «Sodium».FFI.Sign
import «Sodium».FFI.Auth
import «Sodium».FFI.Stream
import «Sodium».FFI.Aead
import «Sodium».FFI.KeyDeriv
import «Sodium».FFI.KeyExch
import «Sodium».FFI.ShortHash
import «Sodium».FFI.GenericHash
import «Sodium».FFI.PwHash
import «Sodium».FFI.SecretStream

open Lean

universe u

namespace Sodium.Crypto

/-- Algorithm specifications with size constants for all LibSodium cryptographic primitives.

This structure provides compile-time size information for all fields used across
different cryptographic algorithms, enabling type-safe wrappers with size validation. -/
structure AlgorithmSpec where
  /-- Algorithm name for identification -/
  name : Name
  /-- Secret key size in bytes -/
  secretKeyBytes : Nat
  /-- Public key size in bytes -/
  publicKeyBytes : Nat
  /-- Nonce size in bytes -/
  nonceBytes : Nat
  /-- MAC size in bytes -/
  macBytes : Nat
  /-- Seed size in bytes for deterministic key generation -/
  seedBytes : Nat
  /-- Precomputed shared secret size for Box operations -/
  beforeNmBytes : Nat
  /-- Sealed box overhead size in bytes -/
  sealBytes : Nat
  /-- Hash output size in bytes for generic hashing -/
  hashBytes : Nat
  /-- Authentication tag size in bytes for AEAD operations -/
  tagBytes : Nat
  /-- Context size in bytes for key derivation -/
  contextBytes : Nat
  /-- Session key size in bytes for key exchange protocols -/
  sessionKeyBytes : Nat
  /-- Salt size in bytes for password hashing -/
  saltBytes : Nat
  /-- Header size in bytes for secret stream operations -/
  headerBytes : Nat
  /-- State size in bytes for streaming operations (currently not in use) -/
  stateBytes : Nat
  deriving BEq, Hashable, Inhabited, ToJson, FromJson

instance : Coe AlgorithmSpec Name := ⟨AlgorithmSpec.name⟩

def NameGeneratorSpec : AlgorithmSpec := {
  name := .mkSimple "nonce"
  nonceBytes := 24
  publicKeyBytes := 0
  secretKeyBytes := 0
  macBytes := 0
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := 0
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

def SecretBoxSpec : AlgorithmSpec := {
  name := .mkSimple "XSalsa20Poly1305"
  secretKeyBytes := FFI.SECRETBOX_KEYBYTES.toNat
  publicKeyBytes := 0  -- N/A for symmetric crypto
  nonceBytes := FFI.SECRETBOX_NONCEBYTES.toNat
  macBytes := FFI.SECRETBOX_MACBYTES.toNat
  seedBytes := FFI.SECRETBOX_KEYBYTES.toNat
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := FFI.SECRETBOX_MACBYTES.toNat
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

def BoxSpec : AlgorithmSpec := {
  name := .mkSimple "Curve25519XSalsa20Poly1305"
  secretKeyBytes := FFI.BOX_SECRETKEYBYTES.toNat
  publicKeyBytes := FFI.BOX_PUBLICKEYBYTES.toNat
  nonceBytes := FFI.BOX_NONCEBYTES.toNat
  macBytes := FFI.BOX_MACBYTES.toNat
  seedBytes := FFI.BOX_SEEDBYTES.toNat
  beforeNmBytes := FFI.BOX_BEFORENMBYTES.toNat
  sealBytes := FFI.BOX_SEALBYTES.toNat
  hashBytes := 0
  tagBytes := FFI.BOX_MACBYTES.toNat
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

def SignSpec : AlgorithmSpec := {
  name := .mkSimple "Ed25519"
  secretKeyBytes := FFI.SIGN_SECRETKEYBYTES.toNat
  publicKeyBytes := FFI.SIGN_PUBLICKEYBYTES.toNat
  nonceBytes := 0     -- N/A for signatures
  macBytes := FFI.SIGN_BYTES.toNat      -- Signature size
  seedBytes := FFI.SIGN_SEEDBYTES.toNat
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := FFI.SIGN_BYTES.toNat
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

/- Authentication Algorithm Specs -/

def AuthSpec : AlgorithmSpec := {
  name := .mkSimple "HMACSHA512256"
  secretKeyBytes := FFI.AUTH_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := 0
  macBytes := FFI.AUTH_BYTES.toNat
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := FFI.AUTH_BYTES.toNat
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

def HmacSha256Spec : AlgorithmSpec := {
  name := .mkSimple "HMACSHA256"
  secretKeyBytes := FFI.HMAC_SHA256_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := 0
  macBytes := FFI.HMAC_SHA256_BYTES.toNat
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := FFI.HMAC_SHA256_BYTES.toNat
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

def HmacSha512Spec : AlgorithmSpec := {
  name := .mkSimple "HMACSHA512"
  secretKeyBytes := FFI.HMAC_SHA512_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := 0
  macBytes := FFI.HMAC_SHA512_BYTES.toNat
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := FFI.HMAC_SHA512_BYTES.toNat
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

/- Key Exchange Algorithm Spec -/

def KeyExchangeSpec : AlgorithmSpec := {
  name := .mkSimple "X25519"
  secretKeyBytes := FFI.KX_SECRETKEYBYTES.toNat
  publicKeyBytes := FFI.KX_PUBLICKEYBYTES.toNat
  nonceBytes := 0
  macBytes := 0
  seedBytes := FFI.KX_SEEDBYTES.toNat
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := 0
  contextBytes := 0
  sessionKeyBytes := FFI.KX_SESSIONKEYBYTES.toNat
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

/- Key Derivation Algorithm Spec -/

def KeyDerivationSpec : AlgorithmSpec := {
  name := .mkSimple "BLAKE2bKDF"
  secretKeyBytes := FFI.KDF_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := 0
  macBytes := 0
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := 0
  contextBytes := FFI.KDF_CONTEXTBYTES.toNat
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

/- Short Hash Algorithm Spec -/

def ShortHashSpec : AlgorithmSpec := {
  name := .mkSimple "SipHash24"
  secretKeyBytes := FFI.SHORTHASH_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := 0
  macBytes := 0
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := FFI.SHORTHASH_BYTES.toNat
  tagBytes := 0
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

/- Generic Hash Algorithm Spec -/

def GenericHashSpec : AlgorithmSpec := {
  name := .mkSimple "BLAKE2b"
  secretKeyBytes := FFI.GENERICHASH_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := 0
  macBytes := 0
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := FFI.GENERICHASH_BYTES.toNat
  tagBytes := 0
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

/- AEAD Algorithm Specs -/

def ChaCha20Poly1305IetfSpec : AlgorithmSpec := {
  name := .mkSimple "ChaCha20Poly1305IETF"
  secretKeyBytes := FFI.CHACHA20POLY1305_IETF_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := FFI.CHACHA20POLY1305_IETF_NONCEBYTES.toNat
  macBytes := 0
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := FFI.CHACHA20POLY1305_IETF_TAGBYTES.toNat
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

def ChaCha20Poly1305Spec : AlgorithmSpec := {
  name := .mkSimple "ChaCha20Poly1305"
  secretKeyBytes := FFI.CHACHA20POLY1305_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := FFI.CHACHA20POLY1305_NONCEBYTES.toNat
  macBytes := 0
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := FFI.CHACHA20POLY1305_TAGBYTES.toNat
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

def XChaCha20Poly1305IetfSpec : AlgorithmSpec := {
  name := .mkSimple "XChaCha20Poly1305IETF"
  secretKeyBytes := FFI.XCHACHA20POLY1305_IETF_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := FFI.XCHACHA20POLY1305_IETF_NONCEBYTES.toNat
  macBytes := 0
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := FFI.XCHACHA20POLY1305_IETF_TAGBYTES.toNat
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

def Aes256GcmSpec : AlgorithmSpec := {
  name := .mkSimple "AES256GCM"
  secretKeyBytes := FFI.AES256GCM_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := FFI.AES256GCM_NONCEBYTES.toNat
  macBytes := 0
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := FFI.AES256GCM_TAGBYTES.toNat
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

def Aegis128LSpec : AlgorithmSpec := {
  name := .mkSimple "AEGIS128L"
  secretKeyBytes := FFI.AEGIS128L_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := FFI.AEGIS128L_NONCEBYTES.toNat
  macBytes := 0
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := FFI.AEGIS128L_TAGBYTES.toNat
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

def Aegis256Spec : AlgorithmSpec := {
  name := .mkSimple "AEGIS256"
  secretKeyBytes := FFI.AEGIS256_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := FFI.AEGIS256_NONCEBYTES.toNat
  macBytes := 0
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := FFI.AEGIS256_TAGBYTES.toNat
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

/- Stream Cipher Algorithm Specs -/

def StreamSpec : AlgorithmSpec := {
  name := .mkSimple "XSalsa20"
  secretKeyBytes := FFI.STREAM_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := FFI.STREAM_NONCEBYTES.toNat
  macBytes := 0
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := 0
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

def ChaCha20StreamSpec : AlgorithmSpec := {
  name := .mkSimple "ChaCha20"
  secretKeyBytes := FFI.CHACHA20_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := FFI.CHACHA20_NONCEBYTES.toNat
  macBytes := 0
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := 0
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

def ChaCha20IetfStreamSpec : AlgorithmSpec := {
  name := .mkSimple "ChaCha20IETF"
  secretKeyBytes := FFI.CHACHA20_IETF_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := FFI.CHACHA20_IETF_NONCEBYTES.toNat
  macBytes := 0
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := 0
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := 0
  stateBytes := 0
}

/- Password Hashing Algorithm Spec -/

def PwHashSpec : AlgorithmSpec := {
  name := .mkSimple "Argon2id"
  secretKeyBytes := 0  -- Variable length output
  publicKeyBytes := 0
  nonceBytes := 0
  macBytes := 0
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0  -- Variable length output
  tagBytes := 0
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := FFI.PWHASH_SALTBYTES.toNat
  headerBytes := 0
  stateBytes := 0  -- No streaming state for pwhash
}

/- Secret Stream Algorithm Spec -/

def SecretStreamSpec : AlgorithmSpec := {
  name := .mkSimple "XChaCha20Poly1305SecretStream"
  secretKeyBytes := FFI.SECRETSTREAM_XCHACHA20POLY1305_KEYBYTES.toNat
  publicKeyBytes := 0
  nonceBytes := 0
  macBytes := FFI.SECRETSTREAM_XCHACHA20POLY1305_ABYTES.toNat
  seedBytes := 0
  beforeNmBytes := 0
  sealBytes := 0
  hashBytes := 0
  tagBytes := FFI.SECRETSTREAM_XCHACHA20POLY1305_ABYTES.toNat
  contextBytes := 0
  sessionKeyBytes := 0
  saltBytes := 0
  headerBytes := FFI.SECRETSTREAM_XCHACHA20POLY1305_HEADERBYTES.toNat
  stateBytes := 0  -- TODO: Add STATEBYTES constant when needed
}

/-- Refined secret key type with size validation -/
structure SecretKey (spec : AlgorithmSpec) where
  bytes : ByteArray
  size_valid : bytes.size = spec.secretKeyBytes := by omega

/-- Refined public key type -/
structure PublicKey (spec : AlgorithmSpec) where
  bytes : ByteArray
  size_valid : bytes.size = spec.publicKeyBytes

/-- Key pair type for asymmetric algorithms -/
structure KeyPair (spec : AlgorithmSpec) where
  public : PublicKey spec
  secret : SecretKey spec

/-- Refined nonce type for uniqueness tracking -/
structure NonceId (spec : AlgorithmSpec) where
  bytes : ByteArray
  size_valid : bytes.size = spec.nonceBytes := by omega

/-- Refined signature type -/
structure Signature (spec : AlgorithmSpec) where
  bytes : ByteArray
  size_valid : bytes.size = spec.macBytes := by omega

/-- Refined seed type for deterministic key generation -/
structure Seed (spec : AlgorithmSpec) where
  bytes : ByteArray
  size_valid : bytes.size = spec.seedBytes := by omega

/-- Authenticated ciphertext that includes MAC -/
structure CipherText (spec : AlgorithmSpec) where
  bytes : ByteArray
  has_mac : bytes.size >= spec.macBytes := by omega

/-- MAC/authentication tag for detached operations -/
structure Mac (spec : AlgorithmSpec) where
  bytes : ByteArray
  size_valid : bytes.size = spec.macBytes := by omega

/-- Ciphertext without embedded MAC (for detached operations) -/
structure DetachedCipherText (spec : AlgorithmSpec) where
  bytes : ByteArray

/-- Sealed box ciphertext (includes ephemeral public key + MAC) -/
structure SealedCipherText (spec : AlgorithmSpec) where
  bytes : ByteArray
  has_seal : bytes.size >= spec.sealBytes := by omega

/-- Hash output for generic hashing operations -/
structure HashOutput (spec : AlgorithmSpec) where
  bytes : ByteArray
  size_valid : bytes.size = spec.hashBytes := by omega

/-- Authentication tag for AEAD operations -/
structure AuthTag (spec : AlgorithmSpec) where
  bytes : ByteArray
  size_valid : bytes.size = spec.tagBytes := by omega

/-- Context data for key derivation -/
structure Context (spec : AlgorithmSpec) where
  bytes : ByteArray
  size_valid : bytes.size = spec.contextBytes := by omega

/-- Session key for key exchange protocols -/
structure SessionKey (spec : AlgorithmSpec) where
  bytes : ByteArray
  size_valid : bytes.size = spec.sessionKeyBytes := by omega

/-- Salt for password hashing -/
structure Salt (spec : AlgorithmSpec) where
  bytes : ByteArray
  size_valid : bytes.size = spec.saltBytes := by omega

/-- Header for secret stream operations -/
structure StreamHeader (spec : AlgorithmSpec) where
  bytes : ByteArray
  size_valid : bytes.size = spec.headerBytes := by omega

/-- Opaque state for streaming operations (variable size, so no size constraint) -/
structure StreamState (spec : AlgorithmSpec) where
  bytes : ByteArray
  -- Note: stateBytes field exists but streaming states are often opaque/variable
  -- so we don't enforce a size constraint here

variable {spec : AlgorithmSpec}

/-- Extract the plaintext length (total - MAC size) -/
def plaintextLength (ct : CipherText spec) : Nat :=
  ct.bytes.size - spec.macBytes

instance : CoeOut (SecretKey spec) ByteArray := ⟨SecretKey.bytes⟩
instance : CoeOut (PublicKey spec) ByteArray := ⟨PublicKey.bytes⟩
instance : CoeOut (NonceId spec) ByteArray := ⟨NonceId.bytes⟩
instance : CoeOut (Signature spec) ByteArray := ⟨Signature.bytes⟩
instance : CoeOut (Seed spec) ByteArray := ⟨Seed.bytes⟩
instance : CoeOut (CipherText spec) ByteArray := ⟨CipherText.bytes⟩
instance : CoeOut (Mac spec) ByteArray := ⟨Mac.bytes⟩
instance : CoeOut (DetachedCipherText spec) ByteArray := ⟨DetachedCipherText.bytes⟩
instance : CoeOut (SealedCipherText spec) ByteArray := ⟨SealedCipherText.bytes⟩
instance : CoeOut (HashOutput spec) ByteArray := ⟨HashOutput.bytes⟩
instance : CoeOut (AuthTag spec) ByteArray := ⟨AuthTag.bytes⟩
instance : CoeOut (Context spec) ByteArray := ⟨Context.bytes⟩
instance : CoeOut (SessionKey spec) ByteArray := ⟨SessionKey.bytes⟩
instance : CoeOut (Salt spec) ByteArray := ⟨Salt.bytes⟩
instance : CoeOut (StreamHeader spec) ByteArray := ⟨StreamHeader.bytes⟩
instance : CoeOut (StreamState spec) ByteArray := ⟨StreamState.bytes⟩

abbrev NonceNameGenerator := NonceId NameGeneratorSpec

abbrev SecretBoxKey := SecretKey SecretBoxSpec
abbrev SecretBoxNonce := NonceId SecretBoxSpec
abbrev SecretBoxCipherText := CipherText SecretBoxSpec
abbrev SecretBoxMac := Mac SecretBoxSpec
abbrev SecretBoxDetachedCipherText := DetachedCipherText SecretBoxSpec

abbrev BoxPublicKey := PublicKey BoxSpec
abbrev BoxSecretKey := SecretKey BoxSpec
abbrev BoxNonce := NonceId BoxSpec
abbrev BoxKeyPair := KeyPair BoxSpec
abbrev BoxCipherText := CipherText BoxSpec
abbrev BoxMac := Mac BoxSpec
abbrev BoxDetachedCipherText := DetachedCipherText BoxSpec

abbrev BoxSealedCipherText := SealedCipherText BoxSpec

abbrev SignPublicKey := PublicKey SignSpec
abbrev SignSecretKey := SecretKey SignSpec
abbrev SignKeyPair := KeyPair SignSpec
abbrev Ed25519Signature := Signature SignSpec

/- Type aliases for Auth algorithms -/
abbrev AuthSecretKey := SecretKey AuthSpec
abbrev AuthMac := Mac AuthSpec

abbrev HmacSha256SecretKey := SecretKey HmacSha256Spec
abbrev HmacSha256Mac := Mac HmacSha256Spec

abbrev HmacSha512SecretKey := SecretKey HmacSha512Spec
abbrev HmacSha512Mac := Mac HmacSha512Spec

/- Type aliases for Key Exchange -/
abbrev KeyExchangePublicKey := PublicKey KeyExchangeSpec
abbrev KeyExchangeSecretKey := SecretKey KeyExchangeSpec
abbrev KeyExchangeKeyPair := KeyPair KeyExchangeSpec
abbrev KeyExchangeSeed := Seed KeyExchangeSpec
abbrev KeyExchangeSessionKey := SessionKey KeyExchangeSpec

/- Type aliases for Key Derivation -/
abbrev KeyDerivationSecretKey := SecretKey KeyDerivationSpec
abbrev KeyDerivationContext := Context KeyDerivationSpec

/- Type aliases for Short Hash -/
abbrev ShortHashSecretKey := SecretKey ShortHashSpec
abbrev ShortHashOutput := HashOutput ShortHashSpec

/- Type aliases for Generic Hash -/
abbrev GenericHashSecretKey := SecretKey GenericHashSpec
abbrev GenericHashOutput := HashOutput GenericHashSpec

/- Type aliases for AEAD algorithms -/
abbrev ChaCha20Poly1305IetfSecretKey := SecretKey ChaCha20Poly1305IetfSpec
abbrev ChaCha20Poly1305IetfNonce := NonceId ChaCha20Poly1305IetfSpec
abbrev ChaCha20Poly1305IetfAuthTag := AuthTag ChaCha20Poly1305IetfSpec

abbrev ChaCha20Poly1305SecretKey := SecretKey ChaCha20Poly1305Spec
abbrev ChaCha20Poly1305Nonce := NonceId ChaCha20Poly1305Spec
abbrev ChaCha20Poly1305AuthTag := AuthTag ChaCha20Poly1305Spec

abbrev XChaCha20Poly1305IetfSecretKey := SecretKey XChaCha20Poly1305IetfSpec
abbrev XChaCha20Poly1305IetfNonce := NonceId XChaCha20Poly1305IetfSpec
abbrev XChaCha20Poly1305IetfAuthTag := AuthTag XChaCha20Poly1305IetfSpec

abbrev Aes256GcmSecretKey := SecretKey Aes256GcmSpec
abbrev Aes256GcmNonce := NonceId Aes256GcmSpec
abbrev Aes256GcmAuthTag := AuthTag Aes256GcmSpec

abbrev Aegis128LSecretKey := SecretKey Aegis128LSpec
abbrev Aegis128LNonce := NonceId Aegis128LSpec
abbrev Aegis128LAuthTag := AuthTag Aegis128LSpec

abbrev Aegis256SecretKey := SecretKey Aegis256Spec
abbrev Aegis256Nonce := NonceId Aegis256Spec
abbrev Aegis256AuthTag := AuthTag Aegis256Spec

/- Type aliases for Stream Ciphers -/
abbrev StreamSecretKey := SecretKey StreamSpec
abbrev StreamNonce := NonceId StreamSpec

abbrev ChaCha20StreamSecretKey := SecretKey ChaCha20StreamSpec
abbrev ChaCha20StreamNonce := NonceId ChaCha20StreamSpec

abbrev ChaCha20IetfStreamSecretKey := SecretKey ChaCha20IetfStreamSpec
abbrev ChaCha20IetfStreamNonce := NonceId ChaCha20IetfStreamSpec

/- Type aliases for Password Hashing -/
-- Note: PwHash uses variable-length outputs, so no fixed-size key types
abbrev PwHashSalt := Salt PwHashSpec

/- Type aliases for Secret Stream -/
abbrev SecretStreamSecretKey := SecretKey SecretStreamSpec
abbrev SecretStreamMac := Mac SecretStreamSpec
abbrev SecretStreamAuthTag := AuthTag SecretStreamSpec
abbrev SecretStreamHeader := StreamHeader SecretStreamSpec

end Sodium.Crypto
