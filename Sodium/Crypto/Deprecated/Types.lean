/-
Refined types for cryptographic primitives with compile-time safety guarantees.

This module provides type-safe wrappers around raw cryptographic data structures,
using dependent types to enforce size constraints and prevent misuse at compile time.
-/
import Lean.Server.Rpc.Basic
import «Sodium».FFI.Deprecated.SecretBox
import «Sodium».FFI.Deprecated.Box
import «Sodium».FFI.Deprecated.Sign
import «Sodium».FFI.Deprecated.Auth
import «Sodium».FFI.Deprecated.Stream
import «Sodium».FFI.Deprecated.Aead
import «Sodium».FFI.Deprecated.KeyDeriv
import «Sodium».FFI.Deprecated.KeyExch
import «Sodium».FFI.Deprecated.ShortHash
import «Sodium».FFI.Deprecated.GenericHash
import «Sodium».FFI.Deprecated.PwHash
import «Sodium».FFI.Deprecated.SecretStream

open Lean

universe u

namespace Sodium.Crypto

private instance : Ord Name := ⟨Name.quickCmp⟩

/-- Algorithm specifications with size constants for all LibSodium cryptographic primitives.

This structure provides compile-time size information for all fields used across
different cryptographic algorithms, enabling type-safe wrappers with size validation. -/
structure AlgorithmSpec where
  /-- Algorithm name for identification -/
  name : Name
  /-- Secret key size in bytes -/
  secretKeyBytes : Nat := 0
  /-- Public key size in bytes -/
  publicKeyBytes : Nat := 0
  /-- Nonce size in bytes -/
  nonceBytes : Nat := 0
  /-- MAC size in bytes -/
  macBytes : Nat := 0
  /-- Seed size in bytes for deterministic key generation -/
  seedBytes : Nat := 0
  /-- Precomputed shared secret size for Box operations -/
  beforeNmBytes : Nat := 0
  /-- Sealed box overhead size in bytes -/
  sealBytes : Nat := 0
  /-- Hash output size in bytes for generic hashing -/
  hashBytes : Nat := 0
  /-- Authentication tag size in bytes for AEAD operations -/
  tagBytes : Nat := 0
  /-- Context size in bytes for key derivation -/
  contextBytes : Nat := 0
  /-- Session key size in bytes for key exchange protocols -/
  sessionKeyBytes : Nat := 0
  /-- Salt size in bytes for password hashing -/
  saltBytes : Nat := 0
  /-- Header size in bytes for secret stream operations -/
  headerBytes : Nat := 0
  /-- Maximum message size in bytes for streaming operations -/
  messageMaxBytes : Nat := 0
  /-- State size in bytes for streaming operations (currently not in use) -/
  stateBytes : Nat := 0
  deriving BEq, Ord, TypeName, Hashable, Inhabited, ToJson, FromJson

instance : Coe AlgorithmSpec Name := ⟨AlgorithmSpec.name⟩

def NameGeneratorSpec : AlgorithmSpec where
  name := .mkSimple "nonce"
  /-
    Generic nonces should support `ByteArray.toUInt64LE!` and `ByteArray.toUInt64BE!`, though
    `ByteArray.compact!` should also suffice (despite producing a different result).

    This choice also has the added benefit of preventing mixups between nonces used generically
    and those used by more secure algorithms.
  -/
  nonceBytes := 8

def SecretBoxSpec : AlgorithmSpec where
  name := .mkSimple "XSalsa20Poly1305"
  secretKeyBytes := FFI.SECRETBOX_KEYBYTES.toNat
  nonceBytes := FFI.SECRETBOX_NONCEBYTES.toNat
  macBytes := FFI.SECRETBOX_MACBYTES.toNat
  seedBytes := FFI.SECRETBOX_KEYBYTES.toNat
  tagBytes := FFI.SECRETBOX_MACBYTES.toNat

def BoxSpec : AlgorithmSpec where
  name := .mkSimple "Curve25519XSalsa20Poly1305"
  secretKeyBytes := FFI.BOX_SECRETKEYBYTES.toNat
  publicKeyBytes := FFI.BOX_PUBLICKEYBYTES.toNat
  nonceBytes := FFI.BOX_NONCEBYTES.toNat
  macBytes := FFI.BOX_MACBYTES.toNat
  seedBytes := FFI.BOX_SEEDBYTES.toNat
  beforeNmBytes := FFI.BOX_BEFORENMBYTES.toNat
  sealBytes := FFI.BOX_SEALBYTES.toNat
  tagBytes := FFI.BOX_MACBYTES.toNat

def SignSpec : AlgorithmSpec where
  name := .mkSimple "Ed25519"
  secretKeyBytes := FFI.SIGN_SECRETKEYBYTES.toNat
  publicKeyBytes := FFI.SIGN_PUBLICKEYBYTES.toNat
  macBytes := FFI.SIGN_BYTES.toNat
  seedBytes := FFI.SIGN_SEEDBYTES.toNat
  tagBytes := FFI.SIGN_BYTES.toNat

/- Authentication Algorithm Specs -/

def AuthSpec : AlgorithmSpec where
  name := .mkSimple "HMACSHA512256"
  secretKeyBytes := FFI.AUTH_KEYBYTES.toNat
  macBytes := FFI.AUTH_BYTES.toNat
  tagBytes := FFI.AUTH_BYTES.toNat

def HmacSha256Spec : AlgorithmSpec where
  name := .mkSimple "HMACSHA256"
  secretKeyBytes := FFI.HMAC_SHA256_KEYBYTES.toNat
  macBytes := FFI.HMAC_SHA256_BYTES.toNat
  tagBytes := FFI.HMAC_SHA256_BYTES.toNat

def HmacSha512Spec : AlgorithmSpec where
  name := .mkSimple "HMACSHA512"
  secretKeyBytes := FFI.HMAC_SHA512_KEYBYTES.toNat
  macBytes := FFI.HMAC_SHA512_BYTES.toNat
  tagBytes := FFI.HMAC_SHA512_BYTES.toNat

/- Key Exchange Algorithm Spec -/

def KeyExchangeSpec : AlgorithmSpec where
  name := .mkSimple "X25519"
  secretKeyBytes := FFI.KX_SECRETKEYBYTES.toNat
  publicKeyBytes := FFI.KX_PUBLICKEYBYTES.toNat
  seedBytes := FFI.KX_SEEDBYTES.toNat
  sessionKeyBytes := FFI.KX_SESSIONKEYBYTES.toNat

/- Key Derivation Algorithm Spec -/

def KeyDerivationSpec : AlgorithmSpec where
  name := .mkSimple "BLAKE2bKDF"
  secretKeyBytes := FFI.KDF_KEYBYTES.toNat
  contextBytes := FFI.KDF_CONTEXTBYTES.toNat

/- Short Hash Algorithm Spec -/

def ShortHashSpec : AlgorithmSpec where
  name := .mkSimple "SipHash24"
  secretKeyBytes := FFI.SHORTHASH_KEYBYTES.toNat
  hashBytes := FFI.SHORTHASH_BYTES.toNat

/- Generic Hash Algorithm Spec -/

def GenericHashSpec : AlgorithmSpec where
  name := .mkSimple "BLAKE2b"
  secretKeyBytes := FFI.GENERICHASH_KEYBYTES.toNat
  hashBytes := FFI.GENERICHASH_BYTES.toNat

/- AEAD Algorithm Specs -/

def ChaCha20Poly1305IetfSpec : AlgorithmSpec where
  name := .mkSimple "ChaCha20Poly1305IETF"
  secretKeyBytes := FFI.CHACHA20POLY1305_IETF_KEYBYTES.toNat
  nonceBytes := FFI.CHACHA20POLY1305_IETF_NONCEBYTES.toNat
  tagBytes := FFI.CHACHA20POLY1305_IETF_TAGBYTES.toNat

def ChaCha20Poly1305Spec : AlgorithmSpec where
  name := .mkSimple "ChaCha20Poly1305"
  secretKeyBytes := FFI.CHACHA20POLY1305_KEYBYTES.toNat
  nonceBytes := FFI.CHACHA20POLY1305_NONCEBYTES.toNat
  tagBytes := FFI.CHACHA20POLY1305_TAGBYTES.toNat

def XChaCha20Poly1305IetfSpec : AlgorithmSpec where
  name := .mkSimple "XChaCha20Poly1305IETF"
  secretKeyBytes := FFI.XCHACHA20POLY1305_IETF_KEYBYTES.toNat
  nonceBytes := FFI.XCHACHA20POLY1305_IETF_NONCEBYTES.toNat
  tagBytes := FFI.XCHACHA20POLY1305_IETF_TAGBYTES.toNat

def Aes256GcmSpec : AlgorithmSpec where
  name := .mkSimple "AES256GCM"
  secretKeyBytes := FFI.AES256GCM_KEYBYTES.toNat
  nonceBytes := FFI.AES256GCM_NONCEBYTES.toNat
  tagBytes := FFI.AES256GCM_TAGBYTES.toNat

def Aegis128LSpec : AlgorithmSpec where
  name := .mkSimple "AEGIS128L"
  secretKeyBytes := FFI.AEGIS128L_KEYBYTES.toNat
  nonceBytes := FFI.AEGIS128L_NONCEBYTES.toNat
  tagBytes := FFI.AEGIS128L_TAGBYTES.toNat

def Aegis256Spec : AlgorithmSpec where
  name := .mkSimple "AEGIS256"
  secretKeyBytes := FFI.AEGIS256_KEYBYTES.toNat
  nonceBytes := FFI.AEGIS256_NONCEBYTES.toNat
  tagBytes := FFI.AEGIS256_TAGBYTES.toNat

/- Stream Cipher Algorithm Specs -/

def StreamSpec : AlgorithmSpec where
  name := .mkSimple "XSalsa20"
  secretKeyBytes := FFI.STREAM_KEYBYTES.toNat
  nonceBytes := FFI.STREAM_NONCEBYTES.toNat

def ChaCha20StreamSpec : AlgorithmSpec where
  name := .mkSimple "ChaCha20"
  secretKeyBytes := FFI.CHACHA20_KEYBYTES.toNat
  nonceBytes := FFI.CHACHA20_NONCEBYTES.toNat

def ChaCha20IetfStreamSpec : AlgorithmSpec where
  name := .mkSimple "ChaCha20IETF"
  secretKeyBytes := FFI.CHACHA20_IETF_KEYBYTES.toNat
  nonceBytes := FFI.CHACHA20_IETF_NONCEBYTES.toNat

/- Password Hashing Algorithm Spec -/

def PwHashSpec : AlgorithmSpec where
  name := .mkSimple "Argon2id"
  saltBytes := FFI.PWHASH_SALTBYTES.toNat

/- Secret Stream Algorithm Spec -/

def SecretStreamSpec : AlgorithmSpec where
  name := .mkSimple "XChaCha20Poly1305SecretStream"
  secretKeyBytes := FFI.SECRETSTREAM_XCHACHA20POLY1305_KEYBYTES.toNat
  macBytes := FFI.SECRETSTREAM_XCHACHA20POLY1305_ABYTES.toNat
  tagBytes := FFI.SECRETSTREAM_XCHACHA20POLY1305_ABYTES.toNat
  headerBytes := FFI.SECRETSTREAM_XCHACHA20POLY1305_HEADERBYTES.toNat
  messageMaxBytes := FFI.SECRETSTREAM_XCHACHA20POLY1305_MESSAGEBYTES_MAX.toNat

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

/-- AEAD ciphertext containing embedded authentication tag -/
structure TaggedCipherText (spec : AlgorithmSpec) where
  bytes : ByteArray
  has_tag : bytes.size >= spec.tagBytes := by omega

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

/-- Message for secret stream operations -/
structure StreamMessage (spec : AlgorithmSpec) where
  bytes : ByteArray
  size_valid : bytes.size ≤ spec.messageMaxBytes

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
instance : CoeOut (TaggedCipherText spec) ByteArray := ⟨TaggedCipherText.bytes⟩
instance : CoeOut (SealedCipherText spec) ByteArray := ⟨SealedCipherText.bytes⟩
instance : CoeOut (HashOutput spec) ByteArray := ⟨HashOutput.bytes⟩
instance : CoeOut (AuthTag spec) ByteArray := ⟨AuthTag.bytes⟩
instance : CoeOut (Context spec) ByteArray := ⟨Context.bytes⟩
instance : CoeOut (SessionKey spec) ByteArray := ⟨SessionKey.bytes⟩
instance : CoeOut (Salt spec) ByteArray := ⟨Salt.bytes⟩
instance : CoeOut (StreamHeader spec) ByteArray := ⟨StreamHeader.bytes⟩
instance : CoeOut (StreamMessage spec) ByteArray := ⟨StreamMessage.bytes⟩
instance : CoeOut (StreamState spec) ByteArray := ⟨StreamState.bytes⟩

abbrev NonceNameGenerator := NonceId NameGeneratorSpec

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

end Sodium.Crypto
