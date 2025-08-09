import Sodium.FFI.Basic

open Lean

namespace Sodium.Crypto

inductive DecryptError
  | refused
  | invalidEncoding (data : ByteArray)
  | invalidString (utf8 : String)
  | invalidJson (json : Json)
  deriving TypeName, Hashable, Inhabited

private instance : Ord Name := ⟨Name.quickCmp⟩

/--
This structure provides compile-time size information for all fields used across
different cryptographic algorithms, enabling type-safe wrappers with size validation.
-/
structure Spec where
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

instance : Coe Spec Name := ⟨Spec.name⟩

def NameGeneratorSpec : Spec where
  name := .mkSimple "nonce"
  /-
    Generic nonces should support `ByteArray.toUInt64LE!` and `ByteArray.toUInt64BE!`, though
    `ByteArray.hash` should also suffice.

    This choice also has the added benefit of preventing mixups between nonces used generically
    and those used by more secure algorithms (which typically require 24 bytes).
  -/
  nonceBytes := 8

  /- Added for convenience. -/
  seedBytes := 32

variable {σ : Type}

/-- Private key for asymmetric cryptography (curve25519, ed25519). Stored in secure memory. -/
structure SecretKey (τ : Sodium σ) (spec : Spec) where
  bytes : SecureArray τ
  size_eq_secret_key_bytes : bytes.size = spec.secretKeyBytes

/-- Public key for asymmetric cryptography (curve25519, ed25519). Safe to share publicly. -/
structure PublicKey (spec : Spec) where
  bytes : ByteArray
  size_eq_public_key_bytes : bytes.size = spec.publicKeyBytes

/-- Public/private key pair for asymmetric cryptography. Contains both keys for crypto operations. -/
structure KeyPair (τ : Sodium σ) (spec : Spec) where
  public : PublicKey spec
  secret : SecretKey τ spec

/-- Nonce (number used once) for cryptographic operations. Must be unique per key/message pair. -/
structure NonceId (spec : Spec) where
  bytes : ByteArray
  size_eq_nonce_bytes : bytes.size = spec.nonceBytes

/-- Digital signature for message authentication and non-repudiation (ed25519). -/
structure Signature (spec : Spec) where
  bytes : ByteArray
  size_eq_mac_bytes : bytes.size = spec.macBytes

/-- Precomputed shared secret for Box operations. Expensive DH computation result in secure memory. -/
structure SharedSecret (τ : Sodium σ) (spec : Spec) where
  bytes : SecureArray τ
  size_eq_before_nm_bytes : bytes.size = spec.beforeNmBytes

/-- Cryptographic seed for deterministic key generation. High-entropy secret in secure memory. -/
structure Seed (τ : Sodium σ) (spec : Spec) where
  bytes : SecureArray τ
  size_eq_seed_bytes : bytes.size = spec.seedBytes

/-- Authenticated ciphertext with embedded MAC. Provides confidentiality and integrity. -/
structure CipherText (spec : Spec) where
  bytes : ByteArray
  nonce : NonceId spec
  size_ge_mac_bytes : bytes.size ≥ spec.macBytes

/-- Message Authentication Code (MAC) for verifying data integrity and authenticity. -/
structure Mac (spec : Spec) where
  bytes : ByteArray
  size_eq_mac_bytes : bytes.size = spec.macBytes

/-- Ciphertext without embedded MAC. Requires separate MAC for authenticated encryption. -/
structure DetachedCipherText (spec : Spec) where
  bytes : ByteArray
  mac : Mac spec
  nonce : NonceId spec

/-- AEAD ciphertext with embedded authentication tag. Single-pass encrypt-then-authenticate. -/
structure TaggedCipherText (spec : Spec) where
  bytes : ByteArray
  size_ge_tag_bytes : bytes.size ≥ spec.tagBytes

/-- Sealed box ciphertext with ephemeral key and MAC. Anonymous encryption to public key. -/
structure SealedCipherText (spec : Spec) where
  bytes : ByteArray
  size_ge_seal_bytes : bytes.size ≥ spec.sealBytes

/-- Cryptographic hash output (BLAKE2b). Fixed-size digest of arbitrary input data. -/
structure HashOutput (spec : Spec) where
  bytes : ByteArray
  size_eq_hash_bytes : bytes.size = spec.hashBytes

/-- Authentication tag for AEAD encryption. Verifies ciphertext integrity and authenticity. -/
structure AuthTag (spec : Spec) where
  bytes : ByteArray
  size_eq_tag_bytes : bytes.size = spec.tagBytes

/-- Context identifier for key derivation. Distinguishes different derived key purposes. -/
structure Context (spec : Spec) where
  bytes : ByteArray
  size_eq_context_bytes : bytes.size = spec.contextBytes

/-- Derived session key for symmetric encryption. Generated from key exchange (X25519). -/
structure SessionKey (τ : Sodium σ) (spec : Spec) where
  bytes : SecureArray τ
  size_eq_session_key_bytes : bytes.size = spec.sessionKeyBytes

/-- Salt for password hashing (Argon2). Random value preventing rainbow table attacks. -/
structure Salt (τ : Sodium σ) (spec : Spec) where
  bytes : SecureArray τ
  size_eq_salt_bytes : bytes.size = spec.saltBytes

/-- Header for streaming AEAD encryption. Contains state information for message sequence. -/
structure StreamHeader (spec : Spec) where
  bytes : ByteArray
  size_eq_header_bytes : bytes.size = spec.headerBytes

/-- Message chunk for streaming encryption. Size-bounded for incremental processing. -/
structure StreamMessage (spec : Spec) where
  bytes : ByteArray
  size_le_message_max_bytes : bytes.size ≤ spec.messageMaxBytes

end Sodium.Crypto
