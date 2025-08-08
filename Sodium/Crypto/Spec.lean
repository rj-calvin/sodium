import Sodium.FFI.Basic

open Lean

namespace Sodium.Crypto

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
    `ByteArray.compact!` should also suffice (despite producing a different result).

    This choice also has the added benefit of preventing mixups between nonces used generically
    and those used by more secure algorithms.
  -/
  nonceBytes := 8

end Sodium.Crypto
