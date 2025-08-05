/-
Cryptographic utility functions for secure memory management and constant-time operations.

This module provides high-level wrappers around LibSodium's utility functions,
ensuring proper security practices for memory management and secret comparisons.
-/
import Sodium.FFI.Utils
import Sodium.FFI.SecretBox
import Sodium.Crypto.Types

open Lean

namespace Sodium.Crypto.Utils

variable {spec : AlgorithmSpec}

/--
Securely zero out any buffer's memory.
Use this for cleaning up temporary sensitive data.
-/
def zeroBuffer (buffer : ByteArray) : IO Unit :=
  FFI.sodiumMemzero buffer

/--
Check if a buffer contains only zero bytes.
Uses LibSodium's constant-time implementation to avoid timing attacks.
-/
def isBufferZero (buffer : ByteArray) : IO Bool :=
  FFI.sodiumIsZero buffer

/--
Compare two nonces lexicographically in constant time.
Useful for nonce ordering and counter operations.
Returns: -1 if nonce1 < nonce2, 0 if equal, 1 if nonce1 > nonce2
-/
def nonceCompare (nonce1 nonce2 : NonceId spec) : IO Int32 :=
  FFI.sodiumCompare nonce1.bytes nonce2.bytes

/--
Verify a 16-byte MAC in constant time.
Use this for SecretBox MAC verification (MACBYTES = 16).
-/
def verifyMac16 (expected computed : ByteArray) : IO Bool := do
  if expected.size != 16 || computed.size != 16 then
    return false
  FFI.cryptoVerify16 expected computed

/--
Verify a 32-byte value in constant time.
Useful for hash comparisons and key verification.
-/
def verifyHash32 (expected computed : ByteArray) : IO Bool := do
  if expected.size != 32 || computed.size != 32 then
    return false
  FFI.cryptoVerify32 expected computed

/--
Verify a 64-byte signature in constant time.
Use this for Ed25519 signature verification.
-/
def verifySignature64 (expected computed : ByteArray) : IO Bool := do
  if expected.size != 64 || computed.size != 64 then
    return false
  FFI.cryptoVerify64 expected computed

/--
Get the maximum message size for SecretBox operations.
Messages larger than this will be rejected by LibSodium.
-/
def getSecretBoxMaxMessageSize : BaseIO USize := FFI.secretBoxMessageBytesMax

/--
Validate that a message size is within SecretBox limits.
-/
def validateMessageSize (messageSize : Nat) : BaseIO Bool := do
  let maxSize ← getSecretBoxMaxMessageSize
  return messageSize ≤ maxSize.toNat

end Sodium.Crypto.Utils
