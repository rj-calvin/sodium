import «Sodium».FFI.Basic
import «Sodium».FFI.Box
import «Sodium».Data.ByteVector

namespace Sodium.Tests.BoxFFI

open Sodium FFI.Box

-- =============================================================================
-- Test Constants and Size Validations
-- =============================================================================

#eval show IO Unit from do
  IO.println s!"Box constants:"
  IO.println s!"  PUBLICKEYBYTES: {PUBLICKEYBYTES}"
  IO.println s!"  SECRETKEYBYTES: {SECRETKEYBYTES}"
  IO.println s!"  NONCEBYTES: {NONCEBYTES}"
  IO.println s!"  MACBYTES: {MACBYTES}"
  IO.println s!"  SEEDBYTES: {SEEDBYTES}"
  IO.println s!"  SHAREDBYTES: {SHAREDBYTES}"
  IO.println s!"  SEALBYTES: {SEALBYTES}"

-- =============================================================================
-- Test Key Generation Operations
-- =============================================================================

-- Test basic keypair generation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey, _secretKey) ← keypair (τ := ctx)
    if publicKey.size == PUBLICKEYBYTES then
      IO.println "✓ Keypair generation succeeded with correct public key size"
    else
      IO.println s!"✗ Public key size mismatch: expected {PUBLICKEYBYTES}, got {publicKey.size}"
  catch e =>
    IO.println s!"✗ Keypair generation failed: {e}"

-- Test deterministic keypair generation from seed
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let seed ← SecureVector.new (τ := ctx) SEEDBYTES
    let (publicKey1, _secretKey1) ← seedKeypair (τ := ctx) seed
    let (publicKey2, _secretKey2) ← seedKeypair (τ := ctx) seed

    if publicKey1.size == PUBLICKEYBYTES then
      IO.println "✓ Seed keypair generation succeeded with correct size"
    else
      IO.println s!"✗ Seed keypair public key size mismatch: expected {PUBLICKEYBYTES}, got {publicKey1.size}"

    -- Both public keys should be identical since same seed
    if publicKey1 == publicKey2 then
      IO.println "✓ Deterministic keypair generation produces identical results"
    else
      IO.println "✗ Deterministic keypair generation should produce identical results"

  catch e =>
    IO.println s!"✗ Seed keypair generation failed: {e}"


-- =============================================================================
-- Test Shared Secret Generation
-- =============================================================================

-- Test shared secret generation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (_publicKey1, secretKey1) ← keypair (τ := ctx)
    let (publicKey2, _secretKey2) ← keypair (τ := ctx)
    let some _sharedSecret ← beforenm (τ := ctx) publicKey2 secretKey1
      | do IO.println "✗ Shared secret generation failed unexpectedly"; return
    IO.println "✓ Shared secret generation succeeded"
  catch e =>
    IO.println s!"✗ Shared secret generation failed: {e}"


-- =============================================================================
-- Test Encryption/Decryption Operations
-- =============================================================================

-- Test basic encryption and decryption
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey1, secretKey1) ← keypair (τ := ctx)
    let (publicKey2, secretKey2) ← keypair (τ := ctx)

    let message := "Hello, Box encryption!".toUTF8.toVector
    let nonce : ByteVector NONCEBYTES :=
      (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk).toVector.cast

    -- Encrypt from 1 to 2
    let some ciphertext ← easy (τ := ctx) message nonce publicKey2 secretKey1
      | do IO.println "✗ Box encryption failed unexpectedly"; return

    -- Decrypt from 1 to 2
    let result ← openEasy (τ := ctx) ciphertext nonce publicKey1 secretKey2
    let some decrypted := result
      | do IO.println "✗ Box decryption failed unexpectedly"; return

    if decrypted == message then
      IO.println "✓ Box encryption/decryption round-trip succeeded"
    else
      IO.println "✗ Box encryption/decryption round-trip failed"

  catch e =>
    IO.println s!"✗ Box encryption/decryption failed: {e}"



-- =============================================================================
-- Test Shared Secret Encryption/Decryption
-- =============================================================================

-- Test encryption with shared secret
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey1, secretKey1) ← keypair (τ := ctx)
    let (publicKey2, secretKey2) ← keypair (τ := ctx)

    -- Generate shared secrets (both should be identical)
    let some sharedSecret1 ← beforenm (τ := ctx) publicKey2 secretKey1
      | do IO.println "✗ Shared secret generation 1 failed unexpectedly"; return
    let some sharedSecret2 ← beforenm (τ := ctx) publicKey1 secretKey2
      | do IO.println "✗ Shared secret generation 2 failed unexpectedly"; return

    let message := "Shared secret encryption test".toUTF8.toVector
    let nonce := ByteVector.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk)

    -- Encrypt with first shared secret
    let ciphertext ← easyAfternm (τ := ctx) message nonce sharedSecret1

    -- Decrypt with second shared secret
    let result ← openEasyAfternm (τ := ctx) ciphertext nonce sharedSecret2
    let some decrypted := result
      | do IO.println "✗ Shared secret decryption failed unexpectedly"; return

    if decrypted == message then
      IO.println "✓ Shared secret encryption/decryption succeeded"
    else
      IO.println "✗ Shared secret encryption/decryption failed"

  catch e =>
    IO.println s!"✗ Shared secret encryption/decryption failed: {e}"

-- =============================================================================
-- Test Detached Operations
-- =============================================================================

-- Test detached encryption and decryption
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey1, secretKey1) ← keypair (τ := ctx)
    let (publicKey2, secretKey2) ← keypair (τ := ctx)

    let message := "Detached encryption test".toUTF8.toVector
    let nonce := ByteVector.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk)

    -- Encrypt detached
    let some (ciphertext, mac) ← detached (τ := ctx) message nonce publicKey2 secretKey1
      | do IO.println "✗ Detached encryption failed unexpectedly"; return

    -- Decrypt detached
    let some decrypted ← openDetached (τ := ctx) ciphertext mac nonce publicKey1 secretKey2
      | do IO.println "✗ Detached decryption failed unexpectedly"; return

    if decrypted == message then
      IO.println "✓ Detached encryption/decryption succeeded"
    else
      IO.println "✗ Detached encryption/decryption failed"

    -- Verify MAC size
    if mac.size == MACBYTES then
      IO.println "✓ Detached MAC has correct size"
    else
      IO.println s!"✗ Detached MAC size mismatch: expected {MACBYTES}, got {mac.size}"

  catch e =>
    IO.println s!"✗ Detached encryption/decryption failed: {e}"

-- Test detached operations with shared secret
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey1, secretKey1) ← keypair (τ := ctx)
    let (publicKey2, secretKey2) ← keypair (τ := ctx)

    let some sharedSecret1 ← beforenm (τ := ctx) publicKey2 secretKey1
      | do IO.println "✗ Shared secret generation 1 failed unexpectedly"; return
    let some sharedSecret2 ← beforenm (τ := ctx) publicKey1 secretKey2
      | do IO.println "✗ Shared secret generation 2 failed unexpectedly"; return

    let message := "Detached shared secret test".toUTF8.toVector
    let nonce := ByteVector.mk (n := NONCEBYTES) (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk)

    -- Encrypt detached with shared secret
    let (ciphertext, mac) ← detachedAfternm (τ := ctx) message nonce sharedSecret1

    -- Decrypt detached with shared secret
    let some decrypted ← openDetachedAfternm (τ := ctx) ciphertext mac nonce sharedSecret2
      | do IO.println "✗ Detached shared secret decryption failed unexpectedly"; return

    if decrypted == message then
      IO.println "✓ Detached shared secret encryption/decryption succeeded"
    else
      IO.println "✗ Detached shared secret encryption/decryption failed"

  catch e =>
    IO.println s!"✗ Detached shared secret encryption/decryption failed: {e}"

-- =============================================================================
-- Test Sealed Box Operations
-- =============================================================================

-- Test sealed box encryption and decryption
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey, secretKey) ← keypair (τ := ctx)

    let message := "Sealed box test message".toUTF8.toVector

    -- Seal to public key
    let some sealed ← easyAnonymous (τ := ctx) message publicKey
      | do IO.println "✗ Sealed box encryption failed unexpectedly"; return

    -- Open with keypair
    let some decrypted ← openAnonymous (τ := ctx) sealed publicKey secretKey
      | do IO.println "✗ Sealed box decryption failed unexpectedly"; return

    if decrypted == message then
      IO.println "✓ Sealed box encryption/decryption succeeded"
    else
      IO.println "✗ Sealed box encryption/decryption failed"

    -- Verify sealed size
    let expectedSize := message.size + SEALBYTES
    if sealed.size == expectedSize then
      IO.println "✓ Sealed box has correct size"
    else
      IO.println s!"✗ Sealed box size mismatch: expected {expectedSize}, got {sealed.size}"

  catch e =>
    IO.println s!"✗ Sealed box encryption/decryption failed: {e}"


-- =============================================================================
-- Test Error Handling and Edge Cases
-- =============================================================================

-- Test encryption with empty message
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey1, secretKey1) ← keypair (τ := ctx)
    let (publicKey2, secretKey2) ← keypair (τ := ctx)

    let emptyMessage := ByteVector.empty
    let nonce := ByteVector.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk)

    let some ciphertext ← easy (τ := ctx) emptyMessage nonce publicKey2 secretKey1
      | do IO.println "✗ Empty message encryption failed unexpectedly"; return
    let result ← openEasy (τ := ctx) ciphertext nonce publicKey1 secretKey2
    let some decrypted := result
      | do IO.println "✗ Empty message decryption failed unexpectedly"; return

    if decrypted == emptyMessage then
      IO.println "✓ Empty message encryption/decryption succeeded"
    else
      IO.println "✗ Empty message encryption/decryption failed"

  catch e =>
    IO.println s!"✗ Empty message encryption/decryption failed: {e}"

-- Test decryption with wrong keypair (should fail)
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (_publicKey1, secretKey1) ← keypair (τ := ctx)
    let (publicKey2, _secretKey2) ← keypair (τ := ctx)
    let (publicKey3, secretKey3) ← keypair (τ := ctx)  -- Wrong keypair

    let message := "Authentication test".toUTF8.toVector
    let nonce := ByteVector.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk)

    let some ciphertext ← easy (τ := ctx) message nonce publicKey2 secretKey1
      | do IO.println "✗ Authentication test encryption failed unexpectedly"; return
    let result ← openEasy (τ := ctx) ciphertext nonce publicKey3 secretKey3  -- Wrong keys
    match result with
    | none => IO.println "✓ Decryption correctly failed with wrong keypair: authentication failed"
    | some _ => IO.println "✗ Decryption should fail with wrong keypair"
  catch e =>
    IO.println s!"✓ Decryption correctly failed with wrong keypair: {e}"

-- Test MAC verification failure in detached mode
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey1, secretKey1) ← keypair (τ := ctx)
    let (publicKey2, secretKey2) ← keypair (τ := ctx)

    let message := "MAC verification test".toUTF8.toVector
    let nonce := ByteVector.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk)

    let some (ciphertext, _mac) ← detached (τ := ctx) message nonce publicKey2 secretKey1
      | do IO.println "✗ Detached encryption failed unexpectedly"; return

    -- Create wrong MAC
    let wrongMac := ByteVector.mk (List.range MACBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk)

    let result ← openDetached (τ := ctx) ciphertext wrongMac nonce publicKey1 secretKey2
    match result with
    | none => IO.println "✓ Detached decryption correctly failed with wrong MAC: authentication failed"
    | some _ => IO.println "✗ Detached decryption should fail with wrong MAC"
  catch e =>
    IO.println s!"✓ Detached decryption correctly failed with wrong MAC: {e}"

-- =============================================================================
-- Test Security Properties
-- =============================================================================

-- Test that different nonces produce different ciphertexts
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (_publicKey1, secretKey1) ← keypair (τ := ctx)
    let (publicKey2, _secretKey2) ← keypair (τ := ctx)

    let message := "Nonce uniqueness test".toUTF8.toVector
    let nonce1 := ByteVector.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk)
    let nonce2 := ByteVector.mk (List.range NONCEBYTES |>.map (fun x => (x + 1) % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk)

    let some ciphertext1 ← easy (τ := ctx) message nonce1 publicKey2 secretKey1
      | do IO.println "✗ Semantic security test encryption 1 failed"; return
    let some ciphertext2 ← easy (τ := ctx) message nonce2 publicKey2 secretKey1
      | do IO.println "✗ Semantic security test encryption 2 failed"; return

    if ciphertext1 != ciphertext2 then
      IO.println "✓ Different nonces produce different ciphertexts (semantic security)"
    else
      IO.println "✗ Different nonces should produce different ciphertexts"

  catch e =>
    IO.println s!"✗ Nonce uniqueness test failed: {e}"

-- Test that different keypairs produce different shared secrets
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (_publicKey1, secretKey1) ← keypair (τ := ctx)
    let (publicKey2, _secretKey2) ← keypair (τ := ctx)
    let (publicKey3, _secretKey3) ← keypair (τ := ctx)

    let some sharedSecret1 ← beforenm (τ := ctx) publicKey2 secretKey1
      | do IO.println "✗ Shared secret generation 1 failed unexpectedly"; return
    let some sharedSecret2 ← beforenm (τ := ctx) publicKey3 secretKey1
      | do IO.println "✗ Shared secret generation 2 failed unexpectedly"; return

    -- Encrypt same message with both shared secrets
    let message := "Shared secret uniqueness test".toUTF8.toVector
    let nonce := ByteVector.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk)

    let ciphertext1 ← easyAfternm (τ := ctx) message nonce sharedSecret1
    let ciphertext2 ← easyAfternm (τ := ctx) message nonce sharedSecret2

    if ciphertext1 != ciphertext2 then
      IO.println "✓ Different keypairs produce different shared secrets"
    else
      IO.println "✗ Different keypairs should produce different shared secrets"

  catch e =>
    IO.println s!"✗ Shared secret uniqueness test failed: {e}"

-- =============================================================================
-- Performance and Stress Tests
-- =============================================================================

-- Test multiple consecutive operations
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey1, secretKey1) ← keypair (τ := ctx)
    let (publicKey2, secretKey2) ← keypair (τ := ctx)

    let mut success_count := 0
    for i in [0:10] do
      try
        let message := s!"Message {i}".toUTF8.toVector
        let nonce := ByteVector.mk (List.range NONCEBYTES |>.map (fun x => (x + i) % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk)

        let some ciphertext ← easy (τ := ctx) message nonce publicKey2 secretKey1
          | continue
        let result ← openEasy (τ := ctx) ciphertext nonce publicKey1 secretKey2
        let some decrypted := result
          | continue

        if decrypted == message then
          success_count := success_count + 1
      catch _ =>
        continue

    IO.println s!"✓ Multiple consecutive operations: {success_count}/10 succeeded"

  catch e =>
    IO.println s!"✗ Multiple consecutive operations failed: {e}"

-- Test with larger messages
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey1, secretKey1) ← keypair (τ := ctx)
    let (publicKey2, secretKey2) ← keypair (τ := ctx)

    -- Create a 1KB message
    let largeMessageArray := List.range 1024 |>.map (· % 256) |>.map UInt8.ofNat |>.toArray
    let largeMessage := (ByteArray.mk largeMessageArray).toVector
    let nonce := ByteVector.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk)

    let some ciphertext ← easy (τ := ctx) largeMessage nonce publicKey2 secretKey1
      | do IO.println "✗ Large message encryption failed unexpectedly"; return
    let result ← openEasy (τ := ctx) ciphertext nonce publicKey1 secretKey2
    let some decrypted := result
      | do IO.println "✗ Large message decryption failed unexpectedly"; return

    if decrypted == largeMessage then
      IO.println "✓ Large message (1KB) encryption/decryption succeeded"
    else
      IO.println "✗ Large message (1KB) encryption/decryption failed"

  catch e =>
    IO.println s!"✗ Large message encryption/decryption failed: {e}"

#eval IO.println "\n=== Box FFI Tests Complete ==="

end Sodium.Tests.BoxFFI
