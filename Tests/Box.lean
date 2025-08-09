import «Sodium».FFI.Basic
import «Sodium».FFI.Box
import «Sodium».Data.ByteArray

namespace Sodium.Tests.BoxFFI

open Sodium.FFI.Box

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
  IO.println s!"  BEFORENMBYTES: {BEFORENMBYTES}"
  IO.println s!"  SEALBYTES: {SEALBYTES}"

-- =============================================================================
-- Test Key Generation Operations
-- =============================================================================

-- Test basic keypair generation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey, _secretKey) ← keypair ctx
    if publicKey.size == PUBLICKEYBYTES.toNat then
      IO.println "✓ Keypair generation succeeded with correct public key size"
    else
      IO.println s!"✗ Public key size mismatch: expected {PUBLICKEYBYTES.toNat}, got {publicKey.size}"
  catch e =>
    IO.println s!"✗ Keypair generation failed: {e}"

-- Test deterministic keypair generation from seed
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let seed ← SecureArray.new ctx SEEDBYTES.toNat
    let (publicKey1, _secretKey1) ← seedKeypair ctx seed
    let (publicKey2, _secretKey2) ← seedKeypair ctx seed

    if publicKey1.size == PUBLICKEYBYTES.toNat then
      IO.println "✓ Seed keypair generation succeeded with correct size"
    else
      IO.println s!"✗ Seed keypair public key size mismatch: expected {PUBLICKEYBYTES.toNat}, got {publicKey1.size}"

    -- Both public keys should be identical since same seed
    if publicKey1 == publicKey2 then
      IO.println "✓ Deterministic keypair generation produces identical results"
    else
      IO.println "✗ Deterministic keypair generation should produce identical results"

  catch e =>
    IO.println s!"✗ Seed keypair generation failed: {e}"

-- Test seed keypair with wrong seed size (should fail)
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let wrongSeed ← SecureArray.new ctx (SEEDBYTES.toNat + 1)  -- Wrong size
    let _ ← seedKeypair ctx wrongSeed
    IO.println "✗ Seed keypair should fail with wrong seed size"
  catch e =>
    IO.println s!"✓ Seed keypair correctly rejected wrong seed size: {e}"

-- =============================================================================
-- Test Shared Secret Generation
-- =============================================================================

-- Test shared secret generation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (_publicKey1, secretKey1) ← keypair ctx
    let (publicKey2, _secretKey2) ← keypair ctx
    let _sharedSecret ← beforenm ctx publicKey2 secretKey1
    IO.println "✓ Shared secret generation succeeded"
  catch e =>
    IO.println s!"✗ Shared secret generation failed: {e}"

-- Test shared secret with wrong public key size (should fail)
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (_publicKey, secretKey) ← keypair ctx
    let wrongPublicKey := ByteArray.mk #[1, 2, 3]  -- Wrong size
    let _ ← beforenm ctx wrongPublicKey secretKey
    IO.println "✗ Shared secret should fail with wrong public key size"
  catch e =>
    IO.println s!"✓ Shared secret correctly rejected wrong public key size: {e}"

-- =============================================================================
-- Test Encryption/Decryption Operations
-- =============================================================================

-- Test basic encryption and decryption
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey1, secretKey1) ← keypair ctx
    let (publicKey2, secretKey2) ← keypair ctx

    let message := "Hello, Box encryption!".toUTF8
    let nonce := ByteArray.mk (List.range NONCEBYTES.toNat |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)

    -- Encrypt from 1 to 2
    let ciphertext ← easy ctx message nonce publicKey2 secretKey1

    -- Decrypt from 1 to 2
    let decrypted ← openEasy ctx ciphertext nonce publicKey1 secretKey2

    if decrypted == message then
      IO.println "✓ Box encryption/decryption round-trip succeeded"
    else
      IO.println "✗ Box encryption/decryption round-trip failed"

  catch e =>
    IO.println s!"✗ Box encryption/decryption failed: {e}"

-- Test encryption with wrong nonce size (should fail)
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey, secretKey) ← keypair ctx
    let message := "test".toUTF8
    let wrongNonce := ByteArray.mk #[1, 2, 3]  -- Wrong size
    let _ ← easy ctx message wrongNonce publicKey secretKey
    IO.println "✗ Encryption should fail with wrong nonce size"
  catch e =>
    IO.println s!"✓ Encryption correctly rejected wrong nonce size: {e}"

-- Test decryption with wrong ciphertext size (should fail)
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey, secretKey) ← keypair ctx
    let nonce := ByteArray.mk (List.range NONCEBYTES.toNat |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    let shortCiphertext := ByteArray.mk #[1, 2, 3]  -- Too short
    let _ ← openEasy ctx shortCiphertext nonce publicKey secretKey
    IO.println "✗ Decryption should fail with too short ciphertext"
  catch e =>
    IO.println s!"✓ Decryption correctly rejected short ciphertext: {e}"

-- =============================================================================
-- Test Shared Secret Encryption/Decryption
-- =============================================================================

-- Test encryption with shared secret
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey1, secretKey1) ← keypair ctx
    let (publicKey2, secretKey2) ← keypair ctx

    -- Generate shared secrets (both should be identical)
    let sharedSecret1 ← beforenm ctx publicKey2 secretKey1
    let sharedSecret2 ← beforenm ctx publicKey1 secretKey2

    let message := "Shared secret encryption test".toUTF8
    let nonce := ByteArray.mk (List.range NONCEBYTES.toNat |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)

    -- Encrypt with first shared secret
    let ciphertext ← easyAfternm ctx message nonce sharedSecret1

    -- Decrypt with second shared secret
    let decrypted ← openEasyAfternm ctx ciphertext nonce sharedSecret2

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
    let (publicKey1, secretKey1) ← keypair ctx
    let (publicKey2, secretKey2) ← keypair ctx

    let message := "Detached encryption test".toUTF8
    let nonce := ByteArray.mk (List.range NONCEBYTES.toNat |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)

    -- Encrypt detached
    let (ciphertext, mac) ← detached ctx message nonce publicKey2 secretKey1

    -- Decrypt detached
    let decrypted ← openDetached ctx ciphertext mac nonce publicKey1 secretKey2

    if decrypted == message then
      IO.println "✓ Detached encryption/decryption succeeded"
    else
      IO.println "✗ Detached encryption/decryption failed"

    -- Verify MAC size
    if mac.size == MACBYTES.toNat then
      IO.println "✓ Detached MAC has correct size"
    else
      IO.println s!"✗ Detached MAC size mismatch: expected {MACBYTES.toNat}, got {mac.size}"

  catch e =>
    IO.println s!"✗ Detached encryption/decryption failed: {e}"

-- Test detached operations with shared secret
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey1, secretKey1) ← keypair ctx
    let (publicKey2, secretKey2) ← keypair ctx

    let sharedSecret1 ← beforenm ctx publicKey2 secretKey1
    let sharedSecret2 ← beforenm ctx publicKey1 secretKey2

    let message := "Detached shared secret test".toUTF8
    let nonce := ByteArray.mk (List.range NONCEBYTES.toNat |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)

    -- Encrypt detached with shared secret
    let (ciphertext, mac) ← detachedAfternm ctx message nonce sharedSecret1

    -- Decrypt detached with shared secret
    let decrypted ← openDetachedAfternm ctx ciphertext mac nonce sharedSecret2

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
    let (publicKey, secretKey) ← keypair ctx

    let message := "Sealed box test message".toUTF8

    -- Seal to public key
    let sealed ← «seal» ctx message publicKey

    -- Open with keypair
    let decrypted ← sealOpen ctx sealed publicKey secretKey

    if decrypted == message then
      IO.println "✓ Sealed box encryption/decryption succeeded"
    else
      IO.println "✗ Sealed box encryption/decryption failed"

    -- Verify sealed size
    let expectedSize := message.size + SEALBYTES.toNat
    if sealed.size == expectedSize then
      IO.println "✓ Sealed box has correct size"
    else
      IO.println s!"✗ Sealed box size mismatch: expected {expectedSize}, got {sealed.size}"

  catch e =>
    IO.println s!"✗ Sealed box encryption/decryption failed: {e}"

-- Test sealed box with wrong public key size (should fail)
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let message := "test".toUTF8
    let wrongPublicKey := ByteArray.mk #[1, 2, 3]  -- Wrong size
    let _ ← «seal» ctx message wrongPublicKey
    IO.println "✗ Sealed box should fail with wrong public key size"
  catch e =>
    IO.println s!"✓ Sealed box correctly rejected wrong public key size: {e}"

-- =============================================================================
-- Test Error Handling and Edge Cases
-- =============================================================================

-- Test encryption with empty message
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey1, secretKey1) ← keypair ctx
    let (publicKey2, secretKey2) ← keypair ctx

    let emptyMessage := ByteArray.empty
    let nonce := ByteArray.mk (List.range NONCEBYTES.toNat |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)

    let ciphertext ← easy ctx emptyMessage nonce publicKey2 secretKey1
    let decrypted ← openEasy ctx ciphertext nonce publicKey1 secretKey2

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
    let (_publicKey1, secretKey1) ← keypair ctx
    let (publicKey2, _secretKey2) ← keypair ctx
    let (publicKey3, secretKey3) ← keypair ctx  -- Wrong keypair

    let message := "Authentication test".toUTF8
    let nonce := ByteArray.mk (List.range NONCEBYTES.toNat |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)

    let ciphertext ← easy ctx message nonce publicKey2 secretKey1
    let _ ← openEasy ctx ciphertext nonce publicKey3 secretKey3  -- Wrong keys
    IO.println "✗ Decryption should fail with wrong keypair"
  catch e =>
    IO.println s!"✓ Decryption correctly failed with wrong keypair: {e}"

-- Test MAC verification failure in detached mode
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey1, secretKey1) ← keypair ctx
    let (publicKey2, secretKey2) ← keypair ctx

    let message := "MAC verification test".toUTF8
    let nonce := ByteArray.mk (List.range NONCEBYTES.toNat |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)

    let (ciphertext, _mac) ← detached ctx message nonce publicKey2 secretKey1

    -- Create wrong MAC
    let wrongMac := ByteArray.mk (List.range MACBYTES.toNat |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)

    let _ ← openDetached ctx ciphertext wrongMac nonce publicKey1 secretKey2
    IO.println "✗ Detached decryption should fail with wrong MAC"
  catch e =>
    IO.println s!"✓ Detached decryption correctly failed with wrong MAC: {e}"

-- =============================================================================
-- Test Security Properties
-- =============================================================================

-- Test that different nonces produce different ciphertexts
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (_publicKey1, secretKey1) ← keypair ctx
    let (publicKey2, _secretKey2) ← keypair ctx

    let message := "Nonce uniqueness test".toUTF8
    let nonce1 := ByteArray.mk (List.range NONCEBYTES.toNat |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    let nonce2 := ByteArray.mk (List.range NONCEBYTES.toNat |>.map (fun x => (x + 1) % 256) |>.map UInt8.ofNat |>.toArray)

    let ciphertext1 ← easy ctx message nonce1 publicKey2 secretKey1
    let ciphertext2 ← easy ctx message nonce2 publicKey2 secretKey1

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
    let (_publicKey1, secretKey1) ← keypair ctx
    let (publicKey2, _secretKey2) ← keypair ctx
    let (publicKey3, _secretKey3) ← keypair ctx

    let sharedSecret1 ← beforenm ctx publicKey2 secretKey1
    let sharedSecret2 ← beforenm ctx publicKey3 secretKey1

    -- Encrypt same message with both shared secrets
    let message := "Shared secret uniqueness test".toUTF8
    let nonce := ByteArray.mk (List.range NONCEBYTES.toNat |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)

    let ciphertext1 ← easyAfternm ctx message nonce sharedSecret1
    let ciphertext2 ← easyAfternm ctx message nonce sharedSecret2

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
    let (publicKey1, secretKey1) ← keypair ctx
    let (publicKey2, secretKey2) ← keypair ctx

    let mut success_count := 0
    for i in [0:10] do
      try
        let message := s!"Message {i}".toUTF8
        let nonce := ByteArray.mk (List.range NONCEBYTES.toNat |>.map (fun x => (x + i) % 256) |>.map UInt8.ofNat |>.toArray)

        let ciphertext ← easy ctx message nonce publicKey2 secretKey1
        let decrypted ← openEasy ctx ciphertext nonce publicKey1 secretKey2

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
    let (publicKey1, secretKey1) ← keypair ctx
    let (publicKey2, secretKey2) ← keypair ctx

    -- Create a 1KB message
    let largeMessage := ByteArray.mk (List.range 1024 |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    let nonce := ByteArray.mk (List.range NONCEBYTES.toNat |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)

    let ciphertext ← easy ctx largeMessage nonce publicKey2 secretKey1
    let decrypted ← openEasy ctx ciphertext nonce publicKey1 secretKey2

    if decrypted == largeMessage then
      IO.println "✓ Large message (1KB) encryption/decryption succeeded"
    else
      IO.println "✗ Large message (1KB) encryption/decryption failed"

  catch e =>
    IO.println s!"✗ Large message encryption/decryption failed: {e}"

#eval IO.println "\n=== Box FFI Tests Complete ==="

end Sodium.Tests.BoxFFI
