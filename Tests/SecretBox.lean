import «Sodium».FFI.Basic
import «Sodium».FFI.SecretBox
import «Sodium».Data.ByteArray

namespace Sodium.Tests.SecretBoxFFI

open Sodium.FFI.SecretBox

-- Display SecretBox constants
#eval show IO Unit from do
  IO.println s!"SecretBox constants:"
  IO.println s!"  KEYBYTES: {KEYBYTES}"
  IO.println s!"  NONCEBYTES: {NONCEBYTES}"
  IO.println s!"  MACBYTES: {MACBYTES}"

-- Test secure key generation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey ← keygen ctx
    if secretKey.size == KEYBYTES then
      IO.println "✓ Secure key generation succeeded with correct size"
    else
      IO.println s!"✗ Key size mismatch: expected {KEYBYTES}, got {secretKey.size}"
  catch e =>
    IO.println s!"✗ Key generation failed: {e}"

-- Test basic encryption/decryption round-trip
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey ← keygen ctx
    
    let message := "Hello, SecretBox encryption!".toUTF8
    let nonce := ByteArray.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    
    let ciphertext ← easy ctx message nonce secretKey
    let decrypted ← openEasy ctx ciphertext nonce secretKey
    
    if decrypted == message then
      IO.println "✓ SecretBox encryption/decryption round-trip succeeded"
    else
      IO.println "✗ SecretBox encryption/decryption round-trip failed"
  catch e =>
    IO.println s!"✗ SecretBox round-trip failed: {e}"

-- Test encryption with wrong nonce size (should fail)
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey ← keygen ctx
    let message := "test".toUTF8
    let wrongNonce := ByteArray.mk #[1, 2, 3]  -- Wrong size
    let _ ← easy ctx message wrongNonce secretKey
    IO.println "✗ Encryption should fail with wrong nonce size"
  catch e =>
    IO.println s!"✓ Encryption correctly rejected wrong nonce size: {e}"

-- Test decryption with short ciphertext (should fail)
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey ← keygen ctx
    let nonce := ByteArray.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    let shortCiphertext := ByteArray.mk #[1, 2, 3]  -- Too short
    let _ ← openEasy ctx shortCiphertext nonce secretKey
    IO.println "✗ Decryption should fail with too short ciphertext"
  catch e =>
    IO.println s!"✓ Decryption correctly rejected short ciphertext: {e}"

-- Test detached encryption/decryption
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey ← keygen ctx
    
    let message := "Detached SecretBox test".toUTF8
    let nonce := ByteArray.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    
    -- Encrypt detached
    let (ciphertext, mac) ← detached ctx message nonce secretKey
    
    -- Decrypt detached
    let decrypted ← openDetached ctx ciphertext mac nonce secretKey
    
    if decrypted == message && mac.size == MACBYTES then
      IO.println "✓ Detached encryption/decryption succeeded"
      IO.println s!"✓ Detached MAC has correct size: {mac.size}"
    else
      IO.println "✗ Detached encryption/decryption failed"
  catch e =>
    IO.println s!"✗ Detached encryption/decryption failed: {e}"

-- Test empty message encryption/decryption
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey ← keygen ctx
    
    let emptyMessage := ByteArray.empty
    let nonce := ByteArray.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    
    let ciphertext ← easy ctx emptyMessage nonce secretKey
    let decrypted ← openEasy ctx ciphertext nonce secretKey
    
    if decrypted == emptyMessage then
      IO.println "✓ Empty message encryption/decryption succeeded"
    else
      IO.println "✗ Empty message encryption/decryption failed"
  catch e =>
    IO.println s!"✗ Empty message encryption/decryption failed: {e}"

-- Test decryption with wrong key (should fail)
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey1 ← keygen ctx
    let secretKey2 ← keygen ctx  -- Different key
    
    let message := "Authentication test".toUTF8
    let nonce := ByteArray.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    
    let ciphertext ← easy ctx message nonce secretKey1
    let _ ← openEasy ctx ciphertext nonce secretKey2  -- Wrong key
    IO.println "✗ Decryption should fail with wrong key"
  catch e =>
    IO.println s!"✓ Decryption correctly failed with wrong key: {e}"

-- Test detached decryption with wrong MAC (should fail)  
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey ← keygen ctx
    
    let message := "MAC verification test".toUTF8
    let nonce := ByteArray.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    
    let (ciphertext, _mac) ← detached ctx message nonce secretKey
    
    -- Create wrong MAC
    let wrongMac := ByteArray.mk (List.range MACBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    
    let _ ← openDetached ctx ciphertext wrongMac nonce secretKey
    IO.println "✗ Detached decryption should fail with wrong MAC"
  catch e =>
    IO.println s!"✓ Detached decryption correctly failed with wrong MAC: {e}"

-- Test that different nonces produce different ciphertexts (semantic security)
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey ← keygen ctx
    
    let message := "Nonce uniqueness test".toUTF8
    let nonce1 := ByteArray.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    let nonce2 := ByteArray.mk (List.range NONCEBYTES |>.map (fun x => (x + 1) % 256) |>.map UInt8.ofNat |>.toArray)
    
    let ciphertext1 ← easy ctx message nonce1 secretKey
    let ciphertext2 ← easy ctx message nonce2 secretKey
    
    if ciphertext1 != ciphertext2 then
      IO.println "✓ Different nonces produce different ciphertexts (semantic security)"
    else
      IO.println "✗ Different nonces should produce different ciphertexts"
  catch e =>
    IO.println s!"✗ Nonce uniqueness test failed: {e}"

-- Test that different keys produce different ciphertexts
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey1 ← keygen ctx
    let secretKey2 ← keygen ctx
    
    let message := "Key uniqueness test".toUTF8
    let nonce := ByteArray.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    
    let ciphertext1 ← easy ctx message nonce secretKey1
    let ciphertext2 ← easy ctx message nonce secretKey2
    
    if ciphertext1 != ciphertext2 then
      IO.println "✓ Different keys produce different ciphertexts"
    else
      IO.println "✗ Different keys should produce different ciphertexts"
  catch e =>
    IO.println s!"✗ Key uniqueness test failed: {e}"

-- Test multiple consecutive operations
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey ← keygen ctx
    
    let mut success_count := 0
    for i in [0:10] do
      try
        let message := s!"Message {i}".toUTF8
        let nonce := ByteArray.mk (List.range NONCEBYTES |>.map (fun x => (x + i) % 256) |>.map UInt8.ofNat |>.toArray)
        
        let ciphertext ← easy ctx message nonce secretKey
        let decrypted ← openEasy ctx ciphertext nonce secretKey
        
        if decrypted == message then
          success_count := success_count + 1
      catch _ =>
        continue
    
    IO.println s!"✓ Multiple consecutive operations: {success_count}/10 succeeded"
  catch e =>
    IO.println s!"✗ Multiple consecutive operations failed: {e}"

-- Test large message encryption (stress test)
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey ← keygen ctx
    
    -- Create a 1KB message
    let largeMessage := ByteArray.mk (List.range 1024 |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    let nonce := ByteArray.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    
    let ciphertext ← easy ctx largeMessage nonce secretKey
    let decrypted ← openEasy ctx ciphertext nonce secretKey
    
    if decrypted == largeMessage then
      IO.println "✓ Large message (1KB) encryption/decryption succeeded"
    else
      IO.println "✗ Large message (1KB) encryption/decryption failed"
      
  catch e =>
    IO.println s!"✗ Large message encryption/decryption failed: {e}"

-- Test deterministic behavior with same inputs
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey ← keygen ctx
    
    let message := "Deterministic test".toUTF8
    let nonce := ByteArray.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    
    let ciphertext1 ← easy ctx message nonce secretKey
    let ciphertext2 ← easy ctx message nonce secretKey
    
    if ciphertext1 == ciphertext2 then
      IO.println "✓ Encryption is deterministic with same key, nonce, and message"
    else
      IO.println "✗ Encryption should be deterministic with same inputs"
  catch e =>
    IO.println s!"✗ Deterministic behavior test failed: {e}"

-- Test key generation produces different keys each time
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey1 ← keygen ctx
    let secretKey2 ← keygen ctx
    
    -- We can't directly compare SecureArray contents, but we can test
    -- that they produce different ciphertexts with the same input
    let message := "Key randomness test".toUTF8
    let nonce := ByteArray.mk (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
    
    let ciphertext1 ← easy ctx message nonce secretKey1
    let ciphertext2 ← easy ctx message nonce secretKey2
    
    if ciphertext1 != ciphertext2 then
      IO.println "✓ Key generation produces unique keys (different ciphertexts)"
    else
      IO.println "? Key generation might not be sufficiently random (same ciphertext)"
  catch e =>
    IO.println s!"✗ Key randomness test failed: {e}"

#eval IO.println "\n=== SecretBox FFI Tests Complete ==="

end Sodium.Tests.SecretBoxFFI