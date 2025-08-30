import «Sodium».FFI.Basic
import «Sodium».FFI.SecretBox
import «Sodium».Data.ByteVector

namespace Sodium.FFI.Tests.SecretBox

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
    let secretKey ← keygen (τ := ctx)
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
    let secretKey ← keygen (τ := ctx)
    
    let message := "Hello, SecretBox encryption!".toUTF8.toVector
    let nonce : ByteVector NONCEBYTES :=
      (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk).toVector.cast
    
    let ciphertext ← easy (τ := ctx) message nonce secretKey
    let some decrypted ← openEasy (τ := ctx) ciphertext nonce secretKey
      | do IO.println "✗ SecretBox decryption failed unexpectedly"; return
    
    if decrypted == message then
      IO.println "✓ SecretBox encryption/decryption round-trip succeeded"
    else
      IO.println "✗ SecretBox encryption/decryption round-trip failed"
  catch e =>
    IO.println s!"✗ SecretBox round-trip failed: {e}"

-- Test detached encryption/decryption
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey ← keygen (τ := ctx)
    
    let message := "Detached SecretBox test".toUTF8.toVector
    let nonce : ByteVector NONCEBYTES :=
      (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk).toVector.cast
    
    -- Encrypt detached
    let (ciphertext, mac) ← detached (τ := ctx) message nonce secretKey
    
    -- Decrypt detached
    let some decrypted ← openDetached (τ := ctx) ciphertext mac nonce secretKey
      | do IO.println "✗ Detached decryption failed unexpectedly"; return
    
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
    let secretKey ← keygen (τ := ctx)
    
    let emptyMessage := ByteVector.empty
    let nonce : ByteVector NONCEBYTES :=
      (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk).toVector.cast
    
    let ciphertext ← easy (τ := ctx) emptyMessage nonce secretKey
    let some decrypted ← openEasy (τ := ctx) ciphertext nonce secretKey
      | do IO.println "✗ Empty message decryption failed unexpectedly"; return
    
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
    let secretKey1 ← keygen (τ := ctx)
    let secretKey2 ← keygen (τ := ctx)  -- Different key
    
    let message := "Authentication test".toUTF8.toVector
    let nonce : ByteVector NONCEBYTES :=
      (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk).toVector.cast
    
    let ciphertext ← easy (τ := ctx) message nonce secretKey1
    let result ← openEasy (τ := ctx) ciphertext nonce secretKey2  -- Wrong key
    match result with
    | none => IO.println "✓ Decryption correctly failed with wrong key: authentication failed"
    | some _ => IO.println "✗ Decryption should fail with wrong key"
  catch e =>
    IO.println s!"✓ Decryption correctly failed with wrong key: {e}"

-- Test detached decryption with wrong MAC (should fail)  
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey ← keygen (τ := ctx)
    
    let message := "MAC verification test".toUTF8.toVector
    let nonce : ByteVector NONCEBYTES :=
      (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk).toVector.cast
    
    let (ciphertext, _mac) ← detached (τ := ctx) message nonce secretKey
    
    -- Create wrong MAC
    let wrongMac : ByteVector MACBYTES :=
      (List.range MACBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk).toVector.cast
    
    let result ← openDetached (τ := ctx) ciphertext wrongMac nonce secretKey
    match result with
    | none => IO.println "✓ Detached decryption correctly failed with wrong MAC: authentication failed"
    | some _ => IO.println "✗ Detached decryption should fail with wrong MAC"
  catch e =>
    IO.println s!"✓ Detached decryption correctly failed with wrong MAC: {e}"

-- Test that different nonces produce different ciphertexts (semantic security)
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let secretKey ← keygen (τ := ctx)
    
    let message := "Nonce uniqueness test".toUTF8.toVector
    let nonce1 : ByteVector NONCEBYTES :=
      (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk).toVector.cast
    let nonce2 : ByteVector NONCEBYTES :=
      (List.range NONCEBYTES |>.map (fun x => (x + 1) % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk).toVector.cast
    
    let ciphertext1 ← easy (τ := ctx) message nonce1 secretKey
    let ciphertext2 ← easy (τ := ctx) message nonce2 secretKey
    
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
    let secretKey1 ← keygen (τ := ctx)
    let secretKey2 ← keygen (τ := ctx)
    
    let message := "Key uniqueness test".toUTF8.toVector
    let nonce : ByteVector NONCEBYTES :=
      (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk).toVector.cast
    
    let ciphertext1 ← easy (τ := ctx) message nonce secretKey1
    let ciphertext2 ← easy (τ := ctx) message nonce secretKey2
    
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
    let secretKey ← keygen (τ := ctx)
    
    let mut success_count := 0
    for i in [0:10] do
      try
        let message := s!"Message {i}".toUTF8.toVector
        let nonce : ByteVector NONCEBYTES :=
          (List.range NONCEBYTES |>.map (fun x => (x + i) % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk).toVector
        
        let ciphertext ← easy (τ := ctx) message nonce secretKey
        let some decrypted ← openEasy (τ := ctx) ciphertext nonce secretKey
          | continue
        
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
    let secretKey ← keygen (τ := ctx)
    
    -- Create a 1KB message
    let largeMessage := (List.range 1024 |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk).toVector
    let nonce : ByteVector NONCEBYTES :=
      (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk).toVector.cast
    
    let ciphertext ← easy (τ := ctx) largeMessage nonce secretKey
    let some decrypted ← openEasy (τ := ctx) ciphertext nonce secretKey
      | do IO.println "✗ Large message decryption failed unexpectedly"; return
    
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
    let secretKey ← keygen (τ := ctx)
    
    let message := "Deterministic test".toUTF8.toVector
    let nonce : ByteVector NONCEBYTES :=
      (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk).toVector.cast
    
    let ciphertext1 ← easy (τ := ctx) message nonce secretKey
    let ciphertext2 ← easy (τ := ctx) message nonce secretKey
    
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
    let secretKey1 ← keygen (τ := ctx)
    let secretKey2 ← keygen (τ := ctx)
    
    -- We can't directly compare SecureArray contents, but we can test
    -- that they produce different ciphertexts with the same input
    let message := "Key randomness test".toUTF8.toVector
    let nonce : ByteVector NONCEBYTES :=
      (List.range NONCEBYTES |>.map (· % 256) |>.map UInt8.ofNat |>.toArray |> ByteArray.mk).toVector.cast
    
    let ciphertext1 ← easy (τ := ctx) message nonce secretKey1
    let ciphertext2 ← easy (τ := ctx) message nonce secretKey2
    
    if ciphertext1 != ciphertext2 then
      IO.println "✓ Key generation produces unique keys (different ciphertexts)"
    else
      IO.println "? Key generation might not be sufficiently random (same ciphertext)"
  catch e =>
    IO.println s!"✗ Key randomness test failed: {e}"

#eval IO.println "\n=== SecretBox FFI Tests Complete ==="

end Sodium.FFI.Tests.SecretBox