import «Sodium».FFI.Auth
import «Sodium».FFI.Basic

namespace Sodium.Tests.Auth

def testAuthKeygen : IO Unit := do
  try
    let key ← Sodium.FFI.Auth.authKeygen
    if key.size == 32 then
      IO.println "✓ Auth keygen generated 32-byte key"
    else
      IO.println ("✗ Auth keygen key size: expected 32, got " ++ toString key.size)
  catch e =>
    IO.println ("✗ Auth keygen failed: " ++ toString e)

def testAuth : IO Unit := do
  try
    let key ← Sodium.FFI.Auth.authKeygen
    let message := "Hello, HMAC-SHA512-256!".toUTF8
    let mac ← Sodium.FFI.Auth.auth message key
    
    if mac.size == 32 then
      IO.println "✓ Auth generated 32-byte MAC"
    else
      IO.println ("✗ Auth MAC size: expected 32, got " ++ toString mac.size)
  catch e =>
    IO.println ("✗ Auth computation failed: " ++ toString e)

def testAuthVerify : IO Unit := do
  try
    let key ← Sodium.FFI.Auth.authKeygen
    let message := "Test message for verification".toUTF8
    let mac ← Sodium.FFI.Auth.auth message key
    
    -- Test valid MAC verification
    let validResult ← Sodium.FFI.Auth.authVerify mac message key
    if validResult then
      IO.println "✓ Auth verification succeeded for valid MAC"
    else
      IO.println "✗ Auth verification failed for valid MAC"
    
    -- Test invalid MAC verification
    let invalidMac := ByteArray.mk #[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                                    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
                                    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
                                    0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f]
    let invalidResult ← Sodium.FFI.Auth.authVerify invalidMac message key
    if not invalidResult then
      IO.println "✓ Auth verification correctly rejected invalid MAC"
    else
      IO.println "✗ Auth verification should have rejected invalid MAC"
  catch e =>
    IO.println ("✗ Auth verification test failed: " ++ toString e)

def testHmacSha256 : IO Unit := do
  try
    let key ← Sodium.FFI.Auth.hmacSha256Keygen
    let message := "Hello, HMAC-SHA256!".toUTF8
    let mac ← Sodium.FFI.Auth.hmacSha256 message key
    
    if mac.size == 32 then
      -- Test verification
      let verified ← Sodium.FFI.Auth.hmacSha256Verify mac message key
      if verified then
        IO.println "✓ HMAC-SHA256 computation and verification working"
      else
        IO.println "✗ HMAC-SHA256 verification failed"
    else
      IO.println ("✗ HMAC-SHA256 MAC size: expected 32, got " ++ toString mac.size)
  catch e =>
    IO.println ("✗ HMAC-SHA256 test failed: " ++ toString e)

def testHmacSha512 : IO Unit := do
  try
    let key ← Sodium.FFI.Auth.hmacSha512Keygen
    let message := "Hello, HMAC-SHA512!".toUTF8
    let mac ← Sodium.FFI.Auth.hmacSha512 message key
    
    if mac.size == 64 then
      -- Test verification
      let verified ← Sodium.FFI.Auth.hmacSha512Verify mac message key
      if verified then
        IO.println "✓ HMAC-SHA512 computation and verification working"
      else
        IO.println "✗ HMAC-SHA512 verification failed"
    else
      IO.println ("✗ HMAC-SHA512 MAC size: expected 64, got " ++ toString mac.size)
  catch e =>
    IO.println ("✗ HMAC-SHA512 test failed: " ++ toString e)

def testAuthDeterministic : IO Unit := do
  try
    let keyBytes := #[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                     0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10,
                     0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
                     0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20]
    let key := ByteArray.mk keyBytes
    let message := "deterministic test message".toUTF8
    
    let mac1 ← Sodium.FFI.Auth.auth message key
    let mac2 ← Sodium.FFI.Auth.auth message key
    
    let consistent := mac1.toList == mac2.toList
    if consistent then
      IO.println "✓ Auth is deterministic with same key and message"
    else
      IO.println "✗ Auth should be deterministic with same inputs"
  catch e =>
    IO.println ("✗ Auth deterministic test failed: " ++ toString e)

def testAuthDifferentKeys : IO Unit := do
  try
    let key1 ← Sodium.FFI.Auth.authKeygen
    let key2 ← Sodium.FFI.Auth.authKeygen
    let message := "test message for different keys".toUTF8
    
    let mac1 ← Sodium.FFI.Auth.auth message key1
    let mac2 ← Sodium.FFI.Auth.auth message key2
    
    let different := mac1.toList != mac2.toList
    if different then
      IO.println "✓ Auth produces different MACs with different keys"
    else
      IO.println "✗ Auth should produce different MACs with different keys"
  catch e =>
    IO.println ("✗ Auth different keys test failed: " ++ toString e)

def testInvalidInputs : IO Unit := do
  let invalidKey := "short".toUTF8
  let validMessage := "test message".toUTF8
  
  -- Test auth with invalid key
  try
    let _ ← Sodium.FFI.Auth.auth validMessage invalidKey
    IO.println "✗ Should have failed with invalid key size"
  catch _ =>
    IO.println "✓ Correctly rejected invalid key size for auth"
  
  -- Test HMAC-SHA256 with invalid key
  try
    let _ ← Sodium.FFI.Auth.hmacSha256 validMessage invalidKey
    IO.println "✗ Should have failed with invalid key size"
  catch _ =>
    IO.println "✓ Correctly rejected invalid key size for HMAC-SHA256"
  
  -- Test HMAC-SHA512 with invalid key
  try
    let _ ← Sodium.FFI.Auth.hmacSha512 validMessage invalidKey
    IO.println "✗ Should have failed with invalid key size"
  catch _ =>
    IO.println "✓ Correctly rejected invalid key size for HMAC-SHA512"

def testEmptyMessage : IO Unit := do
  try
    let key ← Sodium.FFI.Auth.authKeygen
    let emptyMessage := ByteArray.empty
    let mac ← Sodium.FFI.Auth.auth emptyMessage key
    
    if mac.size == 32 then
      let verified ← Sodium.FFI.Auth.authVerify mac emptyMessage key
      if verified then
        IO.println "✓ Auth handles empty message correctly"
      else
        IO.println "✗ Auth verification failed for empty message"
    else
      IO.println ("✗ Auth with empty message MAC size: expected 32, got " ++ toString mac.size)
  catch e =>
    IO.println ("✗ Auth with empty message failed: " ++ toString e)

def runAllTests : IO Unit := do
  IO.println "=== Authentication FFI Tests ==="
  testAuthKeygen
  testAuth
  testAuthVerify
  testHmacSha256
  testHmacSha512
  testAuthDeterministic
  testAuthDifferentKeys
  testInvalidInputs
  testEmptyMessage
  IO.println ""

end Sodium.Tests.Auth