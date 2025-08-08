import «Sodium».FFI.Deprecated.Stream
import «Sodium».FFI.Basic

open Sodium.FFI

namespace Sodium.Tests.Stream

def testStreamKeygen : IO Unit := do
  try
    let key ← streamKeygen
    if key.size == 32 then
      IO.println "✓ Stream keygen generated 32-byte key"
    else
      IO.println (s!"✗ Stream keygen key size: expected 32, got {key.size}")
  catch e =>
    IO.println (s!"✗ Stream keygen failed: {e}")

def testStreamCiphers : IO Unit := do
  try
    let key ← streamKeygen
    let nonceBytes := #[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                       0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10,
                       0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18]
    let nonce := ByteArray.mk nonceBytes
    let message := "Hello, Stream Ciphers!".toUTF8
    
    let ciphertext ← streamXor message nonce key
    let decrypted ← streamXor ciphertext nonce key
    
    if decrypted.toList == message.toList then
      IO.println "✓ Default stream cipher encryption/decryption working"
    else
      IO.println "✗ Default stream cipher failed to decrypt correctly"
  catch e =>
    IO.println (s!"✗ Default stream cipher test failed: {e}")

def testChaCha20 : IO Unit := do
  try
    let key ← chacha20Keygen
    let nonceBytes := #[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]
    let nonce := ByteArray.mk nonceBytes
    let message := "ChaCha20 test message".toUTF8
    
    let ciphertext ← chacha20Xor message nonce key
    let decrypted ← chacha20Xor ciphertext nonce key
    
    if decrypted.toList == message.toList then
      IO.println "✓ ChaCha20 encryption/decryption working"
    else
      IO.println "✗ ChaCha20 failed to decrypt correctly"
  catch e =>
    IO.println (s!"✗ ChaCha20 test failed: {e}")

def testChaCha20Ietf : IO Unit := do
  try
    let key ← chacha20IetfKeygen
    let nonceBytes := #[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                       0x08, 0x09, 0x0a, 0x0b]
    let nonce := ByteArray.mk nonceBytes
    let message := "ChaCha20-IETF test message".toUTF8
    
    let ciphertext ← chacha20IetfXor message nonce key
    let decrypted ← chacha20IetfXor ciphertext nonce key
    
    if decrypted.toList == message.toList then
      IO.println "✓ ChaCha20-IETF encryption/decryption working"
    else
      IO.println "✗ ChaCha20-IETF failed to decrypt correctly"
  catch e =>
    IO.println (s!"✗ ChaCha20-IETF test failed: {e}")

def testSalsa20 : IO Unit := do
  try
    let key ← salsa20Keygen
    let nonceBytes := #[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]
    let nonce := ByteArray.mk nonceBytes
    let message := "Salsa20 test message".toUTF8
    
    let ciphertext ← salsa20Xor message nonce key
    let decrypted ← salsa20Xor ciphertext nonce key
    
    if decrypted.toList == message.toList then
      IO.println "✓ Salsa20 encryption/decryption working"
    else
      IO.println "✗ Salsa20 failed to decrypt correctly"
  catch e =>
    IO.println (s!"✗ Salsa20 test failed: {e}")

def testXChaCha20 : IO Unit := do
  try
    let key ← xchacha20Keygen
    let nonceBytes := #[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                       0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10,
                       0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18]
    let nonce := ByteArray.mk nonceBytes
    let message := "XChaCha20 test message".toUTF8
    
    let ciphertext ← xchacha20Xor message nonce key
    let decrypted ← xchacha20Xor ciphertext nonce key
    
    if decrypted.toList == message.toList then
      IO.println "✓ XChaCha20 encryption/decryption working"
    else
      IO.println "✗ XChaCha20 failed to decrypt correctly"
  catch e =>
    IO.println (s!"✗ XChaCha20 test failed: {e}")

def testXSalsa20 : IO Unit := do
  try
    let key ← xsalsa20Keygen
    let nonceBytes := #[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                       0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10,
                       0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18]
    let nonce := ByteArray.mk nonceBytes
    let message := "XSalsa20 test message".toUTF8
    
    let ciphertext ← xsalsa20Xor message nonce key
    let decrypted ← xsalsa20Xor ciphertext nonce key
    
    if decrypted.toList == message.toList then
      IO.println "✓ XSalsa20 encryption/decryption working"
    else
      IO.println "✗ XSalsa20 failed to decrypt correctly"
  catch e =>
    IO.println (s!"✗ XSalsa20 test failed: {e}")

def testStreamGeneration : IO Unit := do
  try
    let key ← streamKeygen
    let nonceBytes := #[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                       0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10,
                       0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18]
    let nonce := ByteArray.mk nonceBytes
    
    let stream1 ← stream 64 nonce key
    let stream2 ← stream 64 nonce key
    
    if stream1.size == 64 && stream2.size == 64 then
      if stream1.toList == stream2.toList then
        IO.println "✓ Stream generation is deterministic"
      else
        IO.println "✗ Stream generation should be deterministic"
    else
      IO.println (s!"✗ Stream generation size error: got {stream1.size}, {stream2.size}")
  catch e =>
    IO.println (s!"✗ Stream generation test failed: {e}")

def testCounterFunctions : IO Unit := do
  try
    let key ← chacha20Keygen
    let nonceBytes := #[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]
    let nonce := ByteArray.mk nonceBytes
    let message := "Counter test message".toUTF8
    
    let ciphertext1 ← chacha20XorIc message nonce 0 key
    let ciphertext2 ← chacha20XorIc message nonce 1 key
    
    if ciphertext1.toList != ciphertext2.toList then
      IO.println "✓ Counter functions produce different outputs"
    else
      IO.println "✗ Counter functions should produce different outputs"
  catch e =>
    IO.println (s!"✗ Counter function test failed: {e}")

def testInvalidInputs : IO Unit := do
  let shortKey := "short".toUTF8
  let shortNonce := "short".toUTF8
  let validMessage := "test message".toUTF8
  
  try
    let _ ← streamXor validMessage shortNonce shortKey
    IO.println "✗ Should have failed with invalid key/nonce size"
  catch _ =>
    IO.println "✓ Correctly rejected invalid key/nonce size"
  
  try
    let validKey ← streamKeygen
    let _ ← streamXor validMessage shortNonce validKey
    IO.println "✗ Should have failed with invalid nonce size"
  catch _ =>
    IO.println "✓ Correctly rejected invalid nonce size"

def runAllTests : IO Unit := do
  IO.println "=== Stream Cipher FFI Tests ==="
  testStreamKeygen
  testStreamCiphers
  testChaCha20
  testChaCha20Ietf
  testSalsa20
  testXChaCha20
  testXSalsa20
  testStreamGeneration
  testCounterFunctions
  testInvalidInputs
  IO.println ""

end Sodium.Tests.Stream