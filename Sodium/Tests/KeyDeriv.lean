import «Sodium».FFI.KeyDeriv
import «Sodium».FFI.Basic

namespace Sodium.Tests.KeyDeriv

def testKdfKeygen : IO Unit := do
  try
    let key ← Sodium.FFI.KeyDeriv.kdfKeygen
    if key.size == 32 then
      IO.println "✓ KDF keygen generated 32-byte key"
    else
      IO.println ("✗ KDF keygen key size: expected 32, got " ++ toString key.size)
  catch e =>
    IO.println ("✗ KDF keygen failed: " ++ toString e)

def testKdfDeriveFromKey : IO Unit := do
  try
    let masterKey ← Sodium.FFI.KeyDeriv.kdfKeygen
    let context := "testctx\x00".toUTF8
    let subkey1 ← Sodium.FFI.KeyDeriv.kdfDeriveFromKey 32 1 context masterKey
    let subkey2 ← Sodium.FFI.KeyDeriv.kdfDeriveFromKey 32 2 context masterKey
    
    if subkey1.size == 32 && subkey2.size == 32 then
      -- ByteArray comparison needs manual implementation
      let different := subkey1.toList != subkey2.toList
      if different then
        IO.println "✓ KDF derive from key generates different subkeys for different IDs"
      else
        IO.println "✗ KDF derive from key generated identical subkeys for different IDs"
    else
      IO.println ("✗ KDF derive from key subkey sizes: expected 32, got " ++ toString subkey1.size ++ " and " ++ toString subkey2.size)
  catch e =>
    IO.println ("✗ KDF derive from key failed: " ++ toString e)

def testHkdfSha256 : IO Unit := do
  try
    let prk ← Sodium.FFI.KeyDeriv.hkdfSha256Keygen
    let salt := "salt".toUTF8
    let ikm := "input key material".toUTF8
    let context := "test context".toUTF8
    
    let extractedPrk ← Sodium.FFI.KeyDeriv.hkdfSha256Extract salt ikm
    let expandedKey ← Sodium.FFI.KeyDeriv.hkdfSha256Expand 32 context extractedPrk
    
    if prk.size == 32 && extractedPrk.size == 32 && expandedKey.size == 32 then
      IO.println "✓ HKDF-SHA256 extract/expand working correctly"
    else
      IO.println ("✗ HKDF-SHA256 key sizes: PRK " ++ toString prk.size ++ ", extracted " ++ toString extractedPrk.size ++ ", expanded " ++ toString expandedKey.size)
  catch e =>
    IO.println ("✗ HKDF-SHA256 failed: " ++ toString e)

def testHkdfSha512 : IO Unit := do
  try
    let prk ← Sodium.FFI.KeyDeriv.hkdfSha512Keygen
    let salt := "salt512".toUTF8
    let ikm := "input key material 512".toUTF8
    let context := "test context 512".toUTF8
    
    let extractedPrk ← Sodium.FFI.KeyDeriv.hkdfSha512Extract salt ikm
    let expandedKey ← Sodium.FFI.KeyDeriv.hkdfSha512Expand 64 context extractedPrk
    
    if prk.size == 64 && extractedPrk.size == 64 && expandedKey.size == 64 then
      IO.println "✓ HKDF-SHA512 extract/expand working correctly"
    else
      IO.println ("✗ HKDF-SHA512 key sizes: PRK " ++ toString prk.size ++ ", extracted " ++ toString extractedPrk.size ++ ", expanded " ++ toString expandedKey.size)
  catch e =>
    IO.println ("✗ HKDF-SHA512 failed: " ++ toString e)

def testInvalidInputs : IO Unit := do
  let validKey ← Sodium.FFI.KeyDeriv.kdfKeygen
  let invalidKey := "short".toUTF8
  let validContext := "testctx\x00".toUTF8
  let invalidContext := "short".toUTF8
  
  -- Test invalid key size
  try
    let _ ← Sodium.FFI.KeyDeriv.kdfDeriveFromKey 32 1 validContext invalidKey
    IO.println "✗ Should have failed with invalid key size"
  catch _ =>
    IO.println "✓ Correctly rejected invalid key size"
  
  -- Test invalid context size
  try
    let _ ← Sodium.FFI.KeyDeriv.kdfDeriveFromKey 32 1 invalidContext validKey
    IO.println "✗ Should have failed with invalid context size"
  catch _ =>
    IO.println "✓ Correctly rejected invalid context size"
  
  -- Test invalid output length
  try
    let _ ← Sodium.FFI.KeyDeriv.kdfDeriveFromKey 100 1 validContext validKey
    IO.println "✗ Should have failed with invalid output length"
  catch _ =>
    IO.println "✓ Correctly rejected invalid output length"

def runAllTests : IO Unit := do
  IO.println "=== Key Derivation FFI Tests ==="
  testKdfKeygen
  testKdfDeriveFromKey
  testHkdfSha256
  testHkdfSha512
  testInvalidInputs
  IO.println ""

end Sodium.Tests.KeyDeriv