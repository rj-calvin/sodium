import «Sodium».FFI.ShortHash
import «Sodium».FFI.Basic

open Sodium.FFI

namespace Sodium.Tests.ShortHash

def testShortHashKeygen : IO Unit := do
  try
    let key ← shortHashKeygen
    if key.size == 16 then
      IO.println "✓ Short hash keygen generated 16-byte key"
    else
      IO.println ("✗ Short hash keygen key size: expected 16, got " ++ toString key.size)
  catch e =>
    IO.println ("✗ Short hash keygen failed: " ++ toString e)

def testShortHash : IO Unit := do
  try
    let key ← shortHashKeygen
    let message := "Hello, SipHash-2-4!".toUTF8
    let hash ← shortHash message key
    
    if hash.size == 8 then
      IO.println "✓ Short hash generated 8-byte hash"
    else
      IO.println ("✗ Short hash size: expected 8, got " ++ toString hash.size)
  catch e =>
    IO.println ("✗ Short hash computation failed: " ++ toString e)

def testShortHashConsistency : IO Unit := do
  try
    let keyBytes := #[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 
                     0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10]
    let key := ByteArray.mk keyBytes
    let message := "consistent test message".toUTF8
    
    let hash1 ← shortHash message key
    let hash2 ← shortHash message key
    
    let consistent := hash1.toList == hash2.toList
    if consistent then
      IO.println "✓ Short hash is deterministic with same key and message"
    else
      IO.println "✗ Short hash should be deterministic with same inputs"
  catch e =>
    IO.println ("✗ Short hash consistency test failed: " ++ toString e)

def testShortHashDifferentKeys : IO Unit := do
  try
    let key1 ← shortHashKeygen
    let key2 ← shortHashKeygen
    let message := "test message for different keys".toUTF8
    
    let hash1 ← shortHash message key1
    let hash2 ← shortHash message key2
    
    let different := hash1.toList != hash2.toList
    if different then
      IO.println "✓ Short hash produces different outputs with different keys"
    else
      IO.println "✗ Short hash should produce different outputs with different keys"
  catch e =>
    IO.println ("✗ Short hash different keys test failed: " ++ toString e)

def testShortHashx24 : IO Unit := do
  try
    let key ← shortHashKeygen
    let message := "Hello, SipHashx-2-4!".toUTF8
    let hash ← shortHashx24 message key
    
    if hash.size == 16 then
      IO.println "✓ SipHashx-2-4 generated 16-byte hash"
    else
      IO.println ("✗ SipHashx-2-4 hash size: expected 16, got " ++ toString hash.size)
  catch e =>
    IO.println ("✗ SipHashx-2-4 computation failed: " ++ toString e)

def testShortHashInvalidKey : IO Unit := do
  let invalidKey := "short".toUTF8
  let message := "test message".toUTF8
  
  -- Test short hash with invalid key
  try
    let _ ← shortHash message invalidKey
    IO.println "✗ Should have failed with invalid key size"
  catch _ =>
    IO.println "✓ Correctly rejected invalid key size for short hash"
  
  -- Test SipHashx-2-4 with invalid key
  try
    let _ ← shortHashx24 message invalidKey
    IO.println "✗ Should have failed with invalid key size"
  catch _ =>
    IO.println "✓ Correctly rejected invalid key size for SipHashx-2-4"

def testEmptyMessage : IO Unit := do
  try
    let key ← shortHashKeygen
    let emptyMessage := ByteArray.empty
    let hash ← shortHash emptyMessage key
    
    if hash.size == 8 then
      IO.println "✓ Short hash handles empty message correctly"
    else
      IO.println ("✗ Short hash with empty message size: expected 8, got " ++ toString hash.size)
  catch e =>
    IO.println ("✗ Short hash with empty message failed: " ++ toString e)

def runAllTests : IO Unit := do
  IO.println "=== Short Hash FFI Tests ==="
  testShortHashKeygen
  testShortHash
  testShortHashConsistency
  testShortHashDifferentKeys
  testShortHashx24
  testShortHashInvalidKey
  testEmptyMessage
  IO.println ""

end Sodium.Tests.ShortHash