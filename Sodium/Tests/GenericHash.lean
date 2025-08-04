import Sodium.FFI.GenericHash
import Sodium.FFI.Basic

open Sodium.FFI

namespace Sodium.Tests.GenericHash

-- Import needed for sodium_init

-- Test 1: Basic initialization
def testInit : IO Unit := do
  let result ← sodiumInit
  if result = 0 then
    IO.println "✓ Test 1: Sodium init successful"
  else
    IO.println s!"✗ Test 1: Sodium init failed with code {result}"

-- Test 2: Simple constants access
def testConstants : IO Unit := do
  IO.println s!"✓ Test 2: Constants - GENERICHASH_BYTES: {GENERICHASH_BYTES}, GENERICHASH_BYTES_MIN: {GENERICHASH_BYTES_MIN}, GENERICHASH_BYTES_MAX: {GENERICHASH_BYTES_MAX}"

-- Test 3: Create ByteArray for testing
def testByteArrayCreation : IO Unit := do
  let message := "test".toUTF8
  IO.println s!"✓ Test 3: ByteArray created, size: {message.size}"

-- Test 4: Simple hash without key (most basic case)
def testBasicHash : IO Unit := do
  let _ ← sodiumInit
  let message := "test".toUTF8
  try
    let hash ← genericHash GENERICHASH_BYTES message none
    IO.println s!"✓ Test 4: Basic hash successful, size: {hash.size}"
  catch e =>
    IO.println s!"✗ Test 4: Basic hash failed: {e}"

-- Test 5: Hash with key
def testHashWithKey : IO Unit := do
  let _ ← sodiumInit
  let message := "test".toUTF8
  let key := "my-32-byte-key-exactly-this-len!".toUTF8
  try
    let hash ← genericHash GENERICHASH_BYTES message (some key)
    IO.println s!"✓ Test 5: Keyed hash successful, size: {hash.size}"
  catch e =>
    IO.println s!"✗ Test 5: Keyed hash failed: {e}"

-- Test 6: Streaming API - init only
def testStreamInit : IO Unit := do
  let _ ← sodiumInit
  try
    let _state ← init 0 GENERICHASH_BYTES none
    IO.println "✓ Test 6: Stream init successful"
  catch e =>
    IO.println s!"✗ Test 6: Stream init failed: {e}"

-- Test 7: Full streaming API
def testFullStream : IO Unit := do
  let _ ← sodiumInit
  try
    let state ← init 0 GENERICHASH_BYTES none
    let message := "test".toUTF8
    let _ ← update state message
    let hash ← final state GENERICHASH_BYTES
    IO.println s!"✓ Test 7: Full streaming successful, size: {hash.size}"
  catch e =>
    IO.println s!"✗ Test 7: Full streaming failed: {e}"

-- Progressive test runner
def runProgressiveTests : IO Unit := do
  IO.println "=== GenericHash Progressive Tests ==="
  testInit
  testConstants
  testByteArrayCreation
  testBasicHash
  testHashWithKey
  testStreamInit
  testFullStream
  IO.println "=== Tests Complete ==="

-- Individual test evaluations (uncomment one at a time to isolate issues)
-- #eval testInit
-- #eval testConstants
-- #eval testByteArrayCreation
-- #eval testBasicHash
-- #eval testHashWithKey
-- #eval testStreamInit
-- #eval testFullStream
#eval runProgressiveTests

end Sodium.Tests.GenericHash
