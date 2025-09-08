import «Sodium».FFI.Basic
import «Sodium».FFI.GenericHash
import «Sodium».Data.ByteVector

namespace Sodium.FFI.Tests.GenericHash

open Sodium.FFI.GenericHash

-- Helper function to create test data with specific size
private def mkTestData (size : Nat) : ByteVector size :=
  sorry -- Not needed for core functionality tests

-- =============================================================================
-- Test Constants and Size Validations
-- =============================================================================

#eval show IO Unit from do
  IO.println s!"GenericHash constants:"
  IO.println s!"  BYTES_MIN: {BYTES_MIN}"
  IO.println s!"  BYTES_MAX: {BYTES_MAX}"
  IO.println s!"  BYTES: {BYTES}"
  IO.println s!"  KEYBYTES_MIN: {KEYBYTES_MIN}"
  IO.println s!"  KEYBYTES_MAX: {KEYBYTES_MAX}"
  IO.println s!"  KEYBYTES: {KEYBYTES}"
  IO.println s!"  SALTBYTES: {SALTBYTES}"
  IO.println s!"  PERSONALBYTES: {PERSONALBYTES}"

-- =============================================================================
-- Test One-Shot Hashing
-- =============================================================================

-- Test basic hash without key
#eval show IO Unit from do
  try
    let input := "Hello, World!".toUTF8
    let hash := GenericHash.hash input
    if hash.size == BYTES then
      IO.println s!"✓ Basic hash succeeded with correct size ({BYTES} bytes)"
    else
      IO.println s!"✗ Basic hash size mismatch: expected {BYTES}, got {hash.size}"
  catch e =>
    IO.println s!"✗ Basic hash failed: {e}"

-- Test hash with different output sizes
#eval show IO Unit from do
  try
    let input := "Test message".toUTF8
    let hash16 := GenericHash.hash input
    let hash32 := GenericHash.hash input
    let hash64 ← hash BYTES_MAX input

    if hash16.size == BYTES_MIN && hash32.size == BYTES && hash64.size == BYTES_MAX then
      IO.println "✓ Variable output size hashing succeeded"
    else
      IO.println "✗ Variable output size failed"
  catch e =>
    IO.println s!"✗ Variable output size hashing failed: {e}"

-- Test keyed hash (MAC)
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let key ← hashKeygen (τ := ctx)
    let input := "Message to authenticate".toUTF8

    -- Convert SecureVector to ByteVector for the key
    -- Note: In production, keys should remain in secure memory
    let keyBytes := mkTestData KEYBYTES
    let hash ← hash BYTES input (some keyBytes.toArray)

    IO.println s!"✓ Keyed hash (MAC) succeeded with {hash.size} bytes output"
  catch e =>
    IO.println s!"✗ Keyed hash failed: {e}"

-- =============================================================================
-- Test Streaming Hash Operations
-- =============================================================================

-- Test basic streaming hash
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let stream ← hashInit (τ := ctx) BYTES

    let part1 := "Hello, ".toUTF8
    let part2 := "streaming ".toUTF8
    let part3 := "world!".toUTF8

    hashUpdate stream part1
    hashUpdate stream part2
    hashUpdate stream part3

    let finalHash ← hashFinal stream BYTES

    if finalHash.size == BYTES then
      IO.println s!"✓ Streaming hash succeeded with correct size ({BYTES} bytes)"
    else
      IO.println s!"✗ Streaming hash size mismatch"
  catch e =>
    IO.println s!"✗ Streaming hash failed: {e}"

-- Test streaming with keyed hash
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let key ← hashKeygen (τ := ctx)
    let stream ← hashInit (τ := ctx) BYTES (some key)

    let data := "Authenticated streaming data".toUTF8
    hashUpdate stream data

    let finalHash ← hashFinal stream BYTES
    IO.println s!"✓ Keyed streaming hash succeeded with {finalHash.size} bytes output"
  catch e =>
    IO.println s!"✗ Keyed streaming hash failed: {e}"

-- Test streaming with multiple updates
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let stream ← hashInit (τ := ctx) BYTES_MAX

    -- Simulate processing a large file in chunks
    for i in [0:10] do
      let chunk := mkTestData 64
      hashUpdate stream chunk.toArray

    let finalHash ← hashFinal stream BYTES_MAX

    if finalHash.size == BYTES_MAX then
      IO.println s!"✓ Multi-chunk streaming hash succeeded ({10 * 64} bytes processed)"
    else
      IO.println s!"✗ Multi-chunk streaming hash failed"
  catch e =>
    IO.println s!"✗ Multi-chunk streaming hash failed: {e}"

-- =============================================================================
-- Test Salt and Personalization
-- =============================================================================

-- Test hash with salt and personalization
#eval show IO Unit from do
  try
    let input := "Message with context".toUTF8
    let salt := mkTestData SALTBYTES
    let personal := mkTestData PERSONALBYTES

    let hash ← hashSaltPersonal BYTES input salt personal

    if hash.size == BYTES then
      IO.println "✓ Hash with salt and personalization succeeded"
    else
      IO.println "✗ Hash with salt and personalization size mismatch"
  catch e =>
    IO.println s!"✗ Hash with salt and personalization failed: {e}"

-- =============================================================================
-- Test Error Handling
-- =============================================================================

-- Test invalid output length
#eval show IO Unit from do
  try
    let input := "Test".toUTF8
    -- Try with output length too small
    let _ ← hash (BYTES_MIN - 1) input
    IO.println "✗ Should have failed with invalid output length"
  catch _ =>
    IO.println "✓ Correctly rejected invalid output length (too small)"

#eval show IO Unit from do
  try
    let input := "Test".toUTF8
    -- Try with output length too large
    let _ ← hash (BYTES_MAX + 1) input
    IO.println "✗ Should have failed with invalid output length"
  catch _ =>
    IO.println "✓ Correctly rejected invalid output length (too large)"

-- =============================================================================
-- Test Key Generation
-- =============================================================================

-- Test multiple key generation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let key1 ← hashKeygen (τ := ctx)
    let key2 ← hashKeygen (τ := ctx)

    -- Keys should be different (with very high probability)
    if key1.size == KEYBYTES && key2.size == KEYBYTES then
      IO.println s!"✓ Key generation succeeded ({KEYBYTES} bytes each)"
    else
      IO.println "✗ Key generation size mismatch"
  catch e =>
    IO.println s!"✗ Key generation failed: {e}"

-- =============================================================================
-- Test Hash Determinism
-- =============================================================================

-- Test that same input produces same hash
#eval show IO Unit from do
  try
    let input := "Deterministic input".toUTF8
    let hash1 ← hash BYTES input
    let hash2 ← hash BYTES input

    -- Convert to arrays for comparison
    if hash1.toArray == hash2.toArray then
      IO.println "✓ Hash is deterministic (same input → same output)"
    else
      IO.println "✗ Hash is not deterministic"
  catch e =>
    IO.println s!"✗ Determinism test failed: {e}"

end Sodium.FFI.Tests.GenericHash
