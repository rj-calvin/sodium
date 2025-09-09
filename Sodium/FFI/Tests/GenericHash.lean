import «Sodium».FFI.Basic
import «Sodium».FFI.GenericHash
import «Sodium».Data.ByteVector

namespace Sodium.FFI.Tests.GenericHash

open Sodium.FFI.GenericHash

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
    let hash64 := GenericHash.hash input

    if hash16.size == BYTES_MIN && hash32.size == BYTES && hash64.size == BYTES_MAX then
      IO.println "✓ Variable output size hashing succeeded"
    else
      IO.println "✗ Variable output size failed"
  catch e =>
    IO.println s!"✗ Variable output size hashing failed: {e}"

-- -- Test keyed hash (MAC)
-- #eval show IO Unit from do
--   try
--     let ctx ← Sodium.init Unit
--     let key ← hashKeygen (τ := ctx)
--     let input := "Message to authenticate".toUTF8

--     -- Convert SecureVector to ByteVector for the key
--     -- Note: In production, keys should remain in secure memory
--     let hash := GenericHash.hash input (some key.cast)

--     IO.println s!"✓ Keyed hash (MAC) succeeded with {hash.size} bytes output"
--   catch e =>
--     IO.println s!"✗ Keyed hash failed: {e}"

-- =============================================================================
-- Test Streaming Hash Operations
-- =============================================================================

-- Test basic streaming hash
#eval show IO Unit from do
  try
    let part1 := "Hello, ".toUTF8
    let part2 := "streaming ".toUTF8
    let part3 := "world!".toUTF8

    let mut stream := hashInit
    stream := hashUpdate stream part1
    stream := hashUpdate stream part2
    stream := hashUpdate stream part3

    let finalHash := hashFinal stream

    if finalHash.size == BYTES then
      IO.println s!"✓ Streaming hash succeeded with correct size ({BYTES} bytes)"
    else
      IO.println s!"✗ Streaming hash size mismatch"
  catch e =>
    IO.println s!"✗ Streaming hash failed: {e}"

-- -- Test streaming with keyed hash
-- #eval show IO Unit from do
--   try
--     let ctx ← Sodium.init Unit
--     let key ← hashKeygen (τ := ctx)
--     let stream ← hashInit (τ := ctx) BYTES (some key)

--     let data := "Authenticated streaming data".toUTF8
--     hashUpdate stream data

--     let finalHash ← hashFinal stream BYTES
--     IO.println s!"✓ Keyed streaming hash succeeded with {finalHash.size} bytes output"
--   catch e =>
--     IO.println s!"✗ Keyed streaming hash failed: {e}"

-- =============================================================================
-- Test Salt and Personalization
-- =============================================================================

-- Test hash with salt and personalization
#eval show IO Unit from do
  try
    let input := "Message with context".toUTF8
    let salt := default
    let personal := default

    let hash := hashCustom BYTES (by native_decide) input salt personal

    if hash.size == BYTES then
      IO.println "✓ Hash with salt and personalization succeeded"
    else
      IO.println "✗ Hash with salt and personalization size mismatch"
  catch e =>
    IO.println s!"✗ Hash with salt and personalization failed: {e}"

end Sodium.FFI.Tests.GenericHash
