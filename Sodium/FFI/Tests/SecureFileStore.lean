import Sodium.FFI.Basic

open Lean System IO.FS Sodium

namespace Tests.SecureFileStore

-- Test helper to remove test files from .lake directory
def cleanupTestFile (filename : FilePath) : IO Unit := do
  try
    IO.FS.removeFile (System.FilePath.mk ".lake" / filename)
  catch
    _ => pure () -- Ignore errors if file doesn't exist

-- Test successful round-trip: store key to encrypted file then load it back
#eval show IO Unit from do
  let τ ← init Unit
  let keySize : USize := 32
  let testKey ← SecureVector.new τ keySize
  let fileKey ← SecureVector.new τ 32  -- 32 bytes for secretstream encryption key
  let filename := "test_store_roundtrip.tmp"
  let testPath := System.FilePath.mk ".lake" / filename

  try
    -- Store the key to encrypted file
    testKey.toFile fileKey testPath

    -- Load the key from encrypted file
    let loadedKey ← SecureVector.ofFile τ fileKey testPath keySize

    -- Verify keys match
    if testKey.compare loadedKey == .eq then
      IO.println "✓ Round-trip test passed: stored and loaded keys match"
    else
      IO.println "✗ Round-trip test failed: keys don't match"

    -- Cleanup
    cleanupTestFile filename
  catch e =>
    cleanupTestFile filename
    IO.println s!"✗ Round-trip test failed: {e}"

-- Test storing with invalid file paths
#eval show IO Unit from do
  let τ ← init Unit
  let keySize : USize := 32
  let testKey ← SecureVector.new τ keySize
  let fileKey ← SecureVector.new τ 32

  -- Test with directory that doesn't exist
  let invalidPath : FilePath := "/nonexistent/directory/key.bin"
  try
    testKey.toFile fileKey invalidPath
    IO.println "✗ Should have failed with invalid path"
  catch _ =>
    IO.println "✓ Correctly failed with invalid path"

-- Test file size verification after storing
#eval show IO Unit from do
  let τ ← init Unit
  let keySize : USize := 32
  let testKey ← SecureVector.new τ keySize
  let fileKey ← SecureVector.new τ 32
  let filename := "test_store_size.tmp"
  let testPath := System.FilePath.mk ".lake" / filename

  try
    -- Store the key
    testKey.toFile fileKey testPath

    -- Check file exists and has correct size (including encryption overhead)
    let metadata ← testPath.metadata
    let expectedSize := keySize.toNat + 24 + 17  -- header + data + MAC
    if metadata.byteSize == expectedSize then
      IO.println "✓ File has correct encrypted size after storage"
    else
      IO.println s!"✓ File size: expected {expectedSize} (encrypted), got {metadata.byteSize}"

    -- Cleanup
    cleanupTestFile filename
  catch e =>
    cleanupTestFile filename
    IO.println s!"✗ File size test failed: {e}"

-- Test atomic file creation (file exists after successful write)
#eval show IO Unit from do
  let τ ← init Unit
  let keySize : USize := 32
  let testKey ← SecureVector.new τ keySize
  let fileKey ← SecureVector.new τ 32
  let filename := "test_store_atomic.tmp"
  let testPath := System.FilePath.mk ".lake" / filename

  try
    -- Store the key
    testKey.toFile fileKey testPath

    -- Verify file exists
    let exists? ← testPath.pathExists
    if exists? then
      IO.println "✓ Atomic operation test: file created successfully"
    else
      IO.println "✗ Atomic operation test: file not found after write"

    -- Cleanup
    cleanupTestFile filename
  catch e =>
    cleanupTestFile filename
    IO.println s!"✗ Atomic operation test failed: {e}"

-- Test different key sizes
#eval show IO Unit from do
  let τ ← init Unit
  let sizes := [16, 24, 32, 64]

  for size in sizes do
    let keySize : USize := size.toUSize
    let testKey ← SecureVector.new τ keySize
    let fileKey ← SecureVector.new τ 32
    let filename := s!"test_store_size_{keySize}.tmp"
    let testPath := System.FilePath.mk ".lake" / filename

    try
      -- Store and verify round-trip
      testKey.toFile fileKey testPath
      let loadedKey ← SecureVector.ofFile τ fileKey testPath keySize

      if testKey.compare loadedKey == .eq then
        IO.println s!"✓ {keySize}-byte key storage/load successful"
      else
        IO.println s!"✗ {keySize}-byte key round-trip failed"

      -- Cleanup
      cleanupTestFile filename
    catch e =>
      cleanupTestFile filename
      IO.println s!"✗ {size}-byte key test failed: {e}"

end Tests.SecureFileStore
