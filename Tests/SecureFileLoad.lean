import Sodium.FFI.Basic
import Sodium.Crypto.Spec

open Sodium.Crypto (Spec SecretKey)

open Lean System IO.FS Sodium

namespace Tests.SecureFileLoad

-- Test helper to remove test files
def cleanupTestFile (filename : FilePath) : IO Unit := do
  try
    IO.FS.removeFile (".lake" / filename)
  catch
    _ => pure () -- Ignore errors if file doesn't exist

-- Test successful key loading (encrypted file)
#eval show IO Unit from do
  let τ ← init Unit
  let keySize : USize := 32
  let testKey ← SecureArray.new τ keySize
  let fileKey ← SecureArray.new τ 32  -- 32 bytes for secretstream encryption key
  let filename := "test_encrypted_load.tmp"
  let testPath := System.FilePath.mk ".lake" / filename

  try
    -- Store the key to encrypted file first
    testKey.toFile fileKey testPath

    -- Load key from encrypted file
    let loadedKey ← SecureArray.ofFile τ fileKey testPath 32

    -- Verify size
    if loadedKey.size == 32 then
      IO.println "✓ Successfully loaded 32-byte key from encrypted file"
    else
      IO.println s!"✗ Key size mismatch: expected 32, got {loadedKey.size}"

    -- Verify keys match
    if testKey.compare loadedKey == .eq then
      IO.println "✓ Loaded key matches original"
    else
      IO.println "✗ Loaded key doesn't match original"

    -- Cleanup
    cleanupTestFile filename
  catch e =>
    cleanupTestFile filename
    IO.println s!"✗ Test failed: {e}"

-- Test file size mismatch error
#eval show IO Unit from do
  let τ ← init Unit
  let smallKeySize : USize := 8
  let testKey ← SecureArray.new τ smallKeySize
  let fileKey ← SecureArray.new τ 32
  let filename := "test_key_wrong_size.tmp"
  let testPath := System.FilePath.mk ".lake" / filename

  try
    -- Store small key to encrypted file
    testKey.toFile fileKey testPath

    -- Try to load as 32-byte key (should fail)
    try
      let _ ← SecureArray.ofFile τ fileKey testPath 32
      IO.println "✗ Should have failed with size mismatch"
    catch _ =>
      IO.println "✓ Correctly rejected file with wrong size"

    -- Cleanup
    cleanupTestFile filename
  catch e =>
    cleanupTestFile filename
    IO.println s!"✗ Test setup failed: {e}"

-- Test non-existent file error
#eval show IO Unit from do
  let τ ← init Unit
  let fileKey ← SecureArray.new τ 32

  try
    let _ ← SecureArray.ofFile τ fileKey "nonexistent_file.key" 32
    IO.println "✗ Should have failed with file not found"
  catch _ =>
    IO.println "✓ Correctly handled non-existent file"

-- Test integration with SecretKey wrapper
#eval show IO Unit from do
  let τ ← init Unit
  let keySize : USize := 32
  let testKey ← SecureArray.new τ keySize
  let fileKey ← SecureArray.new τ 32
  let filename := "test_secret_key.tmp"
  let testPath := System.FilePath.mk ".lake" / filename

  -- Define a test spec with 32-byte secret keys
  let testSpec : Spec := {
    name := `test
    secretKeyBytes := 32
  }

  try
    -- Store key to encrypted file
    testKey.toFile fileKey testPath

    -- Load into SecureArray
    let secureArray ← SecureArray.ofFile τ fileKey testPath 32

    -- Wrap in SecretKey if size matches
    if h : secureArray.size = testSpec.secretKeyBytes then
      let _ : SecretKey τ testSpec := ⟨secureArray, h⟩
      IO.println "✓ Successfully created SecretKey from loaded encrypted file"
    else
      IO.println "✗ Size mismatch for SecretKey wrapper"

    -- Cleanup
    cleanupTestFile filename
  catch e =>
    cleanupTestFile filename
    IO.println s!"✗ Integration test failed: {e}"

end Tests.SecureFileLoad
