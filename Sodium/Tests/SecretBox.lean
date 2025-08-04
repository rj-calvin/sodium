import «Sodium».FFI.Basic
import «Sodium».FFI.SecretBox

namespace Sodium.Tests

open Sodium.FFI

def testSecretBox : IO Unit := do
  -- Initialize Sodium
  let initResult ← sodiumInit
  if initResult != 0 then
    throw (IO.userError "Failed to initialize Sodium")

  -- Generate a random key
  let key ← secretBoxKeygen
  IO.println s!"Generated key of size: {key.size}"

  -- Generate a random nonce (24 bytes)
  let nonce ← randomBytes SECRETBOX_NONCEBYTES
  IO.println s!"Generated nonce of size: {nonce.size}"

  -- Test message
  let message := "Hello, LibSodium SecretBox!".toUTF8
  IO.println s!"Original message: {String.fromUTF8! message}"

  -- Encrypt the message
  let ciphertext ← secretBoxEasy message nonce key
  IO.println s!"Encrypted message size: {ciphertext.size}"

  -- Decrypt the message
  let decrypted ← secretBoxOpenEasy ciphertext nonce key
  IO.println s!"Decrypted message: {String.fromUTF8! decrypted}"

  -- Verify round-trip
  if message.data == decrypted.data then
    IO.println "✓ SecretBox round-trip test passed!"
  else
    throw (IO.userError "✗ SecretBox round-trip test failed!")

def testSecretBoxInvalidKey : IO Unit := do
  let _ ← sodiumInit

  -- Generate valid nonce and message
  let nonce ← randomBytes SECRETBOX_NONCEBYTES
  let message := "test".toUTF8

  -- Use invalid key size (wrong length)
  let invalidKey ← randomBytes 16  -- Should be 32 bytes

  -- This should fail with invalid key size error
  try
    let _ ← secretBoxEasy message nonce invalidKey
    throw (IO.userError "✗ Expected error for invalid key size")
  catch e =>
    IO.println s!"✓ Correctly caught error: {e}"

def testSecretBoxInvalidNonce : IO Unit := do
  let _ ← sodiumInit

  -- Generate valid key and message
  let key ← secretBoxKeygen
  let message := "test".toUTF8

  -- Use invalid nonce size (wrong length)
  let invalidNonce ← randomBytes 12  -- Should be 24 bytes

  -- This should fail with invalid nonce size error
  try
    let _ ← secretBoxEasy message invalidNonce key
    throw (IO.userError "✗ Expected error for invalid nonce size")
  catch e =>
    IO.println s!"✓ Correctly caught error: {e}"

def testSecretBoxAuthFailure : IO Unit := do
  let _ ← sodiumInit

  let key ← secretBoxKeygen
  let nonce ← randomBytes SECRETBOX_NONCEBYTES
  let message := "test".toUTF8

  -- Encrypt message
  let ciphertext ← secretBoxEasy message nonce key

  -- Corrupt the ciphertext by flipping a bit
  let corruptedCiphertext := ciphertext.set! 0 (ciphertext.get! 0 ^^^ 1)

  -- This should fail authentication
  try
    let _ ← secretBoxOpenEasy corruptedCiphertext nonce key
    throw (IO.userError "✗ Expected authentication failure")
  catch e =>
    IO.println s!"✓ Correctly caught authentication error: {e}"

end Sodium.Tests
