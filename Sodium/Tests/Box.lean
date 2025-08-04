import «Sodium».FFI.Basic
import «Sodium».FFI.Box

namespace Sodium.Tests

open Sodium.FFI

def testBoxBasic : IO Unit := do
  -- Initialize Sodium
  let initResult ← sodiumInit
  if initResult != 0 then
    throw (IO.userError "Failed to initialize Sodium")

  -- Generate Alice's key pair
  let (alicePublicKey, aliceSecretKey) ← boxKeypair
  IO.println s!"Alice's public key size: {alicePublicKey.size}"
  IO.println s!"Alice's secret key size: {aliceSecretKey.size}"

  -- Generate Bob's key pair
  let (bobPublicKey, bobSecretKey) ← boxKeypair
  IO.println s!"Bob's public key size: {bobPublicKey.size}"
  IO.println s!"Bob's secret key size: {bobSecretKey.size}"

  -- Generate a random nonce
  let nonce ← randomBytes BOX_NONCEBYTES
  IO.println s!"Nonce size: {nonce.size}"

  -- Test message
  let message := "Hello from Alice to Bob!".toUTF8
  IO.println s!"Original message: {String.fromUTF8! message}"

  -- Alice encrypts message for Bob (using Bob's public key and Alice's secret key)
  let ciphertext ← boxEasy message nonce bobPublicKey aliceSecretKey
  IO.println s!"Encrypted message size: {ciphertext.size}"

  -- Bob decrypts message from Alice (using Alice's public key and Bob's secret key)
  let decrypted ← boxOpenEasy ciphertext nonce alicePublicKey bobSecretKey
  IO.println s!"Decrypted message: {String.fromUTF8! decrypted}"

  -- Verify round-trip
  if message.data == decrypted.data then
    IO.println "✓ Box round-trip test passed!"
  else
    throw (IO.userError "✗ Box round-trip test failed!")

def testBoxSeedKeypair : IO Unit := do
  let _ ← sodiumInit

  -- Generate a seed
  let seed ← randomBytes BOX_SEEDBYTES
  IO.println s!"Seed size: {seed.size}"

  -- Generate key pair from seed
  let (publicKey1, secretKey1) ← boxSeedKeypair seed
  IO.println s!"First key pair - public: {publicKey1.size}, secret: {secretKey1.size}"

  -- Generate same key pair from same seed (should be deterministic)
  let (publicKey2, secretKey2) ← boxSeedKeypair seed
  IO.println s!"Second key pair - public: {publicKey2.size}, secret: {secretKey2.size}"

  -- Verify keys are identical
  if publicKey1.data == publicKey2.data && secretKey1.data == secretKey2.data then
    IO.println "✓ Seed keypair determinism test passed!"
  else
    throw (IO.userError "✗ Seed keypair determinism test failed!")

def testBoxInvalidSeed : IO Unit := do
  let _ ← sodiumInit

  -- Use invalid seed size (wrong length)
  let invalidSeed ← randomBytes 16  -- Should be 32 bytes

  -- This should fail with invalid seed size error
  try
    let _ ← boxSeedKeypair invalidSeed
    throw (IO.userError "✗ Expected error for invalid seed size")
  catch e =>
    IO.println s!"✓ Correctly caught seed error: {e}"

def testBoxInvalidNonce : IO Unit := do
  let _ ← sodiumInit

  let (_, aliceSecret) ← boxKeypair
  let (bobPublic, _) ← boxKeypair
  let message := "test".toUTF8

  -- Use invalid nonce size (wrong length)
  let invalidNonce ← randomBytes 12  -- Should be 24 bytes

  -- This should fail with invalid nonce size error
  try
    let _ ← boxEasy message invalidNonce bobPublic aliceSecret
    throw (IO.userError "✗ Expected error for invalid nonce size")
  catch e =>
    IO.println s!"✓ Correctly caught nonce error: {e}"

def testBoxInvalidKeys : IO Unit := do
  let _ ← sodiumInit

  let nonce ← randomBytes BOX_NONCEBYTES
  let message := "test".toUTF8

  -- Use invalid public key size (wrong length)
  let invalidPublicKey ← randomBytes 16  -- Should be 32 bytes
  let (_, validSecretKey) ← boxKeypair

  -- This should fail with invalid public key size error
  try
    let _ ← boxEasy message nonce invalidPublicKey validSecretKey
    throw (IO.userError "✗ Expected error for invalid public key size")
  catch e =>
    IO.println s!"✓ Correctly caught public key error: {e}"

  -- Use invalid secret key size (wrong length)
  let (validPublicKey, _) ← boxKeypair
  let invalidSecretKey ← randomBytes 16  -- Should be 32 bytes

  -- This should fail with invalid secret key size error
  try
    let _ ← boxEasy message nonce validPublicKey invalidSecretKey
    throw (IO.userError "✗ Expected error for invalid secret key size")
  catch e =>
    IO.println s!"✓ Correctly caught secret key error: {e}"

def testBoxAuthFailure : IO Unit := do
  let _ ← sodiumInit

  let (alicePublic, aliceSecret) ← boxKeypair
  let (bobPublic, bobSecret) ← boxKeypair
  let nonce ← randomBytes BOX_NONCEBYTES
  let message := "test".toUTF8

  -- Encrypt message
  let ciphertext ← boxEasy message nonce bobPublic aliceSecret

  -- Corrupt the ciphertext by flipping a bit
  let corruptedCiphertext := ciphertext.set! 0 (ciphertext.get! 0 ^^^ 1)

  -- This should fail authentication
  try
    let _ ← boxOpenEasy corruptedCiphertext nonce alicePublic bobSecret
    throw (IO.userError "✗ Expected authentication failure")
  catch e =>
    IO.println s!"✓ Correctly caught authentication error: {e}"

def testBoxWrongKeys : IO Unit := do
  let _ ← sodiumInit

  let (_, aliceSecret) ← boxKeypair
  let (bobPublic, bobSecret) ← boxKeypair
  let (charliePublic, _) ← boxKeypair  -- Third party
  let nonce ← randomBytes BOX_NONCEBYTES
  let message := "test".toUTF8

  -- Alice encrypts for Bob
  let ciphertext ← boxEasy message nonce bobPublic aliceSecret

  -- Try to decrypt with wrong public key (Charlie's instead of Alice's)
  try
    let _ ← boxOpenEasy ciphertext nonce charliePublic bobSecret
    throw (IO.userError "✗ Expected decryption failure with wrong key")
  catch e =>
    IO.println s!"✓ Correctly caught wrong public key error: {e}"

end Sodium.Tests
