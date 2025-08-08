import «Sodium».FFI.Basic
import «Sodium».FFI.Deprecated.Sign

namespace Sodium.Tests

open Sodium.FFI

def testSignBasic : IO Unit := do
  -- Initialize Sodium
  let initResult ← sodiumInit
  if initResult != 0 then
    throw (IO.userError "Failed to initialize Sodium")

  -- Generate signing key pair
  let (publicKey, secretKey) ← signKeypair
  IO.println s!"Public key size: {publicKey.size}"
  IO.println s!"Secret key size: {secretKey.size}"

  -- Test message
  let message := "Hello, digital signatures!".toUTF8
  IO.println s!"Original message: {String.fromUTF8! message}"

  -- Test combined mode (signature + message)
  let signedMessage ← sign message secretKey
  IO.println s!"Signed message size: {signedMessage.size}"

  -- Verify and extract original message
  let verifiedMessage ← signOpen signedMessage publicKey
  IO.println s!"Verified message: {String.fromUTF8! verifiedMessage}"

  -- Verify round-trip
  if message.data == verifiedMessage.data then
    IO.println "✓ Combined mode sign/verify test passed!"
  else
    throw (IO.userError "✗ Combined mode sign/verify test failed!")

def testSignDetached : IO Unit := do
  let _ ← sodiumInit

  let (publicKey, secretKey) ← signKeypair
  let message := "Detached signature test message".toUTF8
  IO.println s!"Message for detached signing: {String.fromUTF8! message}"

  -- Create detached signature
  let signature ← signDetached message secretKey
  IO.println s!"Detached signature size: {signature.size}"

  -- Verify detached signature
  let isValid ← signVerifyDetached signature message publicKey
  if isValid then
    IO.println "✓ Detached signature verification passed!"
  else
    throw (IO.userError "✗ Detached signature verification failed!")

def testSignSeedKeypair : IO Unit := do
  let _ ← sodiumInit

  -- Generate a seed
  let seed ← randomBytes SIGN_SEEDBYTES
  IO.println s!"Seed size: {seed.size}"

  -- Generate key pair from seed
  let (publicKey1, secretKey1) ← signSeedKeypair seed
  IO.println s!"First key pair - public: {publicKey1.size}, secret: {secretKey1.size}"

  -- Generate same key pair from same seed (should be deterministic)
  let (publicKey2, secretKey2) ← signSeedKeypair seed
  IO.println s!"Second key pair - public: {publicKey2.size}, secret: {secretKey2.size}"

  -- Verify keys are identical
  if publicKey1.data == publicKey2.data && secretKey1.data == secretKey2.data then
    IO.println "✓ Seed keypair determinism test passed!"
  else
    throw (IO.userError "✗ Seed keypair determinism test failed!")

  -- Test signing with deterministic keys
  let message := "test".toUTF8
  let signature1 ← signDetached message secretKey1
  let signature2 ← signDetached message secretKey2

  -- Ed25519 signatures are deterministic, so they should be identical
  if signature1.data == signature2.data then
    IO.println "✓ Deterministic signature test passed!"
  else
    throw (IO.userError "✗ Deterministic signature test failed!")

def testSignInvalidSeed : IO Unit := do
  let _ ← sodiumInit

  -- Use invalid seed size (wrong length)
  let invalidSeed ← randomBytes 16  -- Should be 32 bytes

  -- This should fail with invalid seed size error
  try
    let _ ← signSeedKeypair invalidSeed
    throw (IO.userError "✗ Expected error for invalid seed size")
  catch e =>
    IO.println s!"✓ Correctly caught seed error: {e}"

def testSignInvalidKeys : IO Unit := do
  let _ ← sodiumInit

  let message := "test".toUTF8

  -- Test invalid secret key size
  let invalidSecretKey ← randomBytes 32  -- Should be 64 bytes

  try
    let _ ← sign message invalidSecretKey
    throw (IO.userError "✗ Expected error for invalid secret key size")
  catch e =>
    IO.println s!"✓ Correctly caught secret key error: {e}"

  -- Test invalid public key size for verification
  let (_, validSecretKey) ← signKeypair
  let signedMessage ← sign message validSecretKey
  let invalidPublicKey ← randomBytes 16  -- Should be 32 bytes

  try
    let _ ← signOpen signedMessage invalidPublicKey
    throw (IO.userError "✗ Expected error for invalid public key size")
  catch e =>
    IO.println s!"✓ Correctly caught public key error: {e}"

def testSignVerificationFailure : IO Unit := do
  let _ ← sodiumInit

  let (_, secretKey1) ← signKeypair
  let (publicKey2, _) ← signKeypair  -- Different key pair
  let message := "test".toUTF8

  -- Sign with first key pair
  let signedMessage ← sign message secretKey1

  -- Try to verify with wrong public key
  try
    let _ ← signOpen signedMessage publicKey2
    throw (IO.userError "✗ Expected signature verification failure")
  catch e =>
    IO.println s!"✓ Correctly caught verification error: {e}"

def testSignDetachedVerificationFailure : IO Unit := do
  let _ ← sodiumInit

  let (_, secretKey1) ← signKeypair
  let (publicKey2, _) ← signKeypair  -- Different key pair
  let message := "test".toUTF8

  -- Create signature with first key pair
  let signature ← signDetached message secretKey1

  -- Try to verify with wrong public key
  let isValid ← signVerifyDetached signature message publicKey2
  if isValid then
    throw (IO.userError "✗ Expected detached signature verification to fail")
  else
    IO.println "✓ Correctly detected invalid detached signature"

def testSignCorruptedSignature : IO Unit := do
  let _ ← sodiumInit

  let (publicKey, secretKey) ← signKeypair
  let message := "test".toUTF8

  -- Create valid signature
  let signature ← signDetached message secretKey

  -- Corrupt the signature by flipping a bit
  let corruptedSignature := signature.set! 0 (signature.get! 0 ^^^ 1)

  -- This should fail verification
  let isValid ← signVerifyDetached corruptedSignature message publicKey
  if isValid then
    throw (IO.userError "✗ Expected corrupted signature verification to fail")
  else
    IO.println "✓ Correctly detected corrupted signature"

def testSignCorruptedMessage : IO Unit := do
  let _ ← sodiumInit

  let (publicKey, secretKey) ← signKeypair
  let originalMessage := "original message".toUTF8
  let modifiedMessage := "modified message".toUTF8

  -- Sign original message
  let signature ← signDetached originalMessage secretKey

  -- Try to verify signature against modified message
  let isValid ← signVerifyDetached signature modifiedMessage publicKey
  if isValid then
    throw (IO.userError "✗ Expected signature verification to fail for modified message")
  else
    IO.println "✓ Correctly detected message tampering"

end Sodium.Tests
