import Sodium.FFI.Basic
import Sodium.FFI.SecretStream

namespace Tests.SecretStream

open Sodium.FFI

def testSodiumInit : IO Unit := do
  let result ← sodiumInit
  if result = 0 then
    IO.println "✓ Test 1: Sodium initialized successfully"
  else
    IO.println s!"✗ Test 1: Sodium initialization failed: {result}"

def testKeygen : IO Unit := do
  let _ ← sodiumInit
  try
    let key ← keygen
    IO.println s!"✓ Test 2: Key generation successful, size: {key.size}"
  catch e =>
    IO.println s!"✗ Test 2: Key generation failed: {e}"

def testBasicSecretStream : IO Unit := do
  let _ ← sodiumInit
  try
    -- Generate a key
    let key ← keygen

    -- Initialize push state and get header
    let (pushState, header) ← initPush key
    IO.println s!"✓ Test 3a: Push state initialized, header size: {header.size}"

    -- Initialize pull state with the same key and header
    let pullState ← initPull key header
    IO.println "✓ Test 3b: Pull state initialized successfully"

    -- Test message encryption/decryption
    let message := "Hello, LibSodium SecretStream!".toUTF8
    let ciphertext ← push pushState message none SECRETSTREAM_XCHACHA20POLY1305_TAG_MESSAGE
    IO.println s!"✓ Test 3c: Message encrypted, ciphertext size: {ciphertext.size}"

    -- Decrypt the message
    let (decrypted, tag) ← pull pullState ciphertext none
    let decryptedString := String.fromUTF8! decrypted
    IO.println s!"✓ Test 3d: Message decrypted: '{decryptedString}', tag: {tag}"

    -- Verify the decrypted message matches original
    if decryptedString == "Hello, LibSodium SecretStream!" then
      IO.println "✓ Test 3e: Decrypted message matches original"
    else
      IO.println "✗ Test 3e: Decrypted message does not match original"

  catch e =>
    IO.println s!"✗ Test 3: Basic SecretStream test failed: {e}"

def testMultipleMessages : IO Unit := do
  let _ ← sodiumInit
  try
    -- Generate a key
    let key ← keygen

    -- Initialize states
    let (pushState, header) ← initPush key
    let pullState ← initPull key header

    -- Send multiple messages with different tags
    let messages := [
      ("First message", SECRETSTREAM_XCHACHA20POLY1305_TAG_MESSAGE),
      ("Second message", SECRETSTREAM_XCHACHA20POLY1305_TAG_PUSH),
      ("Final message", SECRETSTREAM_XCHACHA20POLY1305_TAG_FINAL)
    ]

    for (msg, tag) in messages do
      let messageBytes := msg.toUTF8
      let ciphertext ← push pushState messageBytes none tag
      let (decrypted, receivedTag) ← pull pullState ciphertext none
      let decryptedString := String.fromUTF8! decrypted

      if decryptedString == msg && receivedTag == tag then
        IO.println s!"✓ Test 4: Message '{msg}' with tag {tag} processed correctly"
      else
        IO.println s!"✗ Test 4: Message '{msg}' failed - got '{decryptedString}' with tag {receivedTag}"

  catch e =>
    IO.println s!"✗ Test 4: Multiple messages test failed: {e}"

def testWithAdditionalData : IO Unit := do
  let _ ← sodiumInit
  try
    -- Generate a key
    let key ← keygen

    -- Initialize states
    let (pushState, header) ← initPush key
    let pullState ← initPull key header

    -- Test with additional authenticated data
    let message := "Secret message".toUTF8
    let additionalData := "public metadata".toUTF8

    -- Encrypt with additional data
    let ciphertext ← push pushState message (some additionalData) SECRETSTREAM_XCHACHA20POLY1305_TAG_MESSAGE
    IO.println s!"✓ Test 5a: Message encrypted with additional data, size: {ciphertext.size}"

    -- Decrypt with same additional data
    let (decrypted, tag) ← pull pullState ciphertext (some additionalData)
    let decryptedString := String.fromUTF8! decrypted
    IO.println s!"✓ Test 5b: Message decrypted with additional data: '{decryptedString}'"

    -- Verify the message
    if decryptedString == "Secret message" && tag == SECRETSTREAM_XCHACHA20POLY1305_TAG_MESSAGE then
      IO.println "✓ Test 5c: Additional data authentication successful"
    else
      IO.println "✗ Test 5c: Additional data authentication failed"

  catch e =>
    IO.println s!"✗ Test 5: Additional data test failed: {e}"

def testRekey : IO Unit := do
  let _ ← sodiumInit
  try
    -- Generate a key
    let key ← keygen

    -- Initialize push state
    let (pushState, _) ← initPush key

    -- Send a message, rekey, then send another
    let message1 := "Before rekey".toUTF8
    let _ ← push pushState message1 none SECRETSTREAM_XCHACHA20POLY1305_TAG_MESSAGE
    IO.println "✓ Test 6a: Message sent before rekey"

    -- Perform rekey
    let _ ← rekey pushState
    IO.println "✓ Test 6b: Rekey operation successful"

    -- Send another message after rekey
    let message2 := "After rekey".toUTF8
    let _ ← push pushState message2 none SECRETSTREAM_XCHACHA20POLY1305_TAG_MESSAGE
    IO.println "✓ Test 6c: Message sent after rekey"

  catch e =>
    IO.println s!"✗ Test 6: Rekey test failed: {e}"

def testInvalidKeySize : IO Unit := do
  let _ ← sodiumInit
  try
    -- Create an invalid key (wrong size)
    let invalidKey := ByteArray.mk #[1, 2, 3, 4, 5] -- 5 bytes instead of 32

    -- This should fail
    let _ ← initPush invalidKey
    IO.println "✗ Test 7: Invalid key size should have failed but didn't"
  catch e =>
    IO.println s!"✓ Test 7: Invalid key size correctly rejected: {e}"

def testInvalidHeaderSize : IO Unit := do
  let _ ← sodiumInit
  try
    -- Generate valid key but invalid header
    let key ← keygen
    let invalidHeader := ByteArray.mk #[1, 2, 3] -- 3 bytes instead of 24

    -- This should fail
    let _ ← initPull key invalidHeader
    IO.println "✗ Test 8: Invalid header size should have failed but didn't"
  catch e =>
    IO.println s!"✓ Test 8: Invalid header size correctly rejected: {e}"

def runAllTests : IO Unit := do
  IO.println "=== SecretStream FFI Tests ==="
  testSodiumInit
  testKeygen
  testBasicSecretStream
  testMultipleMessages
  testWithAdditionalData
  testRekey
  testInvalidKeySize
  testInvalidHeaderSize
  IO.println "=== Tests Complete ==="

#eval runAllTests

end Tests.SecretStream
