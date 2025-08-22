import «Sodium».FFI.SecretStream

namespace Sodium.Tests.SecretStream

open Sodium.FFI.SecretStream

#eval show IO Unit from do
  let τ ← Sodium.init Unit

  -- Generate a key for secretstream
  let key ← keygen (τ := τ)
  IO.println "✓ Generated secretstream key"

  -- Initialize push stream and get header
  let (pushStream, header) ← streamInitPush key
  IO.println s!"✓ Initialized push stream (header size: {header.size} bytes)"

  -- Test messages with different tags
  let message1 : ByteVector 16 := ByteVector.replicate 16 65 -- 16 'A's
  let message2 : ByteVector 24 := ByteVector.replicate 24 66 -- 24 'B's
  let message3 : ByteVector 8 := ByteVector.replicate 8 67   -- 8 'C's
  let additionalData : ByteVector 4 := ByteVector.replicate 4 68 -- 4 'D's

  -- -- Push messages with different tags
  let cipher1 ← streamPush pushStream message1 additionalData .message
  IO.println s!"✓ Encrypted message 1 (size: {cipher1.size} bytes, tag: MESSAGE)"

  let cipher2 ← streamPush pushStream message2 additionalData .push
  IO.println s!"✓ Encrypted message 2 (size: {cipher2.size} bytes, tag: PUSH)"

  let cipher3 ← streamPush pushStream message3 additionalData .final
  IO.println s!"✓ Encrypted message 3 (size: {cipher3.size} bytes, tag: FINAL)"

  -- Initialize pull stream with the header
  let pullStream ← streamInitPull header key
  IO.println "✓ Initialized pull stream"

  -- Decrypt messages
  let result1 ← streamPull pullStream cipher1 additionalData
  match result1 with
  | some (plaintext1, tag1) =>
    if plaintext1.toArray == message1.toArray && tag1 == .message then
      IO.println "✓ Decrypted message 1 successfully with correct tag"
    else
      IO.println "✗ Message 1 decryption failed or wrong tag"
  | none =>
    IO.println "✗ Message 1 authentication failed"

  let result2 ← streamPull pullStream cipher2 additionalData
  match result2 with
  | some (plaintext2, tag2) =>
    if plaintext2.toArray == message2.toArray && tag2 == .push then
      IO.println "✓ Decrypted message 2 successfully with correct tag"
    else
      IO.println "✗ Message 2 decryption failed or wrong tag"
  | none =>
    IO.println "✗ Message 2 authentication failed"

  let result3 ← streamPull pullStream cipher3 additionalData
  match result3 with
  | some (plaintext3, tag3) =>
    if plaintext3.toArray == message3.toArray && tag3 == .final then
      IO.println "✓ Decrypted message 3 successfully with FINAL tag"
    else
      IO.println "✗ Message 3 decryption failed or wrong tag"
  | none =>
    IO.println "✗ Message 3 authentication failed"

#eval show IO Unit from do
  let τ ← Sodium.init Unit

  -- Test authentication failure with wrong additional data
  let key ← keygen (τ := τ)
  let (pushStream, header) ← streamInitPush key
  let message : ByteVector 32 := ByteVector.replicate 32 88 -- 32 'X's
  let correctAD : ByteVector 8 := ByteVector.replicate 8 89 -- 8 'Y's
  let wrongAD : ByteVector 8 := ByteVector.replicate 8 90   -- 8 'Z's

  let ciphertext ← streamPush pushStream message correctAD .message
  let pullStream ← streamInitPull header key

  -- Try to decrypt with wrong additional data
  let failedResult ← streamPull pullStream ciphertext wrongAD
  match failedResult with
  | some _ =>
    IO.println "✗ Should have failed with wrong additional data"
  | none =>
    IO.println "✓ Correctly rejected message with wrong additional data"

#eval show IO Unit from do
  let τ ← Sodium.init Unit

  -- Test rekey functionality
  let key ← keygen (τ := τ)
  let (pushStream, header) ← streamInitPush key
  let message : ByteVector 16 := ByteVector.replicate 16 82 -- 16 'R's
  let noAD : ByteVector 0 := ByteVector.empty

  -- Encrypt before rekey
  let cipher1 ← streamPush pushStream message noAD .message

  -- Perform rekey
  streamRekey pushStream
  IO.println "✓ Performed rekey on push stream"

  -- Encrypt after rekey
  let cipher2 ← streamPush pushStream message noAD .final

  -- Verify ciphertexts are different (they should be due to rekey)
  if cipher1.toArray != cipher2.toArray then
    IO.println "✓ Rekey produced different ciphertext for same message"
  else
    IO.println "✗ Rekey failed - ciphertexts are identical"

  -- Decrypt both messages
  let pullStream ← streamInitPull header key

  let result1 ← streamPull pullStream cipher1 noAD
  match result1 with
  | some (plaintext1, _) =>
    if plaintext1.toArray == message.toArray then
      IO.println "✓ Decrypted pre-rekey message successfully"
    else
      IO.println "✗ Pre-rekey message decryption failed"
  | none =>
    IO.println "✗ Pre-rekey message authentication failed"

  -- Need to rekey pull stream too
  streamRekey pullStream

  let result2 ← streamPull pullStream cipher2 noAD
  match result2 with
  | some (plaintext2, _) =>
    if plaintext2.toArray == message.toArray then
      IO.println "✓ Decrypted post-rekey message successfully"
    else
      IO.println "✗ Post-rekey message decryption failed"
  | none =>
    IO.println "✗ Post-rekey message authentication failed"

end Sodium.Tests.SecretStream
