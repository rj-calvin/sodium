import «Sodium».FFI.Aead

namespace Sodium.FFI.Tests.AEAD

open Sodium.FFI.Aead

#eval show IO Unit from do
  let τ ← Sodium.init Unit

  -- Generate a key for AEAD
  let key ← keygen (τ := τ)
  IO.println "✓ Generated AEAD key"

  -- Create a nonce (24 bytes for XChaCha20-Poly1305)
  let nonce : ByteVector NONCEBYTES := ByteVector.replicate NONCEBYTES 0

  -- Test message and additional data
  let message : ByteVector 32 := ByteVector.replicate 32 65 -- 32 'A's
  let additionalData : ByteVector 16 := ByteVector.replicate 16 66 -- 16 'B's

  -- Encrypt the message
  let ciphertext ← encrypt message additionalData nonce key
  IO.println s!"✓ Encrypted message (ciphertext size: {ciphertext.size} bytes)"

  -- Decrypt the message
  let decrypted ← decrypt ciphertext additionalData nonce key
  match decrypted with
  | some plaintext =>
    if plaintext.toArray == message.toArray then
      IO.println "✓ Decryption successful - message matches!"
    else
      IO.println "✗ Decryption failed - message mismatch"
  | none =>
    IO.println "✗ Decryption failed - authentication error"

  -- Test with wrong additional data (should fail)
  let wrongAD : ByteVector 16 := ByteVector.replicate 16 67 -- 16 'C's
  let failedDecrypt ← decrypt ciphertext wrongAD nonce key
  match failedDecrypt with
  | some _ =>
    IO.println "✗ Should have failed with wrong additional data"
  | none =>
    IO.println "✓ Correctly rejected message with wrong additional data"

#eval show IO Unit from do
  let τ ← Sodium.init Unit

  -- Test detached mode
  let key ← keygen (τ := τ)
  let nonce : ByteVector NONCEBYTES := ByteVector.replicate NONCEBYTES 1
  let message : ByteVector 64 := ByteVector.replicate 64 72 -- 64 'H's
  let additionalData : ByteVector 0 := ByteVector.empty

  -- Encrypt in detached mode
  let (ciphertext, mac) ← encryptDetached message additionalData nonce key
  IO.println s!"✓ Encrypted in detached mode (ciphertext: {ciphertext.size}, mac: {mac.size} bytes)"

  -- Decrypt in detached mode
  let decrypted ← decryptDetached ciphertext mac additionalData nonce key
  match decrypted with
  | some plaintext =>
    if plaintext.toArray == message.toArray then
      IO.println "✓ Detached decryption successful!"
    else
      IO.println "✗ Detached decryption - message mismatch"
  | none =>
    IO.println "✗ Detached decryption failed"

  -- Test with modified MAC (should fail)
  let corruptMac := mac.set! 0 (mac.get! 0 + 1)
  let failedDecrypt ← decryptDetached ciphertext corruptMac additionalData nonce key
  match failedDecrypt with
  | some _ =>
    IO.println "✗ Should have failed with corrupted MAC"
  | none =>
    IO.println "✓ Correctly rejected message with corrupted MAC"

end Sodium.FFI.Tests.AEAD
