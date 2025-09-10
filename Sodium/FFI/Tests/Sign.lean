import «Sodium».FFI.Basic
import «Sodium».FFI.Sign
import «Sodium».Data.ByteVector

namespace Sodium.FFI.Tests.Sign

open Sodium FFI.Sign

-- =============================================================================
-- Test Constants and Size Validations
-- =============================================================================

#eval show IO Unit from do
  IO.println s!"Sign constants:"
  IO.println s!"  PUBLICKEYBYTES: {PUBLICKEYBYTES}"
  IO.println s!"  SECRETKEYBYTES: {SECRETKEYBYTES}"
  IO.println s!"  SEEDBYTES: {SEEDBYTES}"
  IO.println s!"  BYTES: {BYTES}"

-- =============================================================================
-- Test Key Generation Operations
-- =============================================================================

-- Test basic keypair generation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey, _secretKey) ← keypair (τ := ctx)
    if publicKey.size == PUBLICKEYBYTES then
      IO.println "✓ Ed25519 keypair generation succeeded with correct public key size"
    else
      IO.println s!"✗ Public key size mismatch: expected {PUBLICKEYBYTES}, got {publicKey.size}"
  catch e =>
    IO.println s!"✗ Ed25519 keypair generation failed: {e}"

-- Test deterministic keypair generation from seed
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let seed ← SecretVector.new (τ := ctx) SEEDBYTES
    let (publicKey1, _secretKey1) ← seedKeypair (τ := ctx) seed
    let (publicKey2, _secretKey2) ← seedKeypair (τ := ctx) seed

    if publicKey1.size == PUBLICKEYBYTES then
      IO.println "✓ Ed25519 seed keypair generation succeeded with correct size"
    else
      IO.println s!"✗ Seed keypair public key size mismatch: expected {PUBLICKEYBYTES}, got {publicKey1.size}"

    -- Test deterministic behavior - both public keys should be identical
    if publicKey1 == publicKey2 then
      IO.println "✓ Seed keypair generation is deterministic"
    else
      IO.println "✗ Seed keypair generation is not deterministic"
  catch e =>
    IO.println s!"✗ Ed25519 seed keypair generation failed: {e}"

-- =============================================================================
-- Test Combined Signature Operations (sign/signOpen)
-- =============================================================================

-- Test combined signature and verification
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey, secretKey) ← keypair (τ := ctx)

    -- Create a test message
    let message := "Hello, Ed25519 signatures!".toUTF8.toVector

    -- Sign the message
    let signedMessage ← sign message secretKey

    if signedMessage.size == message.size + BYTES then
      IO.println "✓ Combined signature creation succeeded with correct size"
    else
      IO.println s!"✗ Signed message size mismatch: expected {message.size + BYTES}, got {signedMessage.size}"

    -- Verify and recover the message
    match ← signOpen signedMessage publicKey with
    | some recoveredMessage =>
      if recoveredMessage == message then
        IO.println "✓ Combined signature verification and message recovery succeeded"
      else
        IO.println "✗ Recovered message does not match original"
    | none =>
      IO.println "✗ Combined signature verification failed"
  catch e =>
    IO.println s!"✗ Combined signature test failed: {e}"

-- Test signature verification with wrong public key should fail
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (_publicKey1, secretKey1) ← keypair (τ := ctx)
    let (publicKey2, _secretKey2) ← keypair (τ := ctx)

    let message := "Test message for wrong key".toUTF8.toVector
    let signedMessage ← sign message secretKey1

    -- Try to verify with wrong public key
    match ← signOpen signedMessage publicKey2 with
    | some _ =>
      IO.println "✗ Signature verification should have failed with wrong public key"
    | none =>
      IO.println "✓ Signature verification correctly failed with wrong public key"
  catch e =>
    IO.println s!"✗ Wrong key signature test failed: {e}"

-- =============================================================================
-- Test Detached Signature Operations
-- =============================================================================

-- Test detached signature creation and verification
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey, secretKey) ← keypair (τ := ctx)

    let message := "Hello, detached Ed25519 signatures!".toUTF8.toVector

    -- Create detached signature
    let signature ← signDetached message secretKey

    if signature.size == BYTES then
      IO.println "✓ Detached signature creation succeeded with correct size"
    else
      IO.println s!"✗ Signature size mismatch: expected {BYTES}, got {signature.size}"

    -- Verify detached signature
    let isValid ← verifyDetached signature message publicKey
    if isValid then
      IO.println "✓ Detached signature verification succeeded"
    else
      IO.println "✗ Detached signature verification failed"
  catch e =>
    IO.println s!"✗ Detached signature test failed: {e}"

-- Test detached signature verification with wrong message should fail
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey, secretKey) ← keypair (τ := ctx)

    let originalMessage := "Original message".toUTF8.toVector
    let tamperedMessage := "Tampered message".toUTF8.toVector

    let signature ← signDetached originalMessage secretKey

    -- Try to verify signature against tampered message
    let isValid ← verifyDetached signature tamperedMessage publicKey
    if isValid then
      IO.println "✗ Signature verification should have failed with tampered message"
    else
      IO.println "✓ Signature verification correctly failed with tampered message"
  catch e =>
    IO.println s!"✗ Message tampering test failed: {e}"

-- =============================================================================
-- Test Ed25519 to Curve25519 Conversion Operations
-- =============================================================================

-- Test public key conversion
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (ed25519Pk, _ed25519Sk) ← keypair (τ := ctx)

    let curve25519Pk ← ed25519PkToCurve25519 ed25519Pk

    if curve25519Pk.size == 32 then
      IO.println "✓ Ed25519 to Curve25519 public key conversion succeeded"
    else
      IO.println s!"✗ Converted public key size mismatch: expected 32, got {curve25519Pk.size}"
  catch e =>
    IO.println s!"✗ Ed25519 to Curve25519 public key conversion failed: {e}"

-- Test secret key conversion
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (_ed25519Pk, ed25519Sk) ← keypair (τ := ctx)

    let _curve25519Sk ← ed25519SkToCurve25519 ed25519Sk

    -- SecretVector doesn't expose size directly, but we can test that conversion succeeded
    IO.println "✓ Ed25519 to Curve25519 secret key conversion succeeded"
  catch e =>
    IO.println s!"✗ Ed25519 to Curve25519 secret key conversion failed: {e}"

-- =============================================================================
-- Test Edge Cases and Error Conditions
-- =============================================================================

-- Test empty message signing
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey, secretKey) ← keypair (τ := ctx)

    let emptyMessage : ByteVector 0 := default
    let signature ← signDetached emptyMessage secretKey
    let isValid ← verifyDetached signature emptyMessage publicKey

    if isValid then
      IO.println "✓ Empty message signing and verification succeeded"
    else
      IO.println "✗ Empty message signature verification failed"
  catch e =>
    IO.println s!"✗ Empty message signing test failed: {e}"

-- Test large message signing
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey, secretKey) ← keypair (τ := ctx)

    -- Create a large message (1KB)
    let largeMessage := ByteArray.mk (Array.range 1024 |>.map (· % 256 |>.toUInt8)) |>.toVector
    let signature ← signDetached largeMessage secretKey
    let isValid ← verifyDetached signature largeMessage publicKey

    if isValid then
      IO.println "✓ Large message signing and verification succeeded"
    else
      IO.println "✗ Large message signature verification failed"
  catch e =>
    IO.println s!"✗ Large message signing test failed: {e}"

end Sodium.FFI.Tests.Sign
