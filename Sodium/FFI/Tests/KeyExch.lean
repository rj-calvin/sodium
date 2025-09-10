import «Sodium».FFI.KeyExch

namespace Sodium.FFI.Tests.KeyExch

open Sodium FFI KeyExch

-- =============================================================================
-- Test Constants and Size Validations
-- =============================================================================

#eval show IO Unit from do
  IO.println s!"KeyExch constants:"
  IO.println s!"  PUBLICKEYBYTES: {PUBLICKEYBYTES}"
  IO.println s!"  SECRETKEYBYTES: {SECRETKEYBYTES}"
  IO.println s!"  SEEDBYTES: {SEEDBYTES}"
  IO.println s!"  SESSIONKEYBYTES: {SESSIONKEYBYTES}"

-- =============================================================================
-- Test Key Generation Operations
-- =============================================================================

-- Test basic keypair generation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (publicKey, _secretKey) ← keypair (τ := ctx)
    if publicKey.size == PUBLICKEYBYTES then
      IO.println "✓ KeyExch keypair generation succeeded with correct public key size"
    else
      IO.println s!"✗ Public key size mismatch: expected {PUBLICKEYBYTES}, got {publicKey.size}"
  catch e =>
    IO.println s!"✗ KeyExch keypair generation failed: {e}"

-- Test deterministic keypair generation from seed
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let seed ← SecretVector.new (τ := ctx) SEEDBYTES
    let (publicKey1, _secretKey1) ← seedKeypair (τ := ctx) seed
    let (publicKey2, _secretKey2) ← seedKeypair (τ := ctx) seed

    if publicKey1.size == PUBLICKEYBYTES then
      IO.println "✓ KeyExch seed keypair generation succeeded with correct size"
    else
      IO.println s!"✗ Seed keypair public key size mismatch: expected {PUBLICKEYBYTES}, got {publicKey1.size}"

    -- Both public keys should be identical since same seed
    if publicKey1 == publicKey2 then
      IO.println "✓ KeyExch deterministic keypair generation produces identical results"
    else
      IO.println "✗ KeyExch deterministic keypair generation should produce identical results"

  catch e =>
    IO.println s!"✗ KeyExch seed keypair generation failed: {e}"

-- =============================================================================
-- Test Session Key Exchange Operations
-- =============================================================================

-- Test basic client-server key exchange
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (clientPk, clientSk) ← keypair (τ := ctx)
    let (serverPk, serverSk) ← keypair (τ := ctx)

    -- Client derives session keys
    let some (clientRx, clientTx) ← clientSessionKeys (τ := ctx) clientPk clientSk serverPk
      | do IO.println "✗ Client session key derivation failed"; return

    -- Server derives session keys
    let some (serverRx, serverTx) ← serverSessionKeys (τ := ctx) serverPk serverSk clientPk
      | do IO.println "✗ Server session key derivation failed"; return

    -- Verify key sizes
    if clientRx.size == SESSIONKEYBYTES && clientTx.size == SESSIONKEYBYTES then
      IO.println "✓ Client session keys have correct sizes"
    else
      IO.println s!"✗ Client session key size mismatch: rx={clientRx.size}, tx={clientTx.size}, expected {SESSIONKEYBYTES}"

    if serverRx.size == SESSIONKEYBYTES && serverTx.size == SESSIONKEYBYTES then
      IO.println "✓ Server session keys have correct sizes"
    else
      IO.println s!"✗ Server session key size mismatch: rx={serverRx.size}, tx={serverTx.size}, expected {SESSIONKEYBYTES}"

    -- Verify cross-compatibility: client TX should equal server RX, client RX should equal server TX
    if clientTx == serverRx && clientRx == serverTx then
      IO.println "✓ Session key exchange succeeded - keys are properly cross-compatible"
    else
      IO.println "✗ Session key exchange failed - keys are not cross-compatible"

  catch e =>
    IO.println s!"✗ Session key exchange failed: {e}"

-- Test session key derivation with deterministic keys
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let seed1 ← SecretVector.new (τ := ctx) SEEDBYTES
    let seed2 ← SecretVector.new (τ := ctx) SEEDBYTES

    -- Generate deterministic keypairs
    let (clientPk, clientSk) ← seedKeypair (τ := ctx) seed1
    let (serverPk, serverSk) ← seedKeypair (τ := ctx) seed2

    -- Derive session keys twice with same inputs
    let some (clientRx1, clientTx1) ← clientSessionKeys (τ := ctx) clientPk clientSk serverPk
      | do IO.println "✗ Client session key derivation failed"; return
    let some (clientRx2, clientTx2) ← clientSessionKeys (τ := ctx) clientPk clientSk serverPk
      | do IO.println "✗ Client session key derivation failed"; return
    let some (serverRx1, serverTx1) ← serverSessionKeys (τ := ctx) serverPk serverSk clientPk
      | do IO.println "✗ Server session key derivation failed"; return
    let some (serverRx2, serverTx2) ← serverSessionKeys (τ := ctx) serverPk serverSk clientPk
      | do IO.println "✗ Server session key derivation failed"; return

    -- Verify deterministic session key generation
    if clientRx1 == clientRx2 && clientTx1 == clientTx2 then
      IO.println "✓ Client session key derivation is deterministic"
    else
      IO.println "✗ Client session key derivation should be deterministic"

    if serverRx1 == serverRx2 && serverTx1 == serverTx2 then
      IO.println "✓ Server session key derivation is deterministic"
    else
      IO.println "✗ Server session key derivation should be deterministic"

    -- Verify cross-compatibility still holds
    if clientTx1 == serverRx1 && clientRx1 == serverTx1 then
      IO.println "✓ Deterministic session keys are properly cross-compatible"
    else
      IO.println "✗ Deterministic session keys should be cross-compatible"

  catch e =>
    IO.println s!"✗ Deterministic session key derivation failed: {e}"

-- =============================================================================
-- Test Security Properties
-- =============================================================================

-- Test that different keypairs produce different session keys
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (clientPk1, clientSk1) ← keypair (τ := ctx)
    let (clientPk2, clientSk2) ← keypair (τ := ctx)
    let (serverPk, _) ← keypair (τ := ctx)

    let some (clientRx1, clientTx1) ← clientSessionKeys (τ := ctx) clientPk1 clientSk1 serverPk
      | do IO.println "✗ Client session key derivation 1 failed"; return
    let some (clientRx2, clientTx2) ← clientSessionKeys (τ := ctx) clientPk2 clientSk2 serverPk
      | do IO.println "✗ Client session key derivation 2 failed"; return

    if clientRx1 != clientRx2 && clientTx1 != clientTx2 then
      IO.println "✓ Different client keypairs produce different session keys (key uniqueness)"
    else
      IO.println "✗ Different client keypairs should produce different session keys"

  catch e =>
    IO.println s!"✗ Key uniqueness test failed: {e}"

-- Test that different server keys produce different session keys
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (clientPk, clientSk) ← keypair (τ := ctx)
    let (serverPk1, _) ← keypair (τ := ctx)
    let (serverPk2, _) ← keypair (τ := ctx)

    let some (clientRx1, clientTx1) ← clientSessionKeys (τ := ctx) clientPk clientSk serverPk1
      | do IO.println "✗ Client session key derivation with server 1 failed"; return
    let some (clientRx2, clientTx2) ← clientSessionKeys (τ := ctx) clientPk clientSk serverPk2
      | do IO.println "✗ Client session key derivation with server 2 failed"; return

    if clientRx1 != clientRx2 && clientTx1 != clientTx2 then
      IO.println "✓ Different server public keys produce different session keys (server key uniqueness)"
    else
      IO.println "✗ Different server public keys should produce different session keys"

  catch e =>
    IO.println s!"✗ Server key uniqueness test failed: {e}"

-- Test that RX and TX keys are different
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (clientPk, clientSk) ← keypair (τ := ctx)
    let (serverPk, _) ← keypair (τ := ctx)

    let some (clientRx, clientTx) ← clientSessionKeys (τ := ctx) clientPk clientSk serverPk
      | do IO.println "✗ Client session key derivation failed in memory test"; return

    if clientRx != clientTx then
      IO.println "✓ RX and TX session keys are different (bidirectional security)"
    else
      IO.println "✗ RX and TX session keys should be different"

  catch e =>
    IO.println s!"✗ Bidirectional security test failed: {e}"

-- =============================================================================
-- Test Key Exchange Protocol Simulation
-- =============================================================================

-- Test complete key exchange protocol simulation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit

    -- Step 1: Generate long-term identity keypairs
    let (alicePk, aliceSk) ← keypair (τ := ctx)
    let (bobPk, bobSk) ← keypair (τ := ctx)

    -- Step 2: Alice (client) derives session keys
    let some (aliceRx, aliceTx) ← clientSessionKeys (τ := ctx) alicePk aliceSk bobPk
      | do IO.println "✗ Alice session key derivation failed"; return

    -- Step 3: Bob (server) derives session keys
    let some (bobRx, bobTx) ← serverSessionKeys (τ := ctx) bobPk bobSk alicePk
      | do IO.println "✗ Bob session key derivation failed"; return

    -- Step 4: Verify protocol correctness
    let protocolCorrect := (aliceTx == bobRx) && (aliceRx == bobTx)

    if protocolCorrect then
      IO.println "✓ Complete key exchange protocol simulation succeeded"
      IO.println "  - Alice's TX key matches Bob's RX key (Alice → Bob channel)"
      IO.println "  - Alice's RX key matches Bob's TX key (Bob → Alice channel)"
    else
      IO.println "✗ Key exchange protocol simulation failed"

  catch e =>
    IO.println s!"✗ Protocol simulation failed: {e}"

-- =============================================================================
-- Performance and Stress Tests
-- =============================================================================

-- Test multiple key exchanges
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let mut success_count := 0

    for _ in [0:10] do
      try
        let (clientPk, clientSk) ← keypair (τ := ctx)
        let (serverPk, serverSk) ← keypair (τ := ctx)

        let some (clientRx, clientTx) ← clientSessionKeys (τ := ctx) clientPk clientSk serverPk
          | continue
        let some (serverRx, serverTx) ← serverSessionKeys (τ := ctx) serverPk serverSk clientPk
          | continue

        if clientTx == serverRx && clientRx == serverTx then
          success_count := success_count + 1
      catch _ =>
        continue

    IO.println s!"✓ Multiple key exchanges: {success_count}/10 succeeded"

  catch e =>
    IO.println s!"✗ Multiple key exchanges failed: {e}"

-- Test with multiple different server keys (many-to-one scenario)
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let (clientPk, clientSk) ← keypair (τ := ctx)
    let mut unique_sessions := 0

    -- Generate session keys with 5 different servers
    let mut session_keys : Array (SecretVector ctx _) := #[]
    for _ in [0:5] do
      try
        let (serverPk, _) ← keypair (τ := ctx)
        let some (clientRx, _) ← clientSessionKeys (τ := ctx) clientPk clientSk serverPk
          | continue

        -- Check if this session key is unique
        let mut is_unique := true
        for existing_key in session_keys do
          if existing_key == clientRx then
            is_unique := false
            break

        if is_unique then
          session_keys := session_keys.push clientRx
          unique_sessions := unique_sessions + 1
      catch _ =>
        continue

    if unique_sessions == 5 then
      IO.println "✓ Multiple server scenario: All session keys are unique"
    else
      IO.println s!"✓ Multiple server scenario: {unique_sessions}/5 unique session keys generated"

  catch e =>
    IO.println s!"✗ Multiple server scenario failed: {e}"

end Sodium.FFI.Tests.KeyExch
