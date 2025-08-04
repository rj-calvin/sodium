import «Sodium».FFI.KeyExch
import «Sodium».FFI.Basic

open Sodium.FFI

namespace Sodium.Tests.KeyExch

def testKxKeypair : IO Unit := do
  try
    let (publicKey, secretKey) ← kxKeypair
    if publicKey.size == 32 && secretKey.size == 32 then
      IO.println "✓ Key exchange keypair generated successfully (32 bytes each)"
    else
      IO.println ("✗ Key exchange keypair sizes: public " ++ toString publicKey.size ++ ", secret " ++ toString secretKey.size ++ " (expected 32 each)")
  catch e =>
    IO.println ("✗ Key exchange keypair generation failed: " ++ toString e)

def testKxSeedKeypair : IO Unit := do
  try
    let seed := "this_is_exactly_32_bytes_long!!!".toUTF8
    let (publicKey1, secretKey1) ← kxSeedKeypair seed
    let (publicKey2, secretKey2) ← kxSeedKeypair seed
    
    if publicKey1.size == 32 && secretKey1.size == 32 then
      -- Check deterministic generation
      let samePk := publicKey1.toList == publicKey2.toList
      let sameSk := secretKey1.toList == secretKey2.toList
      if samePk && sameSk then
        IO.println "✓ Seed keypair generation is deterministic"
      else
        IO.println "✗ Seed keypair generation should be deterministic"
    else
      IO.println ("✗ Seed keypair sizes: public " ++ toString publicKey1.size ++ ", secret " ++ toString secretKey1.size ++ " (expected 32 each)")
  catch e =>
    IO.println ("✗ Seed keypair generation failed: " ++ toString e)

def testKxSessionKeys : IO Unit := do
  try
    -- Generate client and server keypairs
    let (clientPk, clientSk) ← kxKeypair
    let (serverPk, serverSk) ← kxKeypair
    
    -- Derive session keys from both perspectives
    let (clientRx, clientTx) ← kxClientSessionKeys clientPk clientSk serverPk
    let (serverRx, serverTx) ← kxServerSessionKeys serverPk serverSk clientPk
    
    if clientRx.size == 32 && clientTx.size == 32 && serverRx.size == 32 && serverTx.size == 32 then
      -- Check key symmetry: client TX should equal server RX, and vice versa
      let correctSymmetry := 
        (clientTx.toList == serverRx.toList) && (clientRx.toList == serverTx.toList)
      
      if correctSymmetry then
        IO.println "✓ Session key derivation working correctly with proper TX/RX symmetry"
      else
        IO.println "✗ Session keys don't have correct TX/RX symmetry"
    else
      IO.println ("✗ Session key sizes not all 32 bytes")
  catch e =>
    IO.println ("✗ Session key derivation failed: " ++ toString e)

def testKxInvalidInputs : IO Unit := do
  let (validPk, validSk) ← kxKeypair
  let invalidKey := "short".toUTF8
  let invalidSeed := "too_short".toUTF8
  
  -- Test invalid seed size
  try
    let _ ← kxSeedKeypair invalidSeed
    IO.println "✗ Should have failed with invalid seed size"
  catch _ =>
    IO.println "✓ Correctly rejected invalid seed size"
  
  -- Test invalid client public key
  try
    let _ ← kxClientSessionKeys invalidKey validSk validPk
    IO.println "✗ Should have failed with invalid client public key"
  catch _ =>
    IO.println "✓ Correctly rejected invalid client public key"
  
  -- Test invalid client secret key
  try
    let _ ← kxClientSessionKeys validPk invalidKey validPk
    IO.println "✗ Should have failed with invalid client secret key"
  catch _ =>
    IO.println "✓ Correctly rejected invalid client secret key"
  
  -- Test invalid server public key
  try
    let _ ← kxClientSessionKeys validPk validSk invalidKey
    IO.println "✗ Should have failed with invalid server public key"
  catch _ =>
    IO.println "✓ Correctly rejected invalid server public key"

def testKxKeyReuse : IO Unit := do
  try
    -- Test that same keypairs produce same session keys
    let seed1 := "32_byte_deterministic_seed_test1".toUTF8
    let seed2 := "32_byte_deterministic_seed_test2".toUTF8
    
    let (clientPk, clientSk) ← kxSeedKeypair seed1
    let (serverPk, serverSk) ← kxSeedKeypair seed2
    
    -- Derive session keys twice
    let (rx1, tx1) ← kxClientSessionKeys clientPk clientSk serverPk
    let (rx2, tx2) ← kxClientSessionKeys clientPk clientSk serverPk
    
    let consistent := (rx1.toList == rx2.toList) && (tx1.toList == tx2.toList)
    if consistent then
      IO.println "✓ Key exchange is deterministic with same inputs"
    else
      IO.println "✗ Key exchange should be deterministic with same inputs"
  catch e =>
    IO.println ("✗ Key reuse test failed: " ++ toString e)

def runAllTests : IO Unit := do
  IO.println "=== Key Exchange FFI Tests ==="
  testKxKeypair
  testKxSeedKeypair
  testKxSessionKeys
  testKxInvalidInputs
  testKxKeyReuse
  IO.println ""

end Sodium.Tests.KeyExch