import «Sodium».FFI.Basic
import «Sodium».FFI.KeyDeriv
import «Sodium».Data.ByteVector

namespace Sodium.FFI.Tests.KeyDeriv

open Sodium.FFI.KeyDeriv

-- Helper function to create context from ByteVector
private def mkContext (data : Array UInt8) (h : data.size = 8 := by rfl) : ByteVector CONTEXTBYTES :=
  (ByteArray.mk data).toVector.cast h

-- =============================================================================
-- Test Constants and Size Validations
-- =============================================================================

#eval show IO Unit from do
  IO.println s!"KeyDeriv constants:"
  IO.println s!"  KEYBYTES: {KEYBYTES}"
  IO.println s!"  CONTEXTBYTES: {CONTEXTBYTES}"
  IO.println s!"  BYTES_MIN: {BYTES_MIN}"
  IO.println s!"  BYTES_MAX: {BYTES_MAX}"

-- =============================================================================
-- Test Master Key Generation
-- =============================================================================

-- Test basic master key generation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _masterKey ← keygen (τ := ctx)
    IO.println "✓ Master key generation succeeded"
  catch e =>
    IO.println s!"✗ Master key generation failed: {e}"

-- =============================================================================
-- Test Key Derivation Operations
-- =============================================================================

-- Test basic key derivation with valid parameters
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey ← keygen (τ := ctx)
    let context := mkContext #[0x74, 0x65, 0x73, 0x74, 0x63, 0x74, 0x78, 0x00]
    let subkey ← derive (τ := ctx) 32 1 context masterKey
    if subkey.size == 32 then
      IO.println "✓ Key derivation succeeded with correct size (32 bytes)"
    else
      IO.println s!"✗ Key derivation size mismatch: expected 32, got {subkey.size}"
  catch e =>
    IO.println s!"✗ Key derivation failed: {e}"

-- Test key derivation with minimum and maximum subkey sizes
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey ← keygen (τ := ctx)
    let context := mkContext #[0x74, 0x65, 0x73, 0x74, 0x63, 0x74, 0x78, 0x00]
    let minSubkey ← derive (τ := ctx) BYTES_MIN 1 context masterKey
    let maxSubkey ← derive (τ := ctx) BYTES_MAX 2 context masterKey

    if minSubkey.size == BYTES_MIN && maxSubkey.size == BYTES_MAX then
      IO.println "✓ Min/max subkey sizes work correctly"
    else
      IO.println s!"✗ Min/max subkey size test failed: min={minSubkey.size} (expected {BYTES_MIN}), max={maxSubkey.size} (expected {BYTES_MAX})"
  catch e =>
    IO.println s!"✗ Min/max subkey size test failed: {e}"

-- =============================================================================
-- Test Key Uniqueness Properties
-- =============================================================================

-- Test that different subkey IDs produce different keys
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey ← keygen (τ := ctx)
    let context := mkContext #[0x74, 0x65, 0x73, 0x74, 0x63, 0x74, 0x78, 0x00]
    let subkey1 ← derive (τ := ctx) 32 1 context masterKey
    let subkey2 ← derive (τ := ctx) 32 2 context masterKey
    if subkey1 != subkey2 then
      IO.println "✓ Different subkey IDs produce different keys"
    else
      IO.println "✗ Subkeys should be different for different IDs"
  catch e =>
    IO.println s!"✗ Different subkey ID test failed: {e}"

-- Test that different contexts produce different keys
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey ← keygen (τ := ctx)
    let context1 := mkContext #[0x74, 0x65, 0x73, 0x74, 0x63, 0x74, 0x78, 0x31]  -- "testctx1" as bytes
    let context2 := mkContext #[0x74, 0x65, 0x73, 0x74, 0x63, 0x74, 0x78, 0x32]  -- "testctx2" as bytes
    let subkey1 ← derive (τ := ctx) 32 1 context1 masterKey
    let subkey2 ← derive (τ := ctx) 32 1 context2 masterKey
    if subkey1 != subkey2 then
      IO.println "✓ Different contexts produce different keys"
    else
      IO.println "✗ Subkeys should be different for different contexts"
  catch e =>
    IO.println s!"✗ Different context test failed: {e}"

-- Test that same parameters produce identical keys (deterministic)
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey ← keygen (τ := ctx)
    let context := mkContext #[0x74, 0x65, 0x73, 0x74, 0x63, 0x74, 0x78, 0x00]
    let subkey1 ← derive (τ := ctx) 32 1 context masterKey
    let subkey2 ← derive (τ := ctx) 32 1 context masterKey
    if subkey1 == subkey2 then
      IO.println "✓ Identical parameters produce identical keys (deterministic)"
    else
      IO.println "✗ Key derivation should be deterministic"
  catch e =>
    IO.println s!"✗ Deterministic key derivation test failed: {e}"

-- =============================================================================
-- Test Error Handling and Input Validation
-- =============================================================================

-- Test key derivation with zero context
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey ← keygen (τ := ctx)
    let context := mkContext #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]  -- Zero context
    let subkey ← derive (τ := ctx) 32 1 context masterKey
    if subkey.size == 32 then
      IO.println "✓ Zero context works correctly"
    else
      IO.println "✗ Zero context should work"
  catch e =>
    IO.println s!"✗ Zero context test failed: {e}"

-- Test key derivation with maximum UInt64 context
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey ← keygen (τ := ctx)
    let context := mkContext #[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]  -- Maximum value
    let subkey ← derive (τ := ctx) 32 1 context masterKey
    if subkey.size == 32 then
      IO.println "✓ Maximum UInt64 context works correctly"
    else
      IO.println "✗ Maximum UInt64 context should work"
  catch e =>
    IO.println s!"✗ Maximum UInt64 context test failed: {e}"

-- Test key derivation with subkey size too small
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey ← keygen (τ := ctx)
    let context := mkContext #[0x74, 0x65, 0x73, 0x74, 0x63, 0x74, 0x78, 0x00]
    let _ ← derive (τ := ctx) (BYTES_MIN - 1) 1 context masterKey
    IO.println "✗ Should have failed with subkey size too small"
  catch e =>
    IO.println s!"✓ Correctly rejected subkey size too small: {e}"

-- Test key derivation with subkey size too large
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey ← keygen (τ := ctx)
    let context := mkContext #[0x74, 0x65, 0x73, 0x74, 0x63, 0x74, 0x78, 0x00]
    let _ ← derive (τ := ctx) (BYTES_MAX + 1) 1 context masterKey
    IO.println "✗ Should have failed with subkey size too large"
  catch e =>
    IO.println s!"✓ Correctly rejected subkey size too large: {e}"

-- =============================================================================
-- Test Edge Cases
-- =============================================================================

-- Test key derivation with zero subkey ID
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey ← keygen (τ := ctx)
    let context := mkContext #[0x74, 0x65, 0x73, 0x74, 0x63, 0x74, 0x78, 0x00]
    let subkey ← derive (τ := ctx) 32 0 context masterKey
    if subkey.size == 32 then
      IO.println "✓ Zero subkey ID works correctly"
    else
      IO.println "✗ Zero subkey ID should work"
  catch e =>
    IO.println s!"✗ Zero subkey ID test failed: {e}"

-- Test key derivation with maximum UInt64 subkey ID
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey ← keygen (τ := ctx)
    let context := mkContext #[0x74, 0x65, 0x73, 0x74, 0x63, 0x74, 0x78, 0x00]
    let subkey ← derive (τ := ctx) 32 (UInt64.ofNat (2^64 - 1)) context masterKey
    if subkey.size == 32 then
      IO.println "✓ Maximum subkey ID works correctly"
    else
      IO.println "✗ Maximum subkey ID should work"
  catch e =>
    IO.println s!"✗ Maximum subkey ID test failed: {e}"

-- =============================================================================
-- Test Multiple Key Derivations
-- =============================================================================

-- Test multiple consecutive key derivations
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey ← keygen (τ := ctx)
    let context := mkContext #[0x74, 0x65, 0x73, 0x74, 0x63, 0x74, 0x78, 0x00]

    let mut success_count := 0
    for i in [0:10] do
      try
        let subkey ← derive (τ := ctx) 32 i.toUInt64 context masterKey
        if subkey.size == 32 then
          success_count := success_count + 1
      catch _ =>
        continue

    IO.println s!"✓ Multiple consecutive derivations: {success_count}/10 succeeded"
  catch e =>
    IO.println s!"✗ Multiple consecutive derivations failed: {e}"

-- Test multiple different contexts
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey ← keygen (τ := ctx)

    let contexts := [
      mkContext #[0x63, 0x6F, 0x6E, 0x74, 0x65, 0x78, 0x74, 0x31],  -- "context1" as bytes
      mkContext #[0x63, 0x6F, 0x6E, 0x74, 0x65, 0x78, 0x74, 0x32],  -- "context2" as bytes
      mkContext #[0x63, 0x6F, 0x6E, 0x74, 0x65, 0x78, 0x74, 0x33],  -- "context3" as bytes
      mkContext #[0x63, 0x6F, 0x6E, 0x74, 0x65, 0x78, 0x74, 0x34],  -- "context4" as bytes
      mkContext #[0x63, 0x6F, 0x6E, 0x74, 0x65, 0x78, 0x74, 0x35]   -- "context5" as bytes
    ]

    let mut keys : Array (SecretVector ctx 32) := #[]
    for context in contexts do
      let subkey ← derive (τ := ctx) 32 1 context masterKey
      keys := keys.push subkey

    -- Verify all keys are different
    let mut all_different := true
    for i in [0:keys.size] do
      for j in [i+1:keys.size] do
        if keys[i]? == keys[j]? then
          all_different := false
          break

    if all_different then
      IO.println "✓ Multiple different contexts produce unique keys"
    else
      IO.println "✗ Multiple contexts should produce unique keys"
  catch e =>
    IO.println s!"✗ Multiple context test failed: {e}"

-- =============================================================================
-- Test Security Properties
-- =============================================================================

-- Test that different master keys produce different subkeys
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey1 ← keygen (τ := ctx)
    let masterKey2 ← keygen (τ := ctx)
    let context := mkContext #[0x74, 0x65, 0x73, 0x74, 0x63, 0x74, 0x78, 0x00]

    let subkey1 ← derive (τ := ctx) 32 1 context masterKey1
    let subkey2 ← derive (τ := ctx) 32 1 context masterKey2

    if subkey1 != subkey2 then
      IO.println "✓ Different master keys produce different subkeys"
    else
      IO.println "✗ Different master keys should produce different subkeys"
  catch e =>
    IO.println s!"✗ Different master key test failed: {e}"

-- =============================================================================
-- Test Real-World Usage Patterns
-- =============================================================================

-- Test common context strings
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey ← keygen (τ := ctx)

    let common_contexts := [
      mkContext #[0x55, 0x73, 0x65, 0x72, 0x41, 0x75, 0x74, 0x68],  -- "UserAuth" as bytes
      mkContext #[0x44, 0x61, 0x74, 0x61, 0x4B, 0x65, 0x79, 0x00],  -- "DataKey\x00" as bytes
      mkContext #[0x46, 0x69, 0x6C, 0x65, 0x45, 0x6E, 0x63, 0x72],  -- "FileEncr" as bytes
      mkContext #[0x44, 0x61, 0x74, 0x61, 0x62, 0x61, 0x73, 0x65],  -- "Database" as bytes
      mkContext #[0x53, 0x65, 0x73, 0x73, 0x69, 0x6F, 0x6E, 0x00]   -- "Session\x00" as bytes
    ]

    let mut success_count := 0
    for context in common_contexts do
      try
        let _subkey ← derive (τ := ctx) 32 1 context masterKey
        success_count := success_count + 1
      catch _ =>
        continue

    IO.println s!"✓ Common context patterns: {success_count}/{common_contexts.length} succeeded"
  catch e =>
    IO.println s!"✗ Common context patterns failed: {e}"

-- Test various subkey sizes for different use cases
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let masterKey ← keygen (τ := ctx)
    let context := mkContext #[0x74, 0x65, 0x73, 0x74, 0x63, 0x74, 0x78, 0x00]

    let sizes := [16, 24, 32, 48, 64]  -- Common key sizes
    let mut success_count := 0

    for size in sizes do
      try
        let subkey ← derive (τ := ctx) size.toUSize 1 context masterKey
        if subkey.size == size then
          success_count := success_count + 1
      catch _ =>
        continue

    IO.println s!"✓ Various subkey sizes: {success_count}/{sizes.length} succeeded"
  catch e =>
    IO.println s!"✗ Various subkey sizes test failed: {e}"


#eval IO.println "\n=== KeyDeriv FFI Tests Complete ==="

end Sodium.FFI.Tests.KeyDeriv
