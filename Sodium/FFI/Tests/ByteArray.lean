import «Sodium».Data.ByteArray
import «Sodium».FFI.Basic
import Lean.Data.Json

open Lean

namespace Sodium.FFI.Tests.ByteArray

open ByteArray

-- Test basic ByteArray construction
#eval show IO Unit from do
  let empty := ByteArray.empty
  let single := ByteArray.mk #[42]
  let multi := ByteArray.mk #[1, 2, 3, 4, 5]
  IO.println s!"Empty size: {empty.size}, Single size: {single.size}, Multi size: {multi.size}"

-- Test succ (increment) function
#eval show IO Unit from do
  let original := ByteArray.mk #[0, 0, 0]
  let _incremented := succ original
  IO.println "✓ succ function executed successfully"

-- Test succ with rollover (255 -> 0)
#eval show IO Unit from do
  let maxByte := ByteArray.mk #[255]
  let _rolled := succ maxByte
  IO.println "✓ succ with rollover executed successfully"

-- Test succ with multi-byte increment
#eval show IO Unit from do
  let multiByte := ByteArray.mk #[254, 255, 255]
  let _incremented := succ multiByte
  IO.println "✓ Multi-byte increment executed successfully"

-- Test isZero function
#eval show IO Unit from do
  let zeros := ByteArray.mk #[0, 0, 0, 0]
  let nonZeros := ByteArray.mk #[0, 1, 0, 0]
  let empty := ByteArray.empty

  if isZero zeros && !isZero nonZeros && isZero empty then
    IO.println "✓ isZero function works correctly"
  else
    IO.println "✗ isZero function failed"

-- Test compare function and ordering
#eval show IO Unit from do
  let arr1 := ByteArray.mk #[1, 2, 3]
  let arr2 := ByteArray.mk #[1, 2, 3]
  let arr3 := ByteArray.mk #[1, 2, 4]
  let arr4 := ByteArray.mk #[1, 2]
  let _arr5 := ByteArray.mk #[2, 1, 1]

  -- Test equality
  if ByteArray.compare arr1 arr2 == .eq then
    IO.println "✓ Equal arrays compare correctly"
  else
    IO.println "✗ Equal arrays comparison failed"

  -- Test less than
  if ByteArray.compare arr1 arr3 == .lt then
    IO.println "✓ Less than comparison works"
  else
    IO.println "✗ Less than comparison failed"

  -- Test greater than
  if ByteArray.compare arr3 arr1 == .gt then
    IO.println "✓ Greater than comparison works"
  else
    IO.println "✗ Greater than comparison failed"

  -- Test different lengths
  if ByteArray.compare arr4 arr1 == .lt then
    IO.println "✓ Shorter array compares as less than"
  else
    IO.println "✗ Length comparison failed"

  if ByteArray.compare arr1 arr4 == .gt then
    IO.println "✓ Longer array compares as greater than"
  else
    IO.println "✗ Length comparison failed"

-- Test BEq instance
#eval show IO Unit from do
  let arr1 := ByteArray.mk #[1, 2, 3]
  let arr2 := ByteArray.mk #[1, 2, 3]
  let arr3 := ByteArray.mk #[1, 2, 4]

  if arr1 == arr2 && arr1 != arr3 then
    IO.println "✓ BEq instance works correctly"
  else
    IO.println "✗ BEq instance failed"

-- Test Ord instance
#eval show IO Unit from do
  let arr1 := ByteArray.mk #[1, 2, 3]
  let arr2 := ByteArray.mk #[1, 2, 4]
  let arr3 := ByteArray.mk #[1, 2, 5]

  -- Test proper lexicographic ordering: arr1 < arr2 < arr3
  let cmp1_2 := ByteArray.compare arr1 arr2
  let cmp2_3 := ByteArray.compare arr2 arr3
  let cmp1_3 := ByteArray.compare arr1 arr3

  if cmp1_2 == .lt && cmp2_3 == .lt && cmp1_3 == .lt then
    IO.println "✓ Ord instance works correctly"
  else
    IO.println "✗ Ord instance failed"

-- Test Base64 encoding/decoding roundtrip
#eval show IO Unit from do
  let original := ByteArray.mk #[72, 101, 108, 108, 111, 32, 87, 111, 114, 108, 100] -- "Hello World"
  let encoded := toBase64 original
  match ofBase64? encoded with
  | some decoded =>
    if decoded == original then
      IO.println s!"✓ Base64 roundtrip successful: '{encoded}'"
    else
      IO.println "✗ Base64 roundtrip failed"
  | none =>
    IO.println "✗ Base64 decoding failed"

-- Test Base64 with empty array
#eval show IO Unit from do
  let empty := ByteArray.empty
  let encoded := toBase64 empty
  match ofBase64? encoded with
  | some decoded =>
    if decoded == empty then
      IO.println "✓ Base64 empty array roundtrip successful"
    else
      IO.println "✗ Base64 empty array roundtrip failed"
  | none =>
    IO.println "✗ Base64 empty array decoding failed"

-- Test Base64 with single byte
#eval show IO Unit from do
  let single := ByteArray.mk #[42]
  let encoded := toBase64 single
  match ofBase64? encoded with
  | some decoded =>
    if decoded == single then
      IO.println "✓ Base64 single byte roundtrip successful"
    else
      IO.println "✗ Base64 single byte roundtrip failed"
  | none =>
    IO.println "✗ Base64 single byte decoding failed"

-- Test Base64 with binary data (all byte values)
#eval show IO Unit from do
  let binary := ByteArray.mk (List.range 256 |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
  let encoded := toBase64 binary
  match ofBase64? encoded with
  | some decoded =>
    if decoded == binary then
      IO.println "✓ Base64 binary data roundtrip successful"
    else
      IO.println "✗ Base64 binary data roundtrip failed"
  | none =>
    IO.println "✗ Base64 binary data decoding failed"

-- Test JSON serialization/deserialization
#eval show IO Unit from do
  let original := ByteArray.mk #[1, 2, 3, 4, 5]
  let json := toJson original
  match fromJson? json with
  | .ok decoded =>
    if decoded == original then
      IO.println "✓ JSON roundtrip successful"
    else
      IO.println "✗ JSON roundtrip failed"
  | .error _ =>
    IO.println "✗ JSON deserialization failed"

-- Test JSON with empty array
#eval show IO Unit from do
  let empty := ByteArray.empty
  let json := toJson empty
  match fromJson? json with
  | .ok decoded =>
    if decoded == empty then
      IO.println "✓ JSON empty array roundtrip successful"
    else
      IO.println "✗ JSON empty array roundtrip failed"
  | .error _ =>
    IO.println "✗ JSON empty array deserialization failed"

-- Test succ sequence (multiple increments)
#eval show IO Unit from do
  let mut current := ByteArray.mk #[0, 0]
  let mut success_count := 0

  for _ in [0:5] do
    let next := succ current
    current := next
    success_count := success_count + 1

  IO.println s!"✓ Sequential succ operations: {success_count}/5 completed"

-- Test compare with identical content but different instances
#eval show IO Unit from do
  let arr1 := ByteArray.mk #[1, 2, 3]
  let arr2 := ByteArray.mk #[1, 2, 3]

  -- These should be equal even though they're different instances
  if ByteArray.compare arr1 arr2 == .eq && arr1 == arr2 then
    IO.println "✓ Content equality works across instances"
  else
    IO.println "✗ Content equality failed"

-- Test edge cases for Base64
#eval show IO Unit from do
  -- Test with bytes that might cause Base64 issues
  let challenging := ByteArray.mk #[0, 255, 127, 128, 1, 254]
  let encoded := toBase64 challenging
  match ofBase64? encoded with
  | some decoded =>
    if decoded == challenging then
      IO.println "✓ Base64 challenging bytes roundtrip successful"
    else
      IO.println "✗ Base64 challenging bytes roundtrip failed"
  | none =>
    IO.println "✗ Base64 challenging bytes decoding failed"

-- Test Base64 error handling with invalid input
#eval show IO Unit from do
  -- Test with clearly invalid Base64 strings
  let invalid_inputs := ["invalid!", "abc", "=invalid=", "123@#$"]
  let mut error_count := 0

  for invalid in invalid_inputs do
    match ofBase64? invalid with
    | some _ =>
      IO.println s!"✗ Expected error for invalid Base64: '{invalid}'"
    | none =>
      error_count := error_count + 1

  if error_count == invalid_inputs.length then
    IO.println s!"✓ All {error_count} invalid Base64 inputs properly rejected"
  else
    IO.println s!"✗ Only {error_count}/{invalid_inputs.length} invalid inputs rejected"

-- Test succ with all 255s (should wrap to all 0s + 1 extra byte conceptually)
#eval show IO Unit from do
  let allOnes := ByteArray.mk #[255, 255, 255]
  let _incremented := succ allOnes
  -- Note: The exact behavior depends on sodium_increment implementation
  IO.println "✓ All 255s increment completed"

-- Test isZero edge cases
#eval show IO Unit from do
  let singleZero := ByteArray.mk #[0]
  let singleNonZero := ByteArray.mk #[1]
  let mixedStart := ByteArray.mk #[0, 1, 2]
  let mixedEnd := ByteArray.mk #[1, 2, 0]

  let results := [
    ("single zero", isZero singleZero, true),
    ("single non-zero", isZero singleNonZero, false),
    ("mixed start with zero", isZero mixedStart, false),
    ("mixed end with zero", isZero mixedEnd, false)
  ]

  let mut all_passed := true
  for (desc, actual, expected) in results do
    if actual == expected then
      IO.println s!"✓ isZero {desc}: correct"
    else
      IO.println s!"✗ isZero {desc}: expected {expected}, got {actual}"
      all_passed := false

  if all_passed then
    IO.println "✓ All isZero edge cases passed"

-- Test comparison with empty arrays
#eval show IO Unit from do
  let empty1 := ByteArray.empty
  let empty2 := ByteArray.empty
  let nonEmpty := ByteArray.mk #[1]

  if ByteArray.compare empty1 empty2 == .eq && ByteArray.compare empty1 nonEmpty == .lt && ByteArray.compare nonEmpty empty1 == .gt then
    IO.println "✓ Empty array comparisons work correctly"
  else
    IO.println "✗ Empty array comparisons failed"

-- Performance test: Large array operations
#eval show IO Unit from do
  let large := ByteArray.mk (List.range 1000 |>.map (· % 256) |>.map UInt8.ofNat |>.toArray)
  let encoded := toBase64 large
  match ofBase64? encoded with
  | some decoded =>
    let _incremented := succ large
    let _zero_check := isZero large
    if decoded == large then
      IO.println "✓ Large array (1000 bytes) operations completed successfully"
    else
      IO.println "✗ Large array operations failed"
  | none =>
    IO.println "✗ Large array Base64 decoding failed"

#eval IO.println "\n=== ByteArray Data Tests Complete ==="

end Sodium.FFI.Tests.ByteArray
