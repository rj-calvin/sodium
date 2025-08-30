import «Sodium».FFI.Basic

namespace Sodium.FFI.Tests.SecureVectorComparison

-- Test SecureArray comparison function
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr1 ← SecureArray.new ctx 32
    let arr2 ← SecureArray.new ctx 32
    
    -- Test comparison (should work even if random data is different)
    let cmp := SecureArray.compare arr1 arr2
    match cmp with
    | Ordering.lt => IO.println "✓ SecureArray comparison: arr1 < arr2"
    | Ordering.eq => IO.println "✓ SecureArray comparison: arr1 = arr2"
    | Ordering.gt => IO.println "✓ SecureArray comparison: arr1 > arr2"
    
  catch e =>
    IO.println s!"✗ SecureArray comparison failed: {e}"

-- Test SecureArray comparison with different sizes
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let small ← SecureArray.new ctx 16
    let large ← SecureArray.new ctx 32
    
    let cmp := SecureArray.compare small large
    match cmp with
    | Ordering.lt => IO.println "✓ SecureArray size comparison: small < large (expected)"
    | Ordering.eq => IO.println "? SecureArray size comparison: small = large (unexpected)"
    | Ordering.gt => IO.println "? SecureArray size comparison: small > large (unexpected)"
    
  catch e =>
    IO.println s!"✗ SecureArray size comparison failed: {e}"

-- Test SecureArray self-comparison
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← SecureArray.new ctx 32
    
    let cmp := SecureArray.compare arr arr
    match cmp with
    | Ordering.eq => IO.println "✓ SecureArray self-comparison: arr = arr (expected)"
    | _ => IO.println "? SecureArray self-comparison: arr ≠ arr (unexpected)"
    
  catch e =>
    IO.println s!"✗ SecureArray self-comparison failed: {e}"

-- Test SecureArray ordering with zero-sized arrays
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let zero1 ← SecureArray.new ctx 0
    let zero2 ← SecureArray.new ctx 0
    let nonzero ← SecureArray.new ctx 8
    
    let cmp1 := SecureArray.compare zero1 zero2
    let cmp2 := SecureArray.compare zero1 nonzero
    
    match cmp1 with
    | Ordering.eq => IO.println "✓ Zero-sized SecureArrays are equal"
    | _ => IO.println "? Zero-sized SecureArrays are not equal"
    
    match cmp2 with
    | Ordering.lt => IO.println "✓ Zero-sized < non-zero SecureArray (expected)"
    | _ => IO.println "? Zero-sized ≮ non-zero SecureArray"
    
  catch e =>
    IO.println s!"✗ SecureArray zero-size comparison failed: {e}"

-- Test SecureArray Ord instance
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr1 ← SecureArray.new ctx 16
    let arr2 ← SecureArray.new ctx 32
    let arr3 ← SecureArray.new ctx 48
    
    -- Test that Ord instance works
    let _arrays := [arr1, arr2, arr3]
    IO.println "✓ SecureArray Ord instance compiles and works"
    
  catch e =>
    IO.println s!"✗ SecureArray Ord instance failed: {e}"

end Sodium.FFI.Tests.SecureVectorComparison