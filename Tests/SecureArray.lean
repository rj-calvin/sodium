import «Sodium».FFI.Basic

namespace Sodium.Tests.SecureVector

-- Test basic SecureVector allocation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _arr ← SecureVector.new (τ := ctx) 32
    IO.println "✓ SecureVector allocation succeeded"
  catch e =>
    IO.println s!"✗ SecureVector allocation failed: {e}"

-- Test SecureVector allocation with different sizes
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _small ← SecureVector.new (τ := ctx) 1
    let _medium ← SecureVector.new (τ := ctx) 256
    let _large ← SecureVector.new (τ := ctx) 4096
    IO.println "✓ SecureVector allocation with various sizes succeeded"
  catch e =>
    IO.println s!"✗ SecureVector allocation with various sizes failed: {e}"

-- Test SecureVector zero checking on fresh allocation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← SecureVector.new ctx 32
    -- Fresh SecureVectors are filled with random data, so should not be zero
    let isZero := SecureVector.isZero arr
    if isZero then
      IO.println "? SecureVector is zero (unexpected but possible with random data)"
    else
      IO.println "✓ SecureVector is not zero (expected with random initialization)"
  catch e =>
    IO.println s!"✗ SecureVector zero check failed: {e}"

-- Test SecureVector allocation with zero size
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← SecureVector.new ctx 0
    let isZero := SecureVector.isZero arr
    IO.println s!"✓ SecureVector with size 0 created, isZero: {isZero}"
  catch e =>
    IO.println s!"✗ SecureVector with size 0 failed: {e}"

-- Test multiple SecureVector allocations
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _arr1 ← SecureVector.new ctx 32
    let _arr2 ← SecureVector.new ctx 32
    let _arr3 ← SecureVector.new ctx 64
    IO.println "✓ Multiple SecureVector allocations succeeded"
  catch e =>
    IO.println s!"✗ Multiple SecureVector allocations failed: {e}"

end Sodium.Tests.SecureVector
