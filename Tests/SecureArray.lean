import «Sodium».FFI.Basic

namespace Sodium.Tests.SecureArray

-- Test basic SecureArray allocation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _arr ← SecureArray.new ctx 32
    IO.println "✓ SecureArray allocation succeeded"
  catch e =>
    IO.println s!"✗ SecureArray allocation failed: {e}"

-- Test SecureArray allocation with different sizes
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _small ← SecureArray.new ctx 1
    let _medium ← SecureArray.new ctx 256  
    let _large ← SecureArray.new ctx 4096
    IO.println "✓ SecureArray allocation with various sizes succeeded"
  catch e =>
    IO.println s!"✗ SecureArray allocation with various sizes failed: {e}"

-- Test SecureArray zero checking on fresh allocation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← SecureArray.new ctx 32
    -- Fresh SecureArrays are filled with random data, so should not be zero
    let isZero := SecureArray.isZero arr
    if isZero then
      IO.println "? SecureArray is zero (unexpected but possible with random data)"
    else
      IO.println "✓ SecureArray is not zero (expected with random initialization)"
  catch e =>
    IO.println s!"✗ SecureArray zero check failed: {e}"

-- Test SecureArray allocation with zero size
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← SecureArray.new ctx 0
    let isZero := SecureArray.isZero arr
    IO.println s!"✓ SecureArray with size 0 created, isZero: {isZero}"
  catch e =>
    IO.println s!"✗ SecureArray with size 0 failed: {e}"

-- Test multiple SecureArray allocations
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _arr1 ← SecureArray.new ctx 32
    let _arr2 ← SecureArray.new ctx 32
    let _arr3 ← SecureArray.new ctx 64
    IO.println "✓ Multiple SecureArray allocations succeeded"
  catch e =>
    IO.println s!"✗ Multiple SecureArray allocations failed: {e}"

end Sodium.Tests.SecureArray