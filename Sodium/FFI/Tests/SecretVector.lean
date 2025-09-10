import «Sodium».FFI.Basic

namespace Sodium.FFI.Tests.SecretVector

-- Test basic SecretVector allocation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _arr ← SecretVector.new (τ := ctx) 32
    IO.println "✓ SecretVector allocation succeeded"
  catch e =>
    IO.println s!"✗ SecretVector allocation failed: {e}"

-- Test SecretVector allocation with different sizes
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _small ← SecretVector.new (τ := ctx) 1
    let _medium ← SecretVector.new (τ := ctx) 256
    let _large ← SecretVector.new (τ := ctx) 4096
    IO.println "✓ SecretVector allocation with various sizes succeeded"
  catch e =>
    IO.println s!"✗ SecretVector allocation with various sizes failed: {e}"

-- Test SecretVector zero checking on fresh allocation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← SecretVector.new (τ := ctx) 32
    -- Fresh SecretVectors are filled with random data, so should not be zero
    let isZero := SecretVector.isZero arr
    if isZero then
      IO.println "? SecretVector is zero (unexpected but possible with random data)"
    else
      IO.println "✓ SecretVector is not zero (expected with random initialization)"
  catch e =>
    IO.println s!"✗ SecretVector zero check failed: {e}"

-- Test SecretVector allocation with zero size
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← SecretVector.new (τ := ctx) 0
    let isZero := SecretVector.isZero arr
    IO.println s!"✓ SecretVector with size 0 created, isZero: {isZero}"
  catch e =>
    IO.println s!"✗ SecretVector with size 0 failed: {e}"

-- Test multiple SecretVector allocations
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _arr1 ← SecretVector.new (τ := ctx) 32
    let _arr2 ← SecretVector.new (τ := ctx) 32
    let _arr3 ← SecretVector.new (τ := ctx) 64
    IO.println "✓ Multiple SecretVector allocations succeeded"
  catch e =>
    IO.println s!"✗ Multiple SecretVector allocations failed: {e}"

end Sodium.FFI.Tests.SecretVector
