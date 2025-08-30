import «Sodium».FFI.Basic

namespace Sodium.FFI.Tests.EntropyVector

-- Test basic EntropyVector allocation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _arr ← EntropyVector.new (τ := ctx) 32
    IO.println "✓ EntropyVector allocation succeeded"
  catch e =>
    IO.println s!"✗ EntropyVector allocation failed: {e}"

-- Test EntropyVector allocation with different sizes
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _small ← EntropyVector.new (τ := ctx) 1
    let _medium ← EntropyVector.new (τ := ctx) 256
    let _large ← EntropyVector.new (τ := ctx) 4096
    IO.println "✓ EntropyVector allocation with various sizes succeeded"
  catch e =>
    IO.println s!"✗ EntropyVector allocation with various sizes failed: {e}"

-- Test EntropyVector allocation with zero size
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _arr ← EntropyVector.new (τ := ctx) 0
    IO.println "✓ EntropyVector with size 0 created"
  catch e =>
    IO.println s!"✗ EntropyVector with size 0 failed: {e}"

-- Test EntropyVector refresh functionality
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← EntropyVector.new (τ := ctx) 32
    let _refreshed ← EntropyVector.refresh (τ := ctx) arr
    IO.println "✓ EntropyVector refresh succeeded"
  catch e =>
    IO.println s!"✗ EntropyVector refresh failed: {e}"

-- Test multiple EntropyVector refresh calls
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← EntropyVector.new (τ := ctx) 64
    let refresh1 ← EntropyVector.refresh (τ := ctx) arr
    let refresh2 ← EntropyVector.refresh (τ := ctx) refresh1
    let _refresh3 ← EntropyVector.refresh (τ := ctx) refresh2
    IO.println "✓ Multiple EntropyVector refreshes succeeded"
  catch e =>
    IO.println s!"✗ Multiple EntropyVector refreshes failed: {e}"

end Sodium.FFI.Tests.EntropyVector
