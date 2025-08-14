import «Sodium».FFI.Basic

namespace Sodium.Tests.EntropyArray

-- Test basic EntropyArray allocation
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _arr ← EntropyArray.new ctx 32
    IO.println "✓ EntropyArray allocation succeeded"
  catch e =>
    IO.println s!"✗ EntropyArray allocation failed: {e}"

-- Test EntropyArray allocation with different sizes
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _small ← EntropyArray.new ctx 1
    let _medium ← EntropyArray.new ctx 256
    let _large ← EntropyArray.new ctx 4096
    IO.println "✓ EntropyArray allocation with various sizes succeeded"
  catch e =>
    IO.println s!"✗ EntropyArray allocation with various sizes failed: {e}"

-- Test EntropyArray allocation with zero size
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let _arr ← EntropyArray.new ctx 0
    IO.println "✓ EntropyArray with size 0 created"
  catch e =>
    IO.println s!"✗ EntropyArray with size 0 failed: {e}"

-- Test EntropyArray refresh functionality
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← EntropyArray.new ctx 32
    let _refreshed ← EntropyArray.refresh ctx arr
    IO.println "✓ EntropyArray refresh succeeded"
  catch e =>
    IO.println s!"✗ EntropyArray refresh failed: {e}"

-- Test multiple EntropyArray refresh calls
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← EntropyArray.new ctx 64
    let refresh1 ← EntropyArray.refresh ctx arr
    let refresh2 ← EntropyArray.refresh ctx refresh1
    let _refresh3 ← EntropyArray.refresh ctx refresh2
    IO.println "✓ Multiple EntropyArray refreshes succeeded"
  catch e =>
    IO.println s!"✗ Multiple EntropyArray refreshes failed: {e}"

end Sodium.Tests.EntropyArray
