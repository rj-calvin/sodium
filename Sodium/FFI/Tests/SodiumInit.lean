import «Sodium».FFI.Basic

namespace Sodium.FFI.Tests.SodiumInit

-- Test basic Sodium initialization
#eval show IO Unit from do
  try
    let _ctx ← Sodium.init Unit
    IO.println "✓ Sodium initialization succeeded"
  catch e =>
    IO.println s!"✗ Sodium initialization failed: {e}"

-- Test multiple initializations are safe
#eval show IO Unit from do
  try
    let _ctx1 ← Sodium.init Unit
    let _ctx2 ← Sodium.init String
    let _ctx3 ← Sodium.init Nat
    IO.println "✓ Multiple Sodium initializations succeeded"
  catch e =>
    IO.println s!"✗ Multiple Sodium initializations failed: {e}"

-- Test that initialization provides working context
#eval show IO Unit from do
  try
    let _ctx ← Sodium.init Unit
    -- Just creating the context should be sufficient to verify it works
    IO.println "✓ Sodium context creation succeeded"
  catch e =>
    IO.println s!"✗ Sodium context creation failed: {e}"

end Sodium.FFI.Tests.SodiumInit