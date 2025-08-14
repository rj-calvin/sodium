import «Sodium».FFI.Basic

namespace Sodium.Tests.EntropyExtraction

-- Test basic entropy extraction
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← EntropyArray.new ctx 32
    let (data, _) ← EntropyArray.extract ctx arr 16
    IO.println s!"✓ Basic entropy extraction succeeded, extracted {data.size} bytes"
  catch e =>
    IO.println s!"✗ Basic entropy extraction failed: {e}"

-- Test extracting more data than available
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← EntropyArray.new ctx 16
    let (data, _) ← EntropyArray.extract ctx arr 32
    IO.println s!"✓ Over-extraction handled, got {data.size} bytes (should be ≤ 16)"
  catch e =>
    IO.println s!"✗ Over-extraction test failed: {e}"

-- Test extracting zero bytes
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← EntropyArray.new ctx 32
    let (data, _) ← EntropyArray.extract ctx arr 0
    IO.println s!"✓ Zero-byte extraction succeeded, got {data.size} bytes"
  catch e =>
    IO.println s!"✗ Zero-byte extraction failed: {e}"

-- Test sequential extractions
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← EntropyArray.new ctx 64
    let (data1, arr1) ← EntropyArray.extract ctx arr 16
    let (data2, arr2) ← EntropyArray.extract ctx arr1 16
    let (data3, arr3) ← EntropyArray.extract ctx arr2 16
    let (data4, _) ← EntropyArray.extract ctx arr3 16
    let total := data1.size + data2.size + data3.size + data4.size
    IO.println s!"✓ Sequential extractions succeeded, total: {total} bytes"
  catch e =>
    IO.println s!"✗ Sequential extractions failed: {e}"

-- Test extraction from exhausted array
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← EntropyArray.new ctx 8
    let (_, exhausted) ← EntropyArray.extract ctx arr 8
    let (empty_data, _) ← EntropyArray.extract ctx exhausted 8
    IO.println s!"✓ Exhausted array extraction handled, got {empty_data.size} bytes"
  catch e =>
    IO.println s!"✗ Exhausted array extraction failed: {e}"

-- Test extraction with refresh
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← EntropyArray.new ctx 16
    let (_, exhausted) ← EntropyArray.extract ctx arr 16
    let refreshed ← EntropyArray.refresh ctx exhausted
    let (data, _) ← EntropyArray.extract ctx refreshed 8
    IO.println s!"✓ Extract after refresh succeeded, got {data.size} bytes"
  catch e =>
    IO.println s!"✗ Extract after refresh failed: {e}"

-- Test extraction from zero-sized array
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← EntropyArray.new ctx 0
    let (data, _) ← EntropyArray.extract ctx arr 1
    IO.println s!"✓ Zero-sized array extraction handled, got {data.size} bytes"
  catch e =>
    IO.println s!"✗ Zero-sized array extraction failed: {e}"

-- Test large extraction
#eval show IO Unit from do
  try
    let ctx ← Sodium.init Unit
    let arr ← EntropyArray.new ctx 1024
    let (data, _) ← EntropyArray.extract ctx arr 512
    IO.println s!"✓ Large extraction succeeded, got {data.size} bytes"
  catch e =>
    IO.println s!"✗ Large extraction failed: {e}"

end Sodium.Tests.EntropyExtraction
