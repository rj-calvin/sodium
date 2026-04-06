import Lean.Data.Json
import Sodium.Data.ByteVector

namespace ByteArray

@[extern "lean_sodium_bytes_increment"]
opaque succ (bytes : ByteArray) : BaseIO ByteArray

@[extern "lean_sodium_bytes_to_base64"]
opaque toBase64 (bytes : @& ByteArray) : String

@[extern "lean_sodium_bytes_of_base64"]
opaque ofBase64? (str : @& String) : Option ByteArray

private def toJson.impl : ByteArray → Lean.Json := .str ∘ toBase64

private def fromJson?.impl (json : Lean.Json) : Except String ByteArray := do
  let str ← json.getStr?
  match ofBase64? str with
  | some bytes => pure bytes
  | none => throw "expected Base64 encoding"

@[implemented_by toJson.impl]
protected def toJson (bytes : ByteArray) : Lean.Json :=
  .arr (bytes.data.map (.num ∘ .fromNat ∘ UInt8.toNat))

@[implemented_by fromJson?.impl]
protected def fromJson? (json : Lean.Json) : Except String ByteArray := do
  let arr ← json.getArr?
  let arr ← arr.mapM (·.getNat?)
  return ⟨arr.map (·.toUInt8)⟩

instance : Lean.ToJson ByteArray := ⟨ByteArray.toJson⟩
instance : Lean.FromJson ByteArray := ⟨ByteArray.fromJson?⟩

end ByteArray

namespace ByteVector

@[extern "lean_sodium_bytes_increment_vec"]
opaque succ (bytes : ByteVector n) : BaseIO (ByteVector n)

abbrev toBase64 (bytes : ByteVector n) := bytes.toByteArray.toBase64

def ofBase64? (str : String) : Option (ByteVector n) := do
  let bytes ← ByteArray.ofBase64? str
  if h : bytes.size = n then some ⟨bytes, h⟩
  else none

protected abbrev toJson : ByteVector n → Lean.Json := Lean.toJson ∘ ByteVector.toByteArray

protected def fromJson? (json : Lean.Json) : Except String (ByteVector n) := do
  let bytes ← Lean.fromJson? (α := ByteArray) json
  if h : bytes.size = n then return ⟨bytes, h⟩
  else throw s!"expected exactly {n} bytes"

instance : Lean.ToJson (ByteVector n) := ⟨ByteVector.toJson⟩
instance : Lean.FromJson (ByteVector n) := ⟨ByteVector.fromJson?⟩

end ByteVector
