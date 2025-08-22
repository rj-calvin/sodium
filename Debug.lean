import Sodium.FFI.SecretStream

open Lean Sodium FFI SecretStream

def main : IO Unit := do
  let τ ← init Unit
  let key ← keygen (τ := τ)
  let (st, header) ← streamInitPush key
  let message1 : ByteVector 16 := ByteVector.replicate 16 65 -- 16 'A's
  let additionalData : ByteVector 4 := ByteVector.replicate 4 68 -- 4 'D's
  let cipher1 ← streamPush st message1 additionalData STREAM_TAG_MESSAGE
  IO.println s!"✓ Encrypted message 1 (size: {cipher1.size} bytes, tag: MESSAGE)"
