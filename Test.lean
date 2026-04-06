import Sodium.Crypto.Basic

open Sodium

def main (_ : List String) : IO UInt32 := do
  let τ ← sodium Unit
  let buf : τ.Entropy ← Entropy.randomBytes 16
  let (x, _) ← buf.extractSlice 8
  println! x.toBase64
  return 0

