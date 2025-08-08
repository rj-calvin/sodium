import «Sodium».FFI.Basic
import «Sodium».FFI.Box
import «Sodium».Crypto.Monad

open Lean Sodium Crypto

def main : IO Unit := do
  let core := show CoreM Unit from do
    let (nonce1, nonce2) ← CryptoM.toCoreM fun _ => do
      println! ← getFuel
      let n1 ← mkFreshNonceId
      println! ← getFuel
      let n2 ← mkFreshNonceId
      println! ← getFuel
      return (n1, n2)
    println! nonce1.bytes
    println! nonce2.bytes
  discard <| core.toIO {fileName := default, fileMap := default} {env := ← mkEmptyEnvironment}
