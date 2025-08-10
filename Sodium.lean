-- This module serves as the root of the `Sodium` library.
-- Import modules here that should be built as part of the library.
import «Sodium».Crypto.Monad
import «Sodium».Crypto.Box
import «Sodium».Crypto.SecretBox

open Lean Sodium Crypto SecretBox

#eval show CoreM Unit from do
  CryptoM.toCoreM fun _ => do
    let key ← mkSubKey
    let cipher ← encrypt key "hello world"
    println! cipher.bytes.toBase64
    let .ok msg := ← decrypt key cipher | return ()
    println! (msg : String)
