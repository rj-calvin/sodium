-- This module serves as the root of the `Sodium` library.
-- Import modules here that should be built as part of the library.
import «Sodium».FFI.Basic
import «Sodium».FFI.Box
import «Sodium».Crypto.Monad

open Lean Sodium Crypto

#eval show CoreM Unit from do
  CryptoM.toCoreM fun τ => do
    let nonce ← extractEntropy 24
    let (pk, sk) ← FFI.Box.keypair τ
    let cipher ← FFI.Box.easy τ "hello world".toUTF8 nonce pk sk
    println! cipher.toBase64
    let msg ← FFI.Box.openEasy τ cipher nonce pk sk
    println! String.fromUTF8! msg
