import «Sodium».Crypto.Monad
import «Sodium».Data.Digest

open Lean Sodium Crypto

#eval show MetaM Json from CryptoM.toMetaM fun _ => do
  let sig ← sign (json% {some: "string"})
  println! digest sig
  return encode sig
