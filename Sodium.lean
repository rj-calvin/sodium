import Sodium.Crypto.Basic

open Lean Sodium

#eval show MetaM Unit from CryptoM.run (seed := ByteVector.ofBase64? "5Fo8atebrSv91m9mhX4S3zvBsY4eTABdO0QZ8-C0yJk=") fun (_ : Sodium Unit) => do
  let nonce ← mkFreshNonce `nonce
  println! nonce.toJson

