-- import Tests.SodiumInit
-- import Tests.EntropyArray
-- import Tests.EntropyExtraction
-- import Tests.SecureArray
-- import Tests.SecureArrayComparison
-- import Tests.SecureFileLoad
-- import Tests.SecureFileStore
-- import Tests.Box
-- import Tests.SecretBox
-- import Tests.KeyExch
-- import Tests.ByteArray
-- import Tests.KeyDeriv

import «Sodium».FFI.KeyExch

open Sodium.FFI.KeyExch

def main : IO Unit := do
  let ctx ← Sodium.init Unit
  IO.println "Initialized Sodium context"

  let (publicKey, _secretKey) ← keypair (τ := ctx)
  IO.println s!"Generated keypair successfully, size: {publicKey.size}"

  -- Try to access the public key
  IO.println s!"Public key generated"

  IO.println "Keypair test completed"
