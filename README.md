# Sodium

LibSodium bindings for Lean 4.

Sodium provides FFI bindings to LibSodium's cryptographic primitives through
[Alloy](https://github.com/tydeu/lean4-alloy), along with high-level monadic
interfaces that integrate with Lean's metaprogramming system.

## Using Sodium

```lean
import Sodium

open Lean Sodium Crypto

-- CryptoM integrates with MetaM to align cryptographic determinism with `MetavarContext.depth`
#eval show MetaM Unit from CryptoM.toMetaM fun _ => do
  -- Generate random curve25519 keys
  let keys ← mkFreshKeys
  
  -- Derive a symmetric key from the current position in key-hierarchy (the current metakey and depth)
  let key : SymmKey _ Blake2b ← mkStaleKey fun x => x.cast

  -- Nonce generation is thread-safe. A random default is chosen per spec, followed by little-endian increments
  let nonce ← mkFreshNonce (spec := XSalsa20Poly1305)
```

### Configuration

In your `lakefile.lean`:

```lean
require sodium from git "https://github.com/rj-calvin/sodium.git"@"main" -- no stable release available yet.

-- Sodium modules can use Alloy's native facets
lean_lib MySodiumApp where
  nativeFacets := fun shouldExport =>
    if shouldExport then
      #[Module.oExportFacet, Module.coExportFacet] 
    else
      #[Module.oNoExportFacet, Module.coNoExportFacet]
```

## Status

Sodium remains a **work-in-progress.** Present bindings should be useful, but
may be subject to change as the repository matures.

Current focus is on E2E-encrypted communication and infrastructure for
collaborative theorem proving and distributed syntax sharing.
