# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This repository implements a sophisticated cryptographic framework for Lean4, combining low-level LibSodium FFI bindings with high-level cryptographic abstractions. The project serves dual purposes:

1. **Cryptographic Library**: Type-safe FFI bindings to LibSodium with secure memory management
2. **Secure Communication Infrastructure**: Building toward end-to-end encrypted channels for the Lean Language Server Protocol (LSP)

The architecture features a three-layer design:
- **FFI Layer**: Direct LibSodium bindings using Alloy
- **Data Layer**: Type-safe abstractions with Lean.Syntax serialization
- **Crypto Layer**: Monadic interface integrating with Lean's MetaM

The long-term vision is to enable secure, authenticated communication channels for Lean's language server, allowing encrypted theorem proving and secure code collaboration.

## Architecture

### Core Components

**FFI Modules** (`Sodium.FFI.*`):
- `Basic`: Core LibSodium initialization and secure memory management
- `Box`: Public-key authenticated encryption (Curve25519 + XSalsa20-Poly1305)
- `SecretBox`: Secret-key authenticated encryption (XSalsa20-Poly1305)
- `KeyExch`: Key exchange using Curve25519 with session derivation
- `Aead`: Authenticated encryption with additional data (XChaCha20-Poly1305)
- `SecretStream`: Streaming encryption with forward secrecy
- `Sign`: Digital signatures using Ed25519
- `GenericHash`: BLAKE2b cryptographic hashing with keyed variants

**Data Modules** (`Sodium.Data.*`):
- `ByteVector`: Fixed-size byte arrays with compile-time length tracking
- `Encodable`: JSON serialization framework with mathematical correctness proofs
- `AsyncList`: Asynchronous streaming primitives for chunked encryption
- `Lean.Syntax`: Complete Lean AST serialization for secure LSP communication

**Crypto Modules** (`Sodium.Crypto.*`):
- `Monad`: The `CryptoM` monad integrating with Lean's `MetaM`
- `Types`: Cryptographic type hierarchy with spec-based safety
- `Spec`: Type-level specifications ensuring cryptographic correctness
- `Stream`: High-level streaming encryption with automatic rekeying

### Type Safety System

The project uses a sophisticated `Spec`-based type system to ensure cryptographic correctness:

```lean
-- Specs define valid shapes for cryptographic primitives
variable (spec : Spec) [spec.HasValidShape `nonce] [spec.HasValidShape `symmkey]

-- Keys are tied to specific algorithms and bit lengths
def key : SymmKey τ XSalsa20 := ...  -- Exactly 32 bytes
def nonce : Nonce XSalsa20Poly1305 := ...  -- Exactly 24 bytes
```

This prevents common cryptographic errors like key/nonce reuse or size mismatches at compile time.

## Build System

- **Build**: `lake build` - Compiles the Lean4 code and native C components
- **Build tests**: `lake build Tests` - Builds the test executable  
- **Debug build**: Debug executable with symbols and no optimization
- **Clean build**: `lake clean && lake build` - Forces complete rebuild
- **Check errors**: Always run `lake build` after making changes to verify type correctness

### Dependencies and Configuration

The `lakefile.lean` includes:
- **Alloy**: `require alloy from git "https://github.com/tydeu/lean4-alloy.git"@"master"`
- **Batteries**: `require "leanprover-community" / "batteries" @ git "v4.21.0"`
- **Aesop**: `require aesop from git "https://github.com/leanprover-community/aesop.git" @ "v4.21.0"`
- **LibSodium**: Built from source using `extern_lib libsodium` configuration
- **Module facets**: Alloy native facets configured for C code generation with export/no-export variants

### LibSodium Build System

This project **builds LibSodium from source** automatically during the build process:
- **Version**: LibSodium 1.0.20 is downloaded and compiled automatically  
- **Build Process**: The lakefile downloads the source tarball, configures with `./configure --enable-shared --enable-static`, and builds both library types
- **No System Dependencies**: No need to install system LibSodium packages
- **Portability**: Works across different platforms without requiring pre-installed LibSodium
- **Supply-chain Risk**: Automatically pulling source code opens the project to potential supply-chain attacks
- **Build Location**: Libraries are built in `build/libsodium-build/` directory
- **Configuration**: Uses `-fPIC` for position-independent code and includes debug symbols

**Note**: While system LibSodium can be verified with `pkg-config --libs libsodium`, this project doesn't use it for portability.

### Memory Safety and Security

**Secure Memory Management**:
- All sensitive data uses `SecretVector` with `sodium_malloc()` allocation
- Memory protection with `sodium_mprotect_noaccess()` when not in use
- Automatic secure deallocation with `sodium_free()` in finalizers
- Random initialization of all allocated secure memory

**FFI Safety Patterns**:
- Opaque `SecurePointed` type prevents direct pointer access
- Size tracking at the type level with `USize` parameters  
- Memory protection state changes only within controlled FFI boundaries
- Cross-module secure pointer conversion through dedicated C functions

**Type-Level Guarantees**:
- `Spec` constraints prevent algorithm/key size mismatches
- Compile-time verification of cryptographic parameter compatibility
- Nonce freshness tracking through the `CryptoM` monad
- Automatic entropy management with configurable pool sizes

## The CryptoM Monad

The `CryptoM` monad is the high-level interface for cryptographic operations, integrating with Lean's metaprogramming system:

```lean
-- CryptoM integrates with MetaM for Lean integration
abbrev CryptoM (τ : Sodium σ) := ReaderT (CryptoContext τ) MetaM

-- Context includes entropy pool, master key, and BLAKE2b context
structure CryptoContext (τ : Sodium σ) where
  mtx : Mutex (EntropyState τ)  -- Thread-safe entropy management
  mkey : SymmKey τ Blake2b       -- Master key for key derivation
  ctx : Context Blake2b          -- Personalization context
```

**Key Features**:
- **Entropy Management**: Configurable entropy pool with automatic refresh
- **Nonce Generation**: Thread-safe, unique nonce generation per cryptographic spec
- **Key Derivation**: Hierarchical key derivation using BLAKE2b-based KDF
- **Session Management**: Curve25519 key exchange with separate RX/TX keys
- **MetaM Integration**: Compatible with Lean's metaprogramming and proof contexts

### Testing and Development

**Testing Pattern**:
All FFI functions must be tested in separate modules due to Alloy limitations:

```lean
-- In Sodium/FFI/Tests/Box.lean (separate from FFI definitions)
import «Sodium».FFI.Basic
import «Sodium».FFI.Box

#eval show IO Unit from do
  let ctx ← Sodium.init Unit
  let (publicKey, secretKey) ← keypair (τ := ctx)
  IO.println s!"✓ Generated {publicKey.size}-byte public key"
```

**Test Organization**:
- Each FFI module has a corresponding test module in `Sodium/FFI/Tests/`
- Tests validate constants, key generation, encryption/decryption round-trips
- Integration tests use the `CryptoM` monad for realistic workflows
- Use `lean-lsp` diagnostic messages to review all `#eval` outputs

## Streaming and LSP Integration

### Secure Streaming (`Sodium.Crypto.Stream`)

The streaming system provides forward-secure communication with automatic rekeying:

```lean
-- SecretEncoder for outbound streams
structure SecretEncoder (τ : Sodium σ) where
  closed : IO.Ref Bool
  header : Header XChaCha20Poly1305
  stream : SecureStream τ

-- SecretDecoder for inbound streams  
structure SecretDecoder (τ : Sodium σ) where
  closed : IO.Ref Bool
  buffer : IO.Ref (List Json)
  stream : SecureStream τ
```

**Features**:
- **AsyncList Integration**: Streaming encryption returns `IO.AsyncList` for efficient chunked processing
- **Automatic Rekeying**: Periodic rekeying for forward secrecy
- **Tag-based Protocol**: `.message`, `.push`, `.final`, `.rekey` tags for stream control
- **Chunked Serialization**: `ToChunks`/`FromChunks` typeclasses for efficient large data handling

### Lean Syntax Serialization

The `Sodium.Lean.Syntax` module provides complete serialization of Lean's AST:

```lean
-- All core Lean syntax types are encodable
instance : Encodable Name := ...
instance : Encodable SourceInfo := ...
instance : Encodable Syntax := ...
instance : Encodable (TSyntax kind) := ...
```

This enables:
- **Secure LSP Communication**: Encrypted transmission of Lean syntax trees
- **Remote Theorem Proving**: Authenticated sharing of proof terms
- **Collaborative Development**: End-to-end encrypted code synchronization

### Error Handling

**FFI Error Patterns**:
- Use `IO α` (not `BaseIO α`) for functions that can fail
- C code creates proper `IO.Error.userError` with `lean_mk_io_user_error()`
- Lean code uses try/catch for exception handling

**CryptoM Error Types**:
```lean
inductive CryptoMessage
  | specViolation (spec : Spec) (kind : Name)
  | insufficientEntropy (bytes : Nat)

inductive DecryptResult (α : Type)
  | refused | mangled | unknown | almost | accepted
```

## Development Workflow

### Adding New Cryptographic Operations

1. **Research LibSodium API**: Check `.lake/build/libsodium-build/libsodium-1.0.20/src/libsodium/include/sodium/`
2. **Design Spec**: Create or extend `Spec` definitions for new algorithm parameters
3. **Implement FFI Binding**: Add to appropriate `Sodium/FFI/*.lean` file using Alloy
4. **Add Type Wrappers**: Create high-level types in `Sodium/Crypto/Types.lean`
5. **Extend CryptoM**: Add monadic interface functions to `Sodium/Crypto/Monad.lean`
6. **Create Tests**: Add comprehensive tests to `Sodium/FFI/Tests/*.lean`
7. **Verify Build**: Run `lake build` and check `lean-lsp` diagnostics
8. **Integration Test**: Test end-to-end workflows with the `CryptoM` monad

### Working with the Codebase

- **Build System**: Always run `lake build` after changes to verify compilation
- **Testing**: Use separate test modules and check `#eval` outputs in `lean-lsp`
- **Type Safety**: Leverage the `Spec` system to prevent cryptographic errors at compile time
- **Memory Management**: Use `SecretVector` for all sensitive data, never raw pointers
- **Documentation**: Follow existing patterns for mathematical proofs in `Encodable` instances

The project maintains mathematical rigor through comprehensive correctness proofs while providing practical cryptographic functionality for real-world applications.
