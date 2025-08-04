# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This repository contains Lean4 FFI bindings for the LibSodium cryptographic library. LibSodium is a modern, easy-to-use crypto library that provides encryption, decryption, signatures, password hashing, and more. The goal is to make LibSodium's C API accessible from Lean4 with proper type safety and memory management.

## Build System

- **Build**: `lake build` - Compiles the Lean4 code and native C components
- **Build tests**: `lake build Tests` - Builds the test executable
- **Clean build**: `lake clean && lake build` - Forces complete rebuild
- **Check errors**: Always run `lake build` after making changes to verify type correctness

## FFI Architecture with Alloy

### Core Structure
- `Sodium.lean` - Main module that imports all FFI submodules
- `Sodium/FFI/Basic.lean` - Core FFI bindings (sodium_init, random number generation)
- `Sodium/FFI/Box.lean` - Public-key authenticated encryption (crypto_box)
- `Sodium/FFI/SecretBox.lean` - Secret-key authenticated encryption (crypto_secretbox)
- `Sodium/FFI/GenericHash.lean` - Generic hashing (crypto_generichash/BLAKE2b)
- `Sodium/FFI/SecretStream.lean` - Secret stream AEAD (crypto_secretstream_xchacha20poly1305)
- `Sodium/FFI/Sign.lean` - Digital signatures (crypto_sign/Ed25519)
- `Sodium/FFI/PwHash.lean` - Password hashing (crypto_pwhash/Argon2)
- `Sodium/FFI/Aead.lean` - AEAD variants (crypto_aead_chacha20poly1305, crypto_aead_xchacha20poly1305)
- `Sodium/FFI/Stream.lean` - Stream ciphers (crypto_stream, ChaCha20, Salsa20, XChaCha20, XSalsa20)
- `Sodium/Crypto/Types.lean` - Type-safe wrappers with compile-time size guarantees
- `Sodium/Crypto/Monad.lean` - CryptoM monad for stateful crypto operations
- `Sodium/Data/ByteArray.lean` - ByteArray utilities and operations
- `Sodium/Data/Nat.lean` - Natural number utilities
- `Sodium/Tests/` - Comprehensive test modules for each FFI component
- `Tests.lean` - Main test executable entry point
- `lakefile.lean` - Build configuration with Alloy integration and LibSodium linking

### Alloy FFI Binding Pattern
This project uses **Alloy** to write C code directly in Lean files. Follow this pattern:

1. **Alloy Declaration** (in .lean files):
```lean
import Alloy.C
open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

alloy c extern "lean_sodium_function_name"
def sodium_function_name (arg1 : ArgType1) (arg2 : ArgType2) : BaseIO ResultType :=
  // C code here
  int result = sodium_actual_function(arg1, arg2)
  return lean_io_result_mk_ok(lean_box(result))
```

2. **No separate C files needed** - Alloy generates all C code automatically

### Alloy Advantages
- **Embedded C**: Write C directly in `.lean` files using `alloy c extern` syntax
- **Type Safety**: Automatic conversions between Lean and C types
- **Memory Management**: Built-in reference counting with `lean_inc_ref()` and `lean_dec_ref()`
- **Simplified Build**: No manual C file compilation needed

### Type Conversion Guidelines

- **Simple types**: `UInt8`, `UInt32`, `UInt64`, `Float` map directly to C types
- **Buffers/Arrays**: Use `ByteArray` for binary data, convert with `lean_sarray_cptr()`
- **Strings**: Convert with `lean_string_cstr()` for C string compatibility
- **IO Functions**: Always include `lean_obj_arg world` parameter and return `lean_obj_res`
- **Error Handling**: LibSodium functions return 0 on success, -1 on error

### Memory Management Rules

- **Initialization**: Call `sodium_init()` before any other LibSodium functions
- **Reference Counting**: Use `lean_inc_ref()` and `lean_dec_ref()` for object lifetime
- **External Resources**: Create finalizers for resources that need cleanup
- **Thread Safety**: LibSodium is thread-safe on POSIX systems

### LibSodium API Categories (Implementation Status)

**Current Coverage**: 14/14 major categories (100% complete) with 100 FFI function bindings

✅ **Fully Implemented (14 categories):**
1. **Core Initialization & Utilities**: `sodium_init()`, memory utilities, constant-time verification - in `Sodium/FFI/Basic.lean` + `Sodium/FFI/Utils.lean`
2. **Random Number Generation**: `randombytes_*` - cryptographically secure RNG - in `Sodium/FFI/Basic.lean`
3. **Public-key Encryption**: `crypto_box_*` (Curve25519/XSalsa20/Poly1305) - authenticated encryption, sealed boxes - in `Sodium/FFI/Box.lean`
4. **Secret-key Encryption**: `crypto_secretbox_*` (XSalsa20/Poly1305) - authenticated encryption - in `Sodium/FFI/SecretBox.lean`
5. **Generic Hashing**: `crypto_generichash_*` (BLAKE2b) - streaming hash support - in `Sodium/FFI/GenericHash.lean`
6. **Digital Signatures**: `crypto_sign_*` (Ed25519) - signing, verification, detached signatures - in `Sodium/FFI/Sign.lean`
7. **Password Hashing**: `crypto_pwhash_*` (Argon2id) - key derivation, password verification - in `Sodium/FFI/PwHash.lean`
8. **Secret Stream AEAD**: `crypto_secretstream_xchacha20poly1305_*` - streaming authenticated encryption - in `Sodium/FFI/SecretStream.lean`
9. **AEAD Variants**: `crypto_aead_*` (ChaCha20-Poly1305 IETF/Original, XChaCha20-Poly1305 IETF) - modern AEAD standards - in `Sodium/FFI/Aead.lean`
10. **Key Derivation**: `crypto_kdf_*` (BLAKE2b, HKDF-SHA256/512) - master key to subkey derivation - in `Sodium/FFI/KeyDeriv.lean`
11. **Key Exchange**: `crypto_kx_*` (X25519) - secure key agreement protocol - in `Sodium/FFI/KeyExch.lean`
12. **Short Hashing**: `crypto_shorthash_*` (SipHash-2-4) - fast non-cryptographic hashing - in `Sodium/FFI/ShortHash.lean`
13. **Authentication (MAC)**: `crypto_auth_*` (HMAC-SHA256/512/512-256) - message authentication codes - in `Sodium/FFI/Auth.lean`
14. **Stream Ciphers**: `crypto_stream_*` (ChaCha20, Salsa20, XChaCha20, XSalsa20) - raw encryption streams - in `Sodium/FFI/Stream.lean`

🎉 **Complete Coverage Achieved!** All 14 major LibSodium categories are now fully implemented.

**Advanced/Optional:**
- **AEAD Hardware Acceleration**: `crypto_aead_aes256gcm_*`, `crypto_aead_aegis128l_*`, `crypto_aead_aegis256_*`
- **Low-level Primitives**: `crypto_core_*`, `crypto_scalarmult_*` - building blocks for custom constructions
- **Additional Hash**: `crypto_hash_*` (SHA-256, SHA-512) - standard hash functions

### Build Configuration with Alloy

The `lakefile.lean` includes:
- Alloy dependency: `require alloy from git "https://github.com/tydeu/lean4-alloy.git"@"master"`
- Batteries dependency: `require "leanprover-community" / "batteries" @ git "v4.21.0"`
- LibSodium built from source using `extern_lib libsodium` configuration
- Alloy native facets configured for C code generation
- Module data exports for Alloy C object files
- Test executable configuration with interpreter support

### LibSodium Build System

This project **builds LibSodium from source** automatically during the build process:
- **Version**: LibSodium 1.0.20 is downloaded and compiled automatically
- **Build Process**: The lakefile downloads the source tarball, configures with `./configure`, and builds both static and shared libraries
- **No System Dependencies**: No need to install system LibSodium packages
- **Portability**: Works across different platforms without requiring pre-installed LibSodium
- **Build Location**: Libraries are built in `build/libsodium-build/` directory

**Note**: While system LibSodium can be verified with `pkg-config --libs libsodium`, this project doesn't use it.

### Safety Considerations

- Always validate buffer sizes before passing to LibSodium
- Use LibSodium's secure memory functions when available
- Implement proper error propagation from C to Lean
- Never expose raw pointers in the public Lean API
- Use opaque types for sensitive data structures

### Testing Strategy

- **Comprehensive Test Suite**: Each FFI module has corresponding test modules in `Sodium/Tests/`
- **Unit Tests**: Test each bound function with valid inputs and edge cases
- **Error Handling**: Verify proper error propagation and exception handling
- **Memory Safety**: Test with different buffer sizes and boundary conditions
- **Integration Tests**: Test complete cryptographic workflows
- **Type Safety**: Leverage Lean's type system to prevent misuse at compile time

### Interactive Testing with Alloy

**Important Limitation**: Alloy doesn't support running `#eval` on C code in the same module where it is defined. For testing:

1. **Separate test modules**: Create test files that import FFI modules
2. **Test executable**: Use `lake build Tests` to build the comprehensive test suite
3. **Interactive testing**: Import and test FFI functions from separate modules

```lean
-- In a separate test file (not the same file as FFI definitions)
import «Sodium».FFI.Basic

def testSodiumInit : IO Unit := do
  let result ← sodiumInit
  if result = 0 then
    IO.println "✓ Sodium initialized successfully"
  else
    IO.println "✗ Sodium initialization failed"

#eval testSodiumInit
```

The project includes comprehensive test modules in `Sodium/Tests/` for each FFI component.

### Error Handling in FFI

**For functions that can fail:**
- Use `IO α` (not `BaseIO α`) in Alloy function signatures
- In C code, create proper `IO.Error.userError` constructors:
  ```c
  // Create IO.Error.userError
  lean_object* error_msg = lean_mk_string("Error message")
  lean_object* io_error = lean_alloc_ctor(7, 1, 0)  // userError constructor (tag 7)
  lean_ctor_set(io_error, 0, error_msg)
  return lean_io_result_mk_error(io_error)
  ```
- In Lean, use try/catch syntax to handle exceptions:
  ```lean
  try
    let result ← ffiFunction arg
    -- success handling
  catch e =>
    -- error handling
  ```

**Important:** `BaseIO` cannot throw exceptions (error type is `Empty`). Always use `IO` for functions that need error handling.

### Common Pitfalls

- Missing `sodium_init()` call causes undefined behavior
- Incorrect buffer size calculations leading to memory corruption
- Improper reference counting causing memory leaks
- Exposing internal LibSodium implementation details in public API

## Development Workflow

1. Identify LibSodium function to bind
2. Design Lean type signature with appropriate safety guarantees
3. Implement Alloy FFI binding in appropriate `Sodium/FFI/*.lean` file
4. Add import to `Sodium.lean` if needed
5. Run `lake build` to check for compilation errors
6. Create corresponding tests in `Sodium/Tests/*.lean`
7. Add test import to `Tests.lean`
8. Run `lake build Tests` to verify test compilation
9. Test functionality and document any special usage requirements

## Current Project Status

**Lean Version**: 4.21.0  
**LibSodium Version**: 1.0.20 (built from source)  
**Architecture**: Modular FFI bindings with type-safe wrappers and comprehensive testing  
**Code Statistics**: 
- **Total Lines**: ~4,200 lines across FFI and test modules
- **FFI Bindings**: 100 distinct Alloy extern function bindings
- **API Coverage**: 14/14 major LibSodium categories (100% complete)
- **Test Coverage**: Comprehensive test modules for each implemented component

**Implementation Quality**: 
- ✅ Memory-safe with proper reference counting
- ✅ Type-safe wrappers with compile-time guarantees  
- ✅ Comprehensive error handling and propagation
- ✅ Automatic LibSodium source building (no system dependencies)
- ✅ Full test coverage for implemented APIs
- ✅ Clean Alloy integration with embedded C code

**Development Status**: 🎉 **FFI LAYER COMPLETE!** **100% LibSodium API coverage achieved** - a remarkable milestone! All 14 major cryptographic categories are now fully implemented with comprehensive FFI bindings, type safety, memory management, and test coverage.

**Next Phase - High-Level Abstractions**: While the low-level FFI bindings are complete, the project now focuses on **API ergonomics** and providing high-level abstractions that make cryptographic operations more intuitive and safe for end users. This includes:

- **Type-Safe Wrappers**: Building on `Sodium/Crypto/Types.lean` for compile-time size guarantees
- **Monadic Interfaces**: Expanding `Sodium/Crypto/Monad.lean` for stateful crypto operations  
- **Ergonomic APIs**: Creating user-friendly interfaces that abstract away low-level details
- **Safe Defaults**: Providing secure-by-default configurations and best practices
- **Documentation**: Comprehensive usage examples and security guidelines

The objective has shifted from **coverage** to **usability** - making LibSodium's power accessible through elegant, type-safe Lean4 abstractions.