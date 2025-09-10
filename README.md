# Sodium: Cryptographic Framework for Lean4

A sophisticated cryptographic framework providing type-safe LibSodium bindings and high-level abstractions for secure communication in Lean4.

## Overview

This project implements a three-layer cryptographic architecture combining low-level FFI bindings with mathematically verified high-level abstractions. The framework is designed to support secure communication infrastructure, with particular focus on end-to-end encrypted channels for the Lean Language Server Protocol.

### Architecture

- **FFI Layer**: Direct LibSodium bindings using Alloy with secure memory management
- **Data Layer**: Type-safe abstractions with comprehensive serialization support
- **Crypto Layer**: Monadic interface integrating with Lean's metaprogramming system

## Project Structure

### FFI Modules (`Sodium/FFI/`)
Low-level bindings to LibSodium's cryptographic primitives:

- **Basic**: Core initialization and secure memory management
- **Box**: Public-key authenticated encryption (Curve25519 + XSalsa20-Poly1305)
- **SecretBox**: Secret-key authenticated encryption (XSalsa20-Poly1305) 
- **KeyExch**: Curve25519 key exchange with session key derivation
- **Aead**: Authenticated encryption with additional data (XChaCha20-Poly1305)
- **SecretStream**: Forward-secure streaming encryption with automatic rekeying
- **Sign**: Ed25519 digital signatures
- **GenericHash**: BLAKE2b cryptographic hashing
- **KeyDeriv**: Key derivation functions
- **PwHash**: Password hashing with Argon2

### Crypto Modules (`Sodium/Crypto/`)
High-level cryptographic abstractions:

- **Monad**: The `CryptoM` monad with entropy management and MetaM integration
- **Types**: Cryptographic type hierarchy with spec-based safety guarantees
- **Spec**: Type-level specifications ensuring cryptographic correctness
- **Stream**: Streaming encryption with AsyncList integration

### Data Modules (`Sodium/Data/`)
Supporting data structures and serialization:

- **ByteVector**: Fixed-size byte arrays with compile-time length tracking
- **ByteArray**: Dynamic byte array utilities
- **Encodable**: JSON serialization framework with correctness proofs
- **AsyncList**: Asynchronous streaming primitives
- **Chunk**: Efficient data chunking for streaming operations
- **Lean/Syntax**: Complete Lean AST serialization for secure LSP communication

### Test Suite (`Sodium/FFI/Tests/`)
Comprehensive testing for all FFI components with validation of:
- Cryptographic constants and parameter sizes
- Key generation and deterministic operations
- Encryption/decryption round-trips
- Error handling and edge cases

## Key Features

### Type Safety
- **Spec-based Constraints**: Compile-time verification of cryptographic parameter compatibility
- **Algorithm Binding**: Keys tied to specific algorithms with correct bit lengths
- **Size Tracking**: Type-level size guarantees preventing buffer overflows

### Security
- **Secure Memory**: All sensitive data uses `SecureVector` with `sodium_malloc()`
- **Memory Protection**: Automatic `sodium_mprotect_noaccess()` when not in use
- **Nonce Management**: Thread-safe unique nonce generation with freshness tracking
- **Forward Secrecy**: Automatic rekeying in streaming protocols

### Integration
- **MetaM Compatibility**: `CryptoM` monad integrates with Lean's metaprogramming
- **LSP Support**: Complete Lean syntax tree serialization for secure communication
- **Streaming**: AsyncList-based chunked processing for large data

## Build System

The project uses Lake with automatic LibSodium source compilation:

```bash
lake build
```

### Dependencies
- **Alloy**: FFI framework for C integration
- **Batteries**: Extended Lean standard library
- **LibSodium 1.0.20**: Automatically downloaded and compiled

## Development Status

### Completed Components
✅ **FFI Layer**: Bindings for all major LibSodium function categories  
✅ **Secure Memory**: `SecureVector` implementation with memory protection  
✅ **CryptoM Monad**: Entropy management and key derivation  
✅ **Streaming**: Forward-secure streaming with rekeying  
✅ **Serialization**: Lean syntax tree encoding for syntax sharing and syntax signatures

### In Development
🚧 **LSP Integration**: End-to-end encrypted Lean language server channels  
🚧 **Documentation**: API documentation and usage examples  
🚧 **Performance**: Optimization of streaming and serialization paths  

## Usage Example

```lean
import Sodium
open Sodium Crypto

example : CryptoM τ (KeyPair τ Curve25519) := do
  -- Generate a random keypair
  let keys ← mkFreshKeys
  return keys
  
example : CryptoM τ (CipherText XSalsa20Poly1305)
  -- Encrypt a message using the current "stale" key
  -- This is the key seeded from the metavariable context
  let key ← mkStaleKey
  let cipher ← encrypt "standard" key
  return cipher

example : CryptoM τ MVarId := do
  -- CryptoM provides a custom NameGenerator that derives thread-safe names from nonce values
  let mvar ← mkFreshMVarId
  return mvar

#eval show MetaM (PublicKey Curve25519) from do
  -- The CryptoM monad is a wrapper of MetaM
  let pkey ← CryptoM.toMetaM fun _ => do
    let keys ← mkStaleKeys
    return keys.pkey
  return pkey

```

## Security Considerations

⚠️ **Development Status**: This project is actively developed cryptographic software. While the underlying LibSodium library is production-ready, this Lean4 framework should be thoroughly audited before use in security-critical applications.

- All FFI bindings implement proper error handling and memory safety
- Cryptographic parameters are validated at compile time through the Spec system
- Test suite provides comprehensive coverage of cryptographic operations
- Secure memory management prevents key material exposure

## Resources

- [LibSodium Documentation](https://doc.libsodium.org/)
- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Alloy Documentation](https://github.com/tydeu/lean4-alloy)

## License

This project is available under the same license terms as Lean4.