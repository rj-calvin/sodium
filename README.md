# Sodium - LibSodium FFI Bindings for Lean4

Lean4 bindings for the LibSodium cryptographic library.

## Project Structure

- **`Sodium/FFI/`**: Low-level FFI bindings to LibSodium functions
  - AEAD, Box, GenericHash, KeyDeriv, KeyExch, PwHash, SecretBox, SecretStream, Sign
- **`Sodium/Crypto/`**: High-level cryptographic API (work in progress)
  - Monad, Types, Specs, Stream operations, Hash operations
- **`Sodium/Data/`**: Supporting data structures
  - ByteVector, ByteArray, Chunk, AsyncList
- **`Sodium/FFI/Tests/`**: Test suite for all FFI modules

## LibSodium Resources

- [LibSodium Documentation](https://doc.libsodium.org/)
- [LibSodium GitHub](https://github.com/jedisct1/libsodium)

## Status

⚠️ **This project is still in development.**

- **FFI Layer**: Bindings available for 8 major LibSodium categories
- **High-Level API**: Work in progress (`Sodium/Crypto/` modules)

The FFI bindings are functional and tested, while the high-level cryptographic API is still being developed.