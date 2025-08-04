# Sodium - LibSodium FFI Bindings for Lean4

Type-safe Lean4 bindings for the LibSodium cryptographic library, providing compile-time size guarantees and memory-safe cryptographic operations.

## Features

- **LibSodium coverage**: 14/14 major categories, 100+ FFI function bindings
- **[Alloy](https://github.com/tydeu/lean4-alloy) integration**: C code embedded directly in Lean files

## Quick Start

```bash
# Build the project
lake build

# Run tests
lake build Tests

# Clean build
lake clean && lake build
```

## LibSodium Resources

- [LibSodium Documentation](https://doc.libsodium.org/)
- [LibSodium GitHub](https://github.com/jedisct1/libsodium)

## Status

⚠️ **This project is still in development.** APIs may change and some features are not yet stabilized.

Current implementation provides FFI bindings for all major LibSodium categories including symmetric/asymmetric encryption, digital signatures, hashing, key exchange, and more.