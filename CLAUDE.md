# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This repository contains Lean4 FFI bindings for the LibSodium cryptographic library. LibSodium is a modern, easy-to-use crypto library that provides encryption, decryption, signatures, password hashing, and more. The goal is to make LibSodium's C API accessible from Lean4 with proper type safety and memory management.

## Build System

- **Build**: `lake build` - Compiles the Lean4 code and native C components
- **Build tests**: `lake build Tests` - Builds the test executable
- **Clean build**: `lake clean && lake build` - Forces complete rebuild
- **Check errors**: Always run `lake build` after making changes to verify type correctness

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
- **Supply-chain Risk**: Automatically pulling source code opens the project to potential supply-chain attacks
- **Build Location**: Libraries are built in `build/libsodium-build/` directory

**Note**: While system LibSodium can be verified with `pkg-config --libs libsodium`, this project doesn't use it.

### Safety Considerations

- Always validate buffer sizes before passing to LibSodium
- Use LibSodium's secure memory functions when available
- Implement proper error propagation from C to Lean
- Never expose raw pointers in the public Lean API
- Use opaque types for sensitive data structures

### Interactive Testing with Alloy

**Important Limitation**: Alloy doesn't support running `#eval` on C code in the same module where it is defined. For testing:

1. **Separate test modules**: Create test files that import FFI modules
2. **Test executable**: Use `lean-lsp` to review messages from all `#eval` commands in a test suite
3. **Interactive testing**: Import and test FFI functions from separate modules

```lean
-- In a separate test file (not the same file as FFI definitions)
import «Sodium».FFI.Basic

#eval show IO Unit from do
  let result ← sodiumInit
  if result = 0 then
    IO.println "✓ Sodium initialized successfully"
  else
    IO.println "✗ Sodium initialization failed"

#eval testSodiumInit
```

The project includes comprehensive test modules in `Tests/` for each FFI component.

### Error Handling in FFI

**For functions that can fail:**
- Use `IO α` (not `BaseIO α`) in Alloy function signatures that can encounter errors
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

## Development Workflow

1. Identify LibSodium function to bind
2. Design Lean type signature with appropriate safety guarantees
3. Implement Alloy FFI binding in appropriate `Sodium/FFI/*.lean` file
4. Add import to `Sodium.lean` if needed
5. Check `lake build` to check for alloy compilation errors
5. Check `lean-lsp` to check for type errors
6. Create corresponding tests in `Tests/*.lean`
8. Add `#eval` commands to verify test expressions - use `lean-lsp` to check messages
9. Test functionality and document any special usage requirements
