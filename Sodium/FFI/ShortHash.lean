import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI

-- Short hash constants (SipHash-2-4)
def SHORTHASH_BYTES : UInt32 := 8
def SHORTHASH_KEYBYTES : UInt32 := 16

-- SipHashx-2-4 constants (128-bit output variant)
def SHORTHASH_X_2_4_BYTES : UInt32 := 16
def SHORTHASH_X_2_4_KEYBYTES : UInt32 := 16

/- SipHash-2-4 Functions (64-bit output) -/

alloy c extern "lean_crypto_shorthash_keygen"
def shortHashKeygen : BaseIO ByteArray :=
  lean_object* key = lean_alloc_sarray(sizeof(unsigned char), crypto_shorthash_KEYBYTES, crypto_shorthash_KEYBYTES)
  crypto_shorthash_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c extern "lean_crypto_shorthash"
def shortHash (message : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_shorthash_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 16 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* hash = lean_alloc_sarray(sizeof(unsigned char), crypto_shorthash_BYTES, crypto_shorthash_BYTES)

  int result = crypto_shorthash(
    lean_sarray_cptr(hash),
    lean_sarray_cptr(message), lean_sarray_size(message),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(hash)
    lean_object* error_msg = lean_mk_string("Short hash computation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(hash)

/- SipHashx-2-4 Functions (128-bit output) -/

alloy c extern "lean_crypto_shorthash_siphashx24"
def shortHashx24 (message : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_shorthash_siphashx24_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 16 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* hash = lean_alloc_sarray(sizeof(unsigned char), crypto_shorthash_siphashx24_BYTES, crypto_shorthash_siphashx24_BYTES)

  int result = crypto_shorthash_siphashx24(
    lean_sarray_cptr(hash),
    lean_sarray_cptr(message), lean_sarray_size(message),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(hash)
    lean_object* error_msg = lean_mk_string("SipHashx-2-4 computation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(hash)

end Sodium.FFI
