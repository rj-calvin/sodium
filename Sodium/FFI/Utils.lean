import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI

alloy c extern "lean_sodium_memcmp"
def sodiumMemcmp (b1 : ByteArray) (b2 : ByteArray) : IO Int32 :=
  size_t len1 = lean_sarray_size(b1)
  size_t len2 = lean_sarray_size(b2)
  if (len1 != len2) {
    lean_object* error_msg = lean_mk_string("Buffer sizes must be equal for comparison")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }
  
  int result = sodium_memcmp(lean_sarray_cptr(b1), lean_sarray_cptr(b2), len1)
  return lean_io_result_mk_ok(lean_box(result))

alloy c extern "lean_sodium_memzero"
def sodiumMemzero (buffer : ByteArray) : IO Unit :=
  size_t len = lean_sarray_size(buffer)
  sodium_memzero(lean_sarray_cptr(buffer), len)
  return lean_io_result_mk_ok(lean_box(0))

alloy c extern "lean_sodium_compare"
def sodiumCompare (b1 : ByteArray) (b2 : ByteArray) : IO Int32 :=
  size_t len1 = lean_sarray_size(b1)
  size_t len2 = lean_sarray_size(b2)
  if (len1 != len2) {
    lean_object* error_msg = lean_mk_string("Buffer sizes must be equal for comparison")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }
  
  int result = sodium_compare(lean_sarray_cptr(b1), lean_sarray_cptr(b2), len1)
  return lean_io_result_mk_ok(lean_box(result))

alloy c extern "lean_sodium_is_zero"
def sodiumIsZero (buffer : ByteArray) : IO Bool :=
  size_t len = lean_sarray_size(buffer)
  int result = sodium_is_zero(lean_sarray_cptr(buffer), len)
  uint8_t is_zero = (result == 1)
  return lean_io_result_mk_ok(lean_box(is_zero))

alloy c extern "lean_crypto_verify_16"
def cryptoVerify16 (x : ByteArray) (y : ByteArray) : IO Bool :=
  size_t x_size = lean_sarray_size(x)
  size_t y_size = lean_sarray_size(y)
  if (x_size != 16 || y_size != 16) {
    lean_object* error_msg = lean_mk_string("Both buffers must be exactly 16 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }
  
  int result = crypto_verify_16(lean_sarray_cptr(x), lean_sarray_cptr(y))
  uint8_t is_equal = (result == 0)
  return lean_io_result_mk_ok(lean_box(is_equal))

alloy c extern "lean_crypto_verify_32"
def cryptoVerify32 (x : ByteArray) (y : ByteArray) : IO Bool :=
  size_t x_size = lean_sarray_size(x)
  size_t y_size = lean_sarray_size(y)
  if (x_size != 32 || y_size != 32) {
    lean_object* error_msg = lean_mk_string("Both buffers must be exactly 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }
  
  int result = crypto_verify_32(lean_sarray_cptr(x), lean_sarray_cptr(y))
  uint8_t is_equal = (result == 0)
  return lean_io_result_mk_ok(lean_box(is_equal))

alloy c extern "lean_crypto_verify_64"
def cryptoVerify64 (x : ByteArray) (y : ByteArray) : IO Bool :=
  size_t x_size = lean_sarray_size(x)
  size_t y_size = lean_sarray_size(y)
  if (x_size != 64 || y_size != 64) {
    lean_object* error_msg = lean_mk_string("Both buffers must be exactly 64 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }
  
  int result = crypto_verify_64(lean_sarray_cptr(x), lean_sarray_cptr(y))
  uint8_t is_equal = (result == 0)
  return lean_io_result_mk_ok(lean_box(is_equal))

end Sodium.FFI
