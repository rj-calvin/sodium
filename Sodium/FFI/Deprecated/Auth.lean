import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI

-- Default HMAC constants (HMAC-SHA512-256)
def AUTH_BYTES : UInt32 := 32
def AUTH_KEYBYTES : UInt32 := 32

-- HMAC-SHA256 constants
def HMAC_SHA256_BYTES : UInt32 := 32
def HMAC_SHA256_KEYBYTES : UInt32 := 32

-- HMAC-SHA512 constants
def HMAC_SHA512_BYTES : UInt32 := 64
def HMAC_SHA512_KEYBYTES : UInt32 := 32

-- HMAC-SHA512-256 constants
def HMAC_SHA512256_BYTES : UInt32 := 32
def HMAC_SHA512256_KEYBYTES : UInt32 := 32

/- Default Authentication Functions (HMAC-SHA512-256) -/

alloy c extern "lean_crypto_auth_keygen"
def authKeygen : BaseIO ByteArray :=
  lean_object* key = lean_alloc_sarray(sizeof(unsigned char), crypto_auth_KEYBYTES, crypto_auth_KEYBYTES)
  crypto_auth_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c extern "lean_crypto_auth"
def auth (message : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_auth_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* mac = lean_alloc_sarray(sizeof(unsigned char), crypto_auth_BYTES, crypto_auth_BYTES)

  int result = crypto_auth(
    lean_sarray_cptr(mac),
    lean_sarray_cptr(message), lean_sarray_size(message),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(mac)
    lean_object* error_msg = lean_mk_string("Authentication computation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(mac)

alloy c extern "lean_crypto_auth_verify"
def authVerify (mac : ByteArray) (message : ByteArray) (key : ByteArray) : IO Bool :=
  if (lean_sarray_size(key) != crypto_auth_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(mac) != crypto_auth_BYTES) {
    lean_object* error_msg = lean_mk_string("MAC must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  int result = crypto_auth_verify(
    lean_sarray_cptr(mac),
    lean_sarray_cptr(message), lean_sarray_size(message),
    lean_sarray_cptr(key)
  )

  // crypto_auth_verify returns 0 on success, -1 on failure
  return lean_io_result_mk_ok(lean_box(result == 0 ? 1 : 0))

/- HMAC-SHA256 Functions -/

alloy c extern "lean_crypto_auth_hmacsha256_keygen"
def hmacSha256Keygen : BaseIO ByteArray :=
  lean_object* key = lean_alloc_sarray(sizeof(unsigned char), crypto_auth_hmacsha256_KEYBYTES, crypto_auth_hmacsha256_KEYBYTES)
  crypto_auth_hmacsha256_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c extern "lean_crypto_auth_hmacsha256"
def hmacSha256 (message : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_auth_hmacsha256_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* mac = lean_alloc_sarray(sizeof(unsigned char), crypto_auth_hmacsha256_BYTES, crypto_auth_hmacsha256_BYTES)

  int result = crypto_auth_hmacsha256(
    lean_sarray_cptr(mac),
    lean_sarray_cptr(message), lean_sarray_size(message),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(mac)
    lean_object* error_msg = lean_mk_string("HMAC-SHA256 computation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(mac)

alloy c extern "lean_crypto_auth_hmacsha256_verify"
def hmacSha256Verify (mac : ByteArray) (message : ByteArray) (key : ByteArray) : IO Bool :=
  if (lean_sarray_size(key) != crypto_auth_hmacsha256_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(mac) != crypto_auth_hmacsha256_BYTES) {
    lean_object* error_msg = lean_mk_string("MAC must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  int result = crypto_auth_hmacsha256_verify(
    lean_sarray_cptr(mac),
    lean_sarray_cptr(message), lean_sarray_size(message),
    lean_sarray_cptr(key)
  )

  return lean_io_result_mk_ok(lean_box(result == 0 ? 1 : 0))

/- HMAC-SHA512 Functions -/

alloy c extern "lean_crypto_auth_hmacsha512_keygen"
def hmacSha512Keygen : BaseIO ByteArray :=
  lean_object* key = lean_alloc_sarray(sizeof(unsigned char), crypto_auth_hmacsha512_KEYBYTES, crypto_auth_hmacsha512_KEYBYTES)
  crypto_auth_hmacsha512_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c extern "lean_crypto_auth_hmacsha512"
def hmacSha512 (message : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_auth_hmacsha512_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* mac = lean_alloc_sarray(sizeof(unsigned char), crypto_auth_hmacsha512_BYTES, crypto_auth_hmacsha512_BYTES)

  int result = crypto_auth_hmacsha512(
    lean_sarray_cptr(mac),
    lean_sarray_cptr(message), lean_sarray_size(message),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(mac)
    lean_object* error_msg = lean_mk_string("HMAC-SHA512 computation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(mac)

alloy c extern "lean_crypto_auth_hmacsha512_verify"
def hmacSha512Verify (mac : ByteArray) (message : ByteArray) (key : ByteArray) : IO Bool :=
  if (lean_sarray_size(key) != crypto_auth_hmacsha512_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(mac) != crypto_auth_hmacsha512_BYTES) {
    lean_object* error_msg = lean_mk_string("MAC must be 64 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  int result = crypto_auth_hmacsha512_verify(
    lean_sarray_cptr(mac),
    lean_sarray_cptr(message), lean_sarray_size(message),
    lean_sarray_cptr(key)
  )

  return lean_io_result_mk_ok(lean_box(result == 0 ? 1 : 0))

end Sodium.FFI
