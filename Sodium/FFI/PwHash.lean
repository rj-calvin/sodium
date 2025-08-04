import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI

-- Constants for crypto_pwhash (Argon2id)
def PWHASH_SALTBYTES : USize := 16
def PWHASH_STRBYTES : USize := 128
def PWHASH_OPSLIMIT_INTERACTIVE : USize := 2
def PWHASH_OPSLIMIT_SENSITIVE : USize := 4
def PWHASH_MEMLIMIT_INTERACTIVE : USize := 67108864     -- 64 MB
def PWHASH_MEMLIMIT_SENSITIVE : USize := 1073741824    -- 1024 MB
def PWHASH_ALG_DEFAULT : UInt32 := 2                   -- Argon2id

alloy c extern "lean_crypto_pwhash"
def pwhash (outlen : USize) (passwd : String) (salt : ByteArray) (opslimit : USize) (memlimit : USize) (alg : UInt32) : IO ByteArray :=
  size_t salt_size = lean_sarray_size(salt)
  size_t expected_salt_size = crypto_pwhash_SALTBYTES
  if (salt_size != expected_salt_size) {
    lean_object* error_msg = lean_mk_string("Invalid salt size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (outlen == 0) {
    lean_object* error_msg = lean_mk_string("Output length must be greater than 0")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* out = lean_alloc_sarray(sizeof(unsigned char), outlen, outlen)
  const char* passwd_cstr = lean_string_cstr(passwd)
  size_t passwd_len = lean_string_len(passwd)

  int result = crypto_pwhash(
    lean_sarray_cptr(out), outlen,
    passwd_cstr, passwd_len,
    lean_sarray_cptr(salt),
    opslimit, memlimit, alg
  )

  if (result != 0) {
    lean_dec(out)
    lean_object* error_msg = lean_mk_string("crypto_pwhash failed (possibly out of memory)")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(out)

alloy c extern "lean_crypto_pwhash_str"
def pwhashStr (passwd : String) (opslimit : USize) (memlimit : USize) : IO String :=
  const char* passwd_cstr = lean_string_cstr(passwd)
  size_t passwd_len = lean_string_len(passwd)

  char* out = (char*)malloc(crypto_pwhash_STRBYTES)
  if (out == NULL) {
    lean_object* error_msg = lean_mk_string("Failed to allocate memory for password hash")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  int result = crypto_pwhash_str(
    out,
    passwd_cstr, passwd_len,
    opslimit, memlimit
  )

  if (result != 0) {
    free(out)
    lean_object* error_msg = lean_mk_string("crypto_pwhash_str failed (possibly out of memory)")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* hash_string = lean_mk_string(out)
  free(out)
  return lean_io_result_mk_ok(hash_string)

alloy c extern "lean_crypto_pwhash_str_verify"
def pwhashStrVerify (str : String) (passwd : String) : IO Bool :=
  const char* str_cstr = lean_string_cstr(str)
  const char* passwd_cstr = lean_string_cstr(passwd)
  size_t passwd_len = lean_string_len(passwd)

  int result = crypto_pwhash_str_verify(
    str_cstr,
    passwd_cstr, passwd_len
  )

  uint8_t verification_success = (result == 0)
  return lean_io_result_mk_ok(lean_box(verification_success))

end Sodium.FFI
