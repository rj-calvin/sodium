import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI

-- BLAKE2b-based KDF constants
def KDF_KEYBYTES : UInt32 := 32
def KDF_CONTEXTBYTES : UInt32 := 8
def KDF_BYTES_MIN : UInt32 := 16
def KDF_BYTES_MAX : UInt32 := 64

-- HKDF-SHA256 constants
def HKDF_SHA256_KEYBYTES : UInt32 := 32
def HKDF_SHA256_BYTES_MIN : UInt32 := 0
def HKDF_SHA256_BYTES_MAX : UInt32 := 8160

-- HKDF-SHA512 constants
def HKDF_SHA512_KEYBYTES : UInt32 := 64
def HKDF_SHA512_BYTES_MIN : UInt32 := 0
def HKDF_SHA512_BYTES_MAX : UInt32 := 16320

/- BLAKE2b-based Key Derivation Functions -/

alloy c extern "lean_crypto_kdf_keygen"
def kdfKeygen : BaseIO ByteArray :=
  lean_object* key = lean_alloc_sarray(sizeof(unsigned char), crypto_kdf_KEYBYTES, crypto_kdf_KEYBYTES)
  crypto_kdf_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c extern "lean_crypto_kdf_derive_from_key"
def kdfDeriveFromKey (subkeyLen : UInt32) (subkeyId : UInt64) (context : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_kdf_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(context) != crypto_kdf_CONTEXTBYTES) {
    lean_object* error_msg = lean_mk_string("Context must be 8 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (subkeyLen < crypto_kdf_BYTES_MIN || subkeyLen > crypto_kdf_BYTES_MAX) {
    lean_object* error_msg = lean_mk_string("Subkey length must be between 16 and 64 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* subkey = lean_alloc_sarray(sizeof(unsigned char), subkeyLen, subkeyLen)

  int result = crypto_kdf_derive_from_key(
    lean_sarray_cptr(subkey), subkeyLen,
    subkeyId,
    lean_sarray_cptr(context),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(subkey)
    lean_object* error_msg = lean_mk_string("Key derivation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(subkey)

/- HKDF-SHA256 Key Derivation Functions -/

alloy c extern "lean_crypto_kdf_hkdf_sha256_keygen"
def hkdfSha256Keygen : BaseIO ByteArray :=
  lean_object* prk = lean_alloc_sarray(sizeof(unsigned char), crypto_kdf_hkdf_sha256_KEYBYTES, crypto_kdf_hkdf_sha256_KEYBYTES)
  crypto_kdf_hkdf_sha256_keygen(lean_sarray_cptr(prk))
  return lean_io_result_mk_ok(prk)

alloy c extern "lean_crypto_kdf_hkdf_sha256_extract"
def hkdfSha256Extract (salt : ByteArray) (ikm : ByteArray) : IO ByteArray :=
  lean_object* prk = lean_alloc_sarray(sizeof(unsigned char), crypto_kdf_hkdf_sha256_KEYBYTES, crypto_kdf_hkdf_sha256_KEYBYTES)

  int result = crypto_kdf_hkdf_sha256_extract(
    lean_sarray_cptr(prk),
    lean_sarray_cptr(salt), lean_sarray_size(salt),
    lean_sarray_cptr(ikm), lean_sarray_size(ikm)
  )

  if (result != 0) {
    lean_dec_ref(prk)
    lean_object* error_msg = lean_mk_string("HKDF-SHA256 extract failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(prk)

alloy c extern "lean_crypto_kdf_hkdf_sha256_expand"
def hkdfSha256Expand (outLen : UInt32) (context : ByteArray) (prk : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(prk) != crypto_kdf_hkdf_sha256_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("PRK must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (outLen > crypto_kdf_hkdf_sha256_BYTES_MAX) {
    lean_object* error_msg = lean_mk_string("Output length exceeds maximum")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* out = lean_alloc_sarray(sizeof(unsigned char), outLen, outLen)

  int result = crypto_kdf_hkdf_sha256_expand(
    lean_sarray_cptr(out), outLen,
    lean_sarray_cptr(context), lean_sarray_size(context),
    lean_sarray_cptr(prk)
  )

  if (result != 0) {
    lean_dec_ref(out)
    lean_object* error_msg = lean_mk_string("HKDF-SHA256 expand failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(out)

/- HKDF-SHA512 Key Derivation Functions -/

alloy c extern "lean_crypto_kdf_hkdf_sha512_keygen"
def hkdfSha512Keygen : BaseIO ByteArray :=
  lean_object* prk = lean_alloc_sarray(sizeof(unsigned char), crypto_kdf_hkdf_sha512_KEYBYTES, crypto_kdf_hkdf_sha512_KEYBYTES)
  crypto_kdf_hkdf_sha512_keygen(lean_sarray_cptr(prk))
  return lean_io_result_mk_ok(prk)

alloy c extern "lean_crypto_kdf_hkdf_sha512_extract"
def hkdfSha512Extract (salt : ByteArray) (ikm : ByteArray) : IO ByteArray :=
  lean_object* prk = lean_alloc_sarray(sizeof(unsigned char), crypto_kdf_hkdf_sha512_KEYBYTES, crypto_kdf_hkdf_sha512_KEYBYTES)

  int result = crypto_kdf_hkdf_sha512_extract(
    lean_sarray_cptr(prk),
    lean_sarray_cptr(salt), lean_sarray_size(salt),
    lean_sarray_cptr(ikm), lean_sarray_size(ikm)
  )

  if (result != 0) {
    lean_dec_ref(prk)
    lean_object* error_msg = lean_mk_string("HKDF-SHA512 extract failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(prk)

alloy c extern "lean_crypto_kdf_hkdf_sha512_expand"
def hkdfSha512Expand (outLen : UInt32) (context : ByteArray) (prk : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(prk) != crypto_kdf_hkdf_sha512_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("PRK must be 64 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (outLen > crypto_kdf_hkdf_sha512_BYTES_MAX) {
    lean_object* error_msg = lean_mk_string("Output length exceeds maximum")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* out = lean_alloc_sarray(sizeof(unsigned char), outLen, outLen)

  int result = crypto_kdf_hkdf_sha512_expand(
    lean_sarray_cptr(out), outLen,
    lean_sarray_cptr(context), lean_sarray_size(context),
    lean_sarray_cptr(prk)
  )

  if (result != 0) {
    lean_dec_ref(out)
    lean_object* error_msg = lean_mk_string("HKDF-SHA512 expand failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(out)

end Sodium.FFI
