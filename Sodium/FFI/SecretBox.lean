import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI

-- Constants for crypto_secretbox
def SECRETBOX_KEYBYTES : USize := 32
def SECRETBOX_NONCEBYTES : USize := 24
def SECRETBOX_MACBYTES : USize := 16

alloy c extern "lean_crypto_secretbox_keygen"
def secretBoxKeygen : IO ByteArray :=
  lean_object* key = lean_alloc_sarray(
    sizeof(unsigned char),
    crypto_secretbox_KEYBYTES,
    crypto_secretbox_KEYBYTES)
  crypto_secretbox_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c extern "lean_crypto_secretbox_easy"
def secretBoxEasy (message : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  size_t key_size = lean_sarray_size(key)
  size_t expected_key_size = crypto_secretbox_KEYBYTES
  if (key_size != expected_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t nonce_size = lean_sarray_size(nonce)
  size_t expected_nonce_size = crypto_secretbox_NONCEBYTES
  if (nonce_size != expected_nonce_size) {
    lean_object* error_msg = lean_mk_string("Invalid nonce size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  size_t ciphertext_len = message_len + crypto_secretbox_MACBYTES

  lean_object* ciphertext = lean_alloc_sarray(sizeof(unsigned char), ciphertext_len, ciphertext_len)

  int result = crypto_secretbox_easy(
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec(ciphertext)
    lean_object* error_msg = lean_mk_string("crypto_secretbox_easy failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(ciphertext)

alloy c extern "lean_crypto_secretbox_open_easy"
def secretBoxOpenEasy (ciphertext : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  size_t key_size = lean_sarray_size(key)
  size_t expected_key_size = crypto_secretbox_KEYBYTES
  if (key_size != expected_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t nonce_size = lean_sarray_size(nonce)
  size_t expected_nonce_size = crypto_secretbox_NONCEBYTES
  if (nonce_size != expected_nonce_size) {
    lean_object* error_msg = lean_mk_string("Invalid nonce size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t ciphertext_len = lean_sarray_size(ciphertext)
  if (ciphertext_len < crypto_secretbox_MACBYTES) {
    lean_object* error_msg = lean_mk_string("Ciphertext too short")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = ciphertext_len - crypto_secretbox_MACBYTES
  lean_object* message = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)

  int result = crypto_secretbox_open_easy(
    lean_sarray_cptr(message),
    lean_sarray_cptr(ciphertext), ciphertext_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec(message)
    lean_object* error_msg = lean_mk_string("crypto_secretbox_open_easy failed (authentication failed)")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(message)

alloy c extern "lean_crypto_secretbox_detached"
def secretBoxDetached (message : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO (ByteArray × ByteArray) :=
  size_t key_size = lean_sarray_size(key)
  size_t expected_key_size = crypto_secretbox_KEYBYTES
  if (key_size != expected_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t nonce_size = lean_sarray_size(nonce)
  size_t expected_nonce_size = crypto_secretbox_NONCEBYTES
  if (nonce_size != expected_nonce_size) {
    lean_object* error_msg = lean_mk_string("Invalid nonce size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  lean_object* ciphertext = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)
  lean_object* mac = lean_alloc_sarray(sizeof(unsigned char), crypto_secretbox_MACBYTES, crypto_secretbox_MACBYTES)

  int result = crypto_secretbox_detached(
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(mac),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec(ciphertext)
    lean_dec(mac)
    lean_object* error_msg = lean_mk_string("crypto_secretbox_detached failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(pair, 0, ciphertext)
  lean_ctor_set(pair, 1, mac)

  return lean_io_result_mk_ok(pair)

alloy c extern "lean_crypto_secretbox_open_detached"
def secretBoxOpenDetached (ciphertext : ByteArray) (mac : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  size_t key_size = lean_sarray_size(key)
  size_t expected_key_size = crypto_secretbox_KEYBYTES
  if (key_size != expected_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t nonce_size = lean_sarray_size(nonce)
  size_t expected_nonce_size = crypto_secretbox_NONCEBYTES
  if (nonce_size != expected_nonce_size) {
    lean_object* error_msg = lean_mk_string("Invalid nonce size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t mac_size = lean_sarray_size(mac)
  size_t expected_mac_size = crypto_secretbox_MACBYTES
  if (mac_size != expected_mac_size) {
    lean_object* error_msg = lean_mk_string("Invalid MAC size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t ciphertext_len = lean_sarray_size(ciphertext)
  lean_object* message = lean_alloc_sarray(sizeof(unsigned char), ciphertext_len, ciphertext_len)

  int result = crypto_secretbox_open_detached(
    lean_sarray_cptr(message),
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(mac),
    ciphertext_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec(message)
    lean_object* error_msg = lean_mk_string("crypto_secretbox_open_detached failed (authentication failed)")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(message)

alloy c extern "lean_crypto_secretbox_messagebytes_max"
def secretBoxMessageBytesMax : BaseIO USize :=
  size_t max_bytes = crypto_secretbox_messagebytes_max()
  return lean_io_result_mk_ok(lean_box_usize(max_bytes))

end Sodium.FFI
