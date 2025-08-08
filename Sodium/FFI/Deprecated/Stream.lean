import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI

/- Default Stream (XSalsa20) Constants -/
def STREAM_KEYBYTES : UInt32 := 32
def STREAM_NONCEBYTES : UInt32 := 24

/- ChaCha20 Constants -/
def CHACHA20_KEYBYTES : UInt32 := 32
def CHACHA20_NONCEBYTES : UInt32 := 8

/- ChaCha20-IETF Constants -/
def CHACHA20_IETF_KEYBYTES : UInt32 := 32
def CHACHA20_IETF_NONCEBYTES : UInt32 := 12

/- Salsa20 Constants -/
def SALSA20_KEYBYTES : UInt32 := 32
def SALSA20_NONCEBYTES : UInt32 := 8

/- XChaCha20 Constants -/
def XCHACHA20_KEYBYTES : UInt32 := 32
def XCHACHA20_NONCEBYTES : UInt32 := 24

/- XSalsa20 Constants -/
def XSALSA20_KEYBYTES : UInt32 := 32
def XSALSA20_NONCEBYTES : UInt32 := 24

/- Default Stream Functions (XSalsa20) -/

alloy c extern "lean_crypto_stream_keygen"
def streamKeygen : BaseIO ByteArray :=
  lean_object* key = lean_alloc_sarray(sizeof(unsigned char), crypto_stream_KEYBYTES, crypto_stream_KEYBYTES)
  crypto_stream_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c extern "lean_crypto_stream"
def stream (length : UInt64) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 24 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), length, length)

  int result = crypto_stream(
    lean_sarray_cptr(output), length,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("Stream generation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

alloy c extern "lean_crypto_stream_xor"
def streamXor (message : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 24 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)

  int result = crypto_stream_xor(
    lean_sarray_cptr(output),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("Stream XOR failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

/- ChaCha20 Functions -/

alloy c extern "lean_crypto_stream_chacha20_keygen"
def chacha20Keygen : BaseIO ByteArray :=
  lean_object* key = lean_alloc_sarray(sizeof(unsigned char), crypto_stream_chacha20_KEYBYTES, crypto_stream_chacha20_KEYBYTES)
  crypto_stream_chacha20_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c extern "lean_crypto_stream_chacha20"
def chacha20 (length : UInt64) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_chacha20_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_chacha20_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 8 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), length, length)

  int result = crypto_stream_chacha20(
    lean_sarray_cptr(output), length,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("ChaCha20 stream generation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

alloy c extern "lean_crypto_stream_chacha20_xor"
def chacha20Xor (message : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_chacha20_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_chacha20_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 8 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)

  int result = crypto_stream_chacha20_xor(
    lean_sarray_cptr(output),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("ChaCha20 XOR failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

alloy c extern "lean_crypto_stream_chacha20_xor_ic"
def chacha20XorIc (message : ByteArray) (nonce : ByteArray) (initialCounter : UInt64) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_chacha20_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_chacha20_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 8 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)

  int result = crypto_stream_chacha20_xor_ic(
    lean_sarray_cptr(output),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce), initialCounter,
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("ChaCha20 XOR with counter failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

/- ChaCha20-IETF Functions -/

alloy c extern "lean_crypto_stream_chacha20_ietf_keygen"
def chacha20IetfKeygen : BaseIO ByteArray :=
  lean_object* key = lean_alloc_sarray(sizeof(unsigned char), crypto_stream_chacha20_ietf_KEYBYTES, crypto_stream_chacha20_ietf_KEYBYTES)
  crypto_stream_chacha20_ietf_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c extern "lean_crypto_stream_chacha20_ietf"
def chacha20Ietf (length : UInt64) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_chacha20_ietf_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_chacha20_ietf_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 12 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), length, length)

  int result = crypto_stream_chacha20_ietf(
    lean_sarray_cptr(output), length,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("ChaCha20-IETF stream generation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

alloy c extern "lean_crypto_stream_chacha20_ietf_xor"
def chacha20IetfXor (message : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_chacha20_ietf_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_chacha20_ietf_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 12 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)

  int result = crypto_stream_chacha20_ietf_xor(
    lean_sarray_cptr(output),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("ChaCha20-IETF XOR failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

alloy c extern "lean_crypto_stream_chacha20_ietf_xor_ic"
def chacha20IetfXorIc (message : ByteArray) (nonce : ByteArray) (initialCounter : UInt32) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_chacha20_ietf_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_chacha20_ietf_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 12 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)

  int result = crypto_stream_chacha20_ietf_xor_ic(
    lean_sarray_cptr(output),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce), initialCounter,
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("ChaCha20-IETF XOR with counter failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

/- Salsa20 Functions -/

alloy c extern "lean_crypto_stream_salsa20_keygen"
def salsa20Keygen : BaseIO ByteArray :=
  lean_object* key = lean_alloc_sarray(sizeof(unsigned char), crypto_stream_salsa20_KEYBYTES, crypto_stream_salsa20_KEYBYTES)
  crypto_stream_salsa20_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c extern "lean_crypto_stream_salsa20"
def salsa20 (length : UInt64) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_salsa20_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_salsa20_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 8 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), length, length)

  int result = crypto_stream_salsa20(
    lean_sarray_cptr(output), length,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("Salsa20 stream generation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

alloy c extern "lean_crypto_stream_salsa20_xor"
def salsa20Xor (message : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_salsa20_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_salsa20_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 8 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)

  int result = crypto_stream_salsa20_xor(
    lean_sarray_cptr(output),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("Salsa20 XOR failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

alloy c extern "lean_crypto_stream_salsa20_xor_ic"
def salsa20XorIc (message : ByteArray) (nonce : ByteArray) (initialCounter : UInt64) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_salsa20_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_salsa20_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 8 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)

  int result = crypto_stream_salsa20_xor_ic(
    lean_sarray_cptr(output),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce), initialCounter,
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("Salsa20 XOR with counter failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

/- XChaCha20 Functions -/

alloy c extern "lean_crypto_stream_xchacha20_keygen"
def xchacha20Keygen : BaseIO ByteArray :=
  lean_object* key = lean_alloc_sarray(sizeof(unsigned char), crypto_stream_xchacha20_KEYBYTES, crypto_stream_xchacha20_KEYBYTES)
  crypto_stream_xchacha20_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c extern "lean_crypto_stream_xchacha20"
def xchacha20 (length : UInt64) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_xchacha20_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_xchacha20_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 24 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), length, length)

  int result = crypto_stream_xchacha20(
    lean_sarray_cptr(output), length,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("XChaCha20 stream generation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

alloy c extern "lean_crypto_stream_xchacha20_xor"
def xchacha20Xor (message : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_xchacha20_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_xchacha20_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 24 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)

  int result = crypto_stream_xchacha20_xor(
    lean_sarray_cptr(output),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("XChaCha20 XOR failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

alloy c extern "lean_crypto_stream_xchacha20_xor_ic"
def xchacha20XorIc (message : ByteArray) (nonce : ByteArray) (initialCounter : UInt64) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_xchacha20_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_xchacha20_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 24 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)

  int result = crypto_stream_xchacha20_xor_ic(
    lean_sarray_cptr(output),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce), initialCounter,
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("XChaCha20 XOR with counter failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

/- XSalsa20 Functions -/

alloy c extern "lean_crypto_stream_xsalsa20_keygen"
def xsalsa20Keygen : BaseIO ByteArray :=
  lean_object* key = lean_alloc_sarray(sizeof(unsigned char), crypto_stream_xsalsa20_KEYBYTES, crypto_stream_xsalsa20_KEYBYTES)
  crypto_stream_xsalsa20_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c extern "lean_crypto_stream_xsalsa20"
def xsalsa20 (length : UInt64) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_xsalsa20_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_xsalsa20_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 24 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), length, length)

  int result = crypto_stream_xsalsa20(
    lean_sarray_cptr(output), length,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("XSalsa20 stream generation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

alloy c extern "lean_crypto_stream_xsalsa20_xor"
def xsalsa20Xor (message : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_xsalsa20_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_xsalsa20_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 24 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)

  int result = crypto_stream_xsalsa20_xor(
    lean_sarray_cptr(output),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("XSalsa20 XOR failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

alloy c extern "lean_crypto_stream_xsalsa20_xor_ic"
def xsalsa20XorIc (message : ByteArray) (nonce : ByteArray) (initialCounter : UInt64) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_stream_xsalsa20_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_stream_xsalsa20_NONCEBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 24 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  lean_object* output = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)

  int result = crypto_stream_xsalsa20_xor_ic(
    lean_sarray_cptr(output),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce), initialCounter,
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(output)
    lean_object* error_msg = lean_mk_string("XSalsa20 XOR with counter failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(output)

end Sodium.FFI
