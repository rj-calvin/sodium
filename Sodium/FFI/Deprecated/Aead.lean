import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI

-- ChaCha20-Poly1305 IETF (96-bit nonce) AEAD constants
def CHACHA20POLY1305_IETF_KEYBYTES : UInt32 := 32
def CHACHA20POLY1305_IETF_NONCEBYTES : UInt32 := 12
def CHACHA20POLY1305_IETF_TAGBYTES : UInt32 := 16

-- ChaCha20-Poly1305 Original (64-bit nonce) AEAD constants
def CHACHA20POLY1305_KEYBYTES : UInt32 := 32
def CHACHA20POLY1305_NONCEBYTES : UInt32 := 8
def CHACHA20POLY1305_TAGBYTES : UInt32 := 16

-- XChaCha20-Poly1305 IETF AEAD constants
def XCHACHA20POLY1305_IETF_KEYBYTES : UInt32 := 32
def XCHACHA20POLY1305_IETF_NONCEBYTES : UInt32 := 24
def XCHACHA20POLY1305_IETF_TAGBYTES : UInt32 := 16

-- AES256-GCM AEAD constants
def AES256GCM_KEYBYTES : UInt32 := 32
def AES256GCM_NONCEBYTES : UInt32 := 12
def AES256GCM_TAGBYTES : UInt32 := 16

-- AEGIS-128L AEAD constants
def AEGIS128L_KEYBYTES : UInt32 := 16
def AEGIS128L_NONCEBYTES : UInt32 := 16
def AEGIS128L_TAGBYTES : UInt32 := 32

-- AEGIS-256 AEAD constants
def AEGIS256_KEYBYTES : UInt32 := 32
def AEGIS256_NONCEBYTES : UInt32 := 32
def AEGIS256_TAGBYTES : UInt32 := 32

/- ChaCha20-Poly1305 IETF AEAD Functions -/

alloy c extern "lean_crypto_aead_chacha20poly1305_ietf_keygen"
def chacha20poly1305IetfKeygen : BaseIO ByteArray :=
  lean_object* key = lean_alloc_sarray(sizeof(unsigned char), 32, 32)
  crypto_aead_chacha20poly1305_ietf_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c extern "lean_crypto_aead_chacha20poly1305_ietf_encrypt"
def chacha20poly1305IetfEncrypt (message : ByteArray) (ad : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != 32) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != 12) {
    lean_object* error_msg = lean_mk_string("Nonce must be 12 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t mlen = lean_sarray_size(message)
  size_t ciphertext_len = mlen + crypto_aead_chacha20poly1305_ietf_ABYTES
  lean_object* ciphertext = lean_alloc_sarray(sizeof(unsigned char), ciphertext_len, ciphertext_len)
  unsigned long long clen;

  int result = crypto_aead_chacha20poly1305_ietf_encrypt(
    lean_sarray_cptr(ciphertext), &clen,
    lean_sarray_cptr(message), mlen,
    lean_sarray_cptr(ad), lean_sarray_size(ad),
    NULL,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(ciphertext)
    lean_object* error_msg = lean_mk_string("ChaCha20-Poly1305 IETF encryption failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_sarray_set_size(ciphertext, clen)
  return lean_io_result_mk_ok(ciphertext)

alloy c extern "lean_crypto_aead_chacha20poly1305_ietf_decrypt"
def chacha20poly1305IetfDecrypt (ciphertext : ByteArray) (ad : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != 32) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != 12) {
    lean_object* error_msg = lean_mk_string("Nonce must be 12 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t clen = lean_sarray_size(ciphertext)
  if (clen < crypto_aead_chacha20poly1305_ietf_ABYTES) {
    lean_object* error_msg = lean_mk_string("Ciphertext too short")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = clen - 16
  lean_object* message = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)
  unsigned long long mlen;

  int result = crypto_aead_chacha20poly1305_ietf_decrypt(
    lean_sarray_cptr(message), &mlen,
    NULL,
    lean_sarray_cptr(ciphertext), clen,
    lean_sarray_cptr(ad), lean_sarray_size(ad),
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(message)
    lean_object* error_msg = lean_mk_string("ChaCha20-Poly1305 IETF decryption failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_sarray_set_size(message, mlen)
  return lean_io_result_mk_ok(message)

/- ChaCha20-Poly1305 Original AEAD Functions -/

alloy c extern "lean_crypto_aead_chacha20poly1305_keygen"
def chacha20poly1305Keygen : BaseIO ByteArray :=
  lean_object* key = lean_alloc_sarray(sizeof(unsigned char), 32, 32)
  crypto_aead_chacha20poly1305_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c extern "lean_crypto_aead_chacha20poly1305_encrypt"
def chacha20poly1305Encrypt (message : ByteArray) (ad : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != 32) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != 8) {
    lean_object* error_msg = lean_mk_string("Nonce must be 8 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t mlen = lean_sarray_size(message)
  size_t ciphertext_len = mlen + crypto_aead_chacha20poly1305_ABYTES
  lean_object* ciphertext = lean_alloc_sarray(sizeof(unsigned char), ciphertext_len, ciphertext_len)
  unsigned long long clen;

  int result = crypto_aead_chacha20poly1305_encrypt(
    lean_sarray_cptr(ciphertext), &clen,
    lean_sarray_cptr(message), mlen,
    lean_sarray_cptr(ad), lean_sarray_size(ad),
    NULL,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(ciphertext)
    lean_object* error_msg = lean_mk_string("ChaCha20-Poly1305 encryption failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_sarray_set_size(ciphertext, clen)
  return lean_io_result_mk_ok(ciphertext)

alloy c extern "lean_crypto_aead_chacha20poly1305_decrypt"
def chacha20poly1305Decrypt (ciphertext : ByteArray) (ad : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != 32) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != 8) {
    lean_object* error_msg = lean_mk_string("Nonce must be 8 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t clen = lean_sarray_size(ciphertext)
  if (clen < crypto_aead_chacha20poly1305_ABYTES) {
    lean_object* error_msg = lean_mk_string("Ciphertext too short")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = clen - crypto_aead_chacha20poly1305_ABYTES
  lean_object* message = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)
  unsigned long long mlen;

  int result = crypto_aead_chacha20poly1305_decrypt(
    lean_sarray_cptr(message), &mlen,
    NULL,
    lean_sarray_cptr(ciphertext), clen,
    lean_sarray_cptr(ad), lean_sarray_size(ad),
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(message)
    lean_object* error_msg = lean_mk_string("ChaCha20-Poly1305 decryption failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_sarray_set_size(message, mlen)
  return lean_io_result_mk_ok(message)

/- XChaCha20-Poly1305 IETF AEAD Functions -/

alloy c extern "lean_crypto_aead_xchacha20poly1305_ietf_keygen"
def xchacha20poly1305IetfKeygen : BaseIO ByteArray :=
  lean_object* key = lean_alloc_sarray(sizeof(unsigned char), crypto_aead_xchacha20poly1305_ietf_KEYBYTES, crypto_aead_xchacha20poly1305_ietf_KEYBYTES)
  crypto_aead_xchacha20poly1305_ietf_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c extern "lean_crypto_aead_xchacha20poly1305_ietf_encrypt"
def xchacha20poly1305IetfEncrypt (message : ByteArray) (ad : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_aead_xchacha20poly1305_ietf_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_aead_xchacha20poly1305_ietf_NPUBBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 24 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t mlen = lean_sarray_size(message)
  size_t ciphertext_len = mlen + crypto_aead_xchacha20poly1305_ietf_ABYTES
  lean_object* ciphertext = lean_alloc_sarray(sizeof(unsigned char), ciphertext_len, ciphertext_len)
  unsigned long long clen;

  int result = crypto_aead_xchacha20poly1305_ietf_encrypt(
    lean_sarray_cptr(ciphertext), &clen,
    lean_sarray_cptr(message), mlen,
    lean_sarray_cptr(ad), lean_sarray_size(ad),
    NULL,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(ciphertext)
    lean_object* error_msg = lean_mk_string("XChaCha20-Poly1305 IETF encryption failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_sarray_set_size(ciphertext, clen)
  return lean_io_result_mk_ok(ciphertext)

alloy c extern "lean_crypto_aead_xchacha20poly1305_ietf_decrypt"
def xchacha20poly1305IetfDecrypt (ciphertext : ByteArray) (ad : ByteArray) (nonce : ByteArray) (key : ByteArray) : IO ByteArray :=
  if (lean_sarray_size(key) != crypto_aead_xchacha20poly1305_ietf_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("Key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(nonce) != crypto_aead_xchacha20poly1305_ietf_NPUBBYTES) {
    lean_object* error_msg = lean_mk_string("Nonce must be 24 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t clen = lean_sarray_size(ciphertext)
  if (clen < crypto_aead_xchacha20poly1305_ietf_ABYTES) {
    lean_object* error_msg = lean_mk_string("Ciphertext too short")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = clen - crypto_aead_xchacha20poly1305_ietf_ABYTES
  lean_object* message = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)
  unsigned long long mlen;

  int result = crypto_aead_xchacha20poly1305_ietf_decrypt(
    lean_sarray_cptr(message), &mlen,
    NULL,
    lean_sarray_cptr(ciphertext), clen,
    lean_sarray_cptr(ad), lean_sarray_size(ad),
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    lean_dec_ref(message)
    lean_object* error_msg = lean_mk_string("XChaCha20-Poly1305 IETF decryption failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_sarray_set_size(message, mlen)
  return lean_io_result_mk_ok(message)

end Sodium.FFI
