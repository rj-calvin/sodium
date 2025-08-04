import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI

-- Constants for crypto_sign (Ed25519)
def SIGN_PUBLICKEYBYTES : USize := 32
def SIGN_SECRETKEYBYTES : USize := 64
def SIGN_BYTES : USize := 64
def SIGN_SEEDBYTES : USize := 32

alloy c extern "lean_crypto_sign_keypair"
def signKeypair : IO (ByteArray × ByteArray) :=
  lean_object* public_key = lean_alloc_sarray(
    sizeof(unsigned char),
    crypto_sign_PUBLICKEYBYTES,
    crypto_sign_PUBLICKEYBYTES)
  lean_object* secret_key = lean_alloc_sarray(
    sizeof(unsigned char),
    crypto_sign_SECRETKEYBYTES,
    crypto_sign_SECRETKEYBYTES)

  int result = crypto_sign_keypair(
    lean_sarray_cptr(public_key),
    lean_sarray_cptr(secret_key)
  )

  if (result != 0) {
    lean_dec(public_key)
    lean_dec(secret_key)
    lean_object* error_msg = lean_mk_string("crypto_sign_keypair failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(pair, 0, public_key)
  lean_ctor_set(pair, 1, secret_key)

  return lean_io_result_mk_ok(pair)

alloy c extern "lean_crypto_sign_seed_keypair"
def signSeedKeypair (seed : ByteArray) : IO (ByteArray × ByteArray) :=
  size_t seed_size = lean_sarray_size(seed)
  size_t expected_seed_size = crypto_sign_SEEDBYTES
  if (seed_size != expected_seed_size) {
    lean_object* error_msg = lean_mk_string("Invalid seed size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* public_key = lean_alloc_sarray(
    sizeof(unsigned char),
    crypto_sign_PUBLICKEYBYTES,
    crypto_sign_PUBLICKEYBYTES)
  lean_object* secret_key = lean_alloc_sarray(
    sizeof(unsigned char),
    crypto_sign_SECRETKEYBYTES,
    crypto_sign_SECRETKEYBYTES)

  int result = crypto_sign_seed_keypair(
    lean_sarray_cptr(public_key),
    lean_sarray_cptr(secret_key),
    lean_sarray_cptr(seed)
  )

  if (result != 0) {
    lean_dec(public_key)
    lean_dec(secret_key)
    lean_object* error_msg = lean_mk_string("crypto_sign_seed_keypair failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(pair, 0, public_key)
  lean_ctor_set(pair, 1, secret_key)

  return lean_io_result_mk_ok(pair)

alloy c extern "lean_crypto_sign"
def sign (message : ByteArray) (secretKey : ByteArray) : IO ByteArray :=
  size_t secret_key_size = lean_sarray_size(secretKey)
  size_t expected_secret_key_size = crypto_sign_SECRETKEYBYTES
  if (secret_key_size != expected_secret_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid secret key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  size_t signed_message_len = message_len + crypto_sign_BYTES

  lean_object* signed_message = lean_alloc_sarray(sizeof(unsigned char), signed_message_len, signed_message_len)
  unsigned long long signed_message_len_actual;

  int result = crypto_sign(
    lean_sarray_cptr(signed_message), &signed_message_len_actual,
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(secretKey)
  )

  if (result != 0) {
    lean_dec(signed_message)
    lean_object* error_msg = lean_mk_string("crypto_sign failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(signed_message)

alloy c extern "lean_crypto_sign_open"
def signOpen (signedMessage : ByteArray) (publicKey : ByteArray) : IO ByteArray :=
  size_t public_key_size = lean_sarray_size(publicKey)
  size_t expected_public_key_size = crypto_sign_PUBLICKEYBYTES
  if (public_key_size != expected_public_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid public key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t signed_message_len = lean_sarray_size(signedMessage)
  if (signed_message_len < crypto_sign_BYTES) {
    lean_object* error_msg = lean_mk_string("Signed message too short")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = signed_message_len - crypto_sign_BYTES
  lean_object* message = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)
  unsigned long long message_len_actual;

  int result = crypto_sign_open(
    lean_sarray_cptr(message), &message_len_actual,
    lean_sarray_cptr(signedMessage), signed_message_len,
    lean_sarray_cptr(publicKey)
  )

  if (result != 0) {
    lean_dec(message)
    lean_object* error_msg = lean_mk_string("crypto_sign_open failed (signature verification failed)")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(message)

alloy c extern "lean_crypto_sign_detached"
def signDetached (message : ByteArray) (secretKey : ByteArray) : IO ByteArray :=
  size_t secret_key_size = lean_sarray_size(secretKey)
  size_t expected_secret_key_size = crypto_sign_SECRETKEYBYTES
  if (secret_key_size != expected_secret_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid secret key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  lean_object* signature = lean_alloc_sarray(sizeof(unsigned char), crypto_sign_BYTES, crypto_sign_BYTES)
  unsigned long long signature_len_actual;

  int result = crypto_sign_detached(
    lean_sarray_cptr(signature), &signature_len_actual,
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(secretKey)
  )

  if (result != 0) {
    lean_dec(signature)
    lean_object* error_msg = lean_mk_string("crypto_sign_detached failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(signature)

alloy c extern "lean_crypto_sign_verify_detached"
def signVerifyDetached (signature : ByteArray) (message : ByteArray) (publicKey : ByteArray) : IO Bool :=
  size_t signature_size = lean_sarray_size(signature)
  size_t expected_signature_size = crypto_sign_BYTES
  if (signature_size != expected_signature_size) {
    lean_object* error_msg = lean_mk_string("Invalid signature size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t public_key_size = lean_sarray_size(publicKey)
  size_t expected_public_key_size = crypto_sign_PUBLICKEYBYTES
  if (public_key_size != expected_public_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid public key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)

  int result = crypto_sign_verify_detached(
    lean_sarray_cptr(signature),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(publicKey)
  )

  uint8_t verification_success = (result == 0)
  return lean_io_result_mk_ok(lean_box(verification_success))

end Sodium.FFI
