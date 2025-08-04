import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI

-- Constants for crypto_box
def BOX_PUBLICKEYBYTES : USize := 32
def BOX_SECRETKEYBYTES : USize := 32
def BOX_NONCEBYTES : USize := 24
def BOX_MACBYTES : USize := 16
def BOX_SEEDBYTES : USize := 32
def BOX_BEFORENMBYTES : USize := 32
def BOX_SEALBYTES : USize := 48  -- PUBLICKEYBYTES + MACBYTES

alloy c extern "lean_crypto_box_keypair"
def boxKeypair : IO (ByteArray × ByteArray) :=
  lean_object* public_key = lean_alloc_sarray(
    sizeof(unsigned char),
    crypto_box_PUBLICKEYBYTES,
    crypto_box_PUBLICKEYBYTES)
  lean_object* secret_key = lean_alloc_sarray(
    sizeof(unsigned char),
    crypto_box_SECRETKEYBYTES,
    crypto_box_SECRETKEYBYTES)

  int result = crypto_box_keypair(
    lean_sarray_cptr(public_key),
    lean_sarray_cptr(secret_key)
  )

  if (result != 0) {
    lean_dec(public_key)
    lean_dec(secret_key)
    lean_object* error_msg = lean_mk_string("crypto_box_keypair failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(pair, 0, public_key)
  lean_ctor_set(pair, 1, secret_key)

  return lean_io_result_mk_ok(pair)

alloy c extern "lean_crypto_box_seed_keypair"
def boxSeedKeypair (seed : ByteArray) : IO (ByteArray × ByteArray) :=
  size_t seed_size = lean_sarray_size(seed)
  size_t expected_seed_size = crypto_box_SEEDBYTES
  if (seed_size != expected_seed_size) {
    lean_object* error_msg = lean_mk_string("Invalid seed size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* public_key = lean_alloc_sarray(
    sizeof(unsigned char),
    crypto_box_PUBLICKEYBYTES,
    crypto_box_PUBLICKEYBYTES)
  lean_object* secret_key = lean_alloc_sarray(
    sizeof(unsigned char),
    crypto_box_SECRETKEYBYTES,
    crypto_box_SECRETKEYBYTES)

  int result = crypto_box_seed_keypair(
    lean_sarray_cptr(public_key),
    lean_sarray_cptr(secret_key),
    lean_sarray_cptr(seed)
  )

  if (result != 0) {
    lean_dec(public_key)
    lean_dec(secret_key)
    lean_object* error_msg = lean_mk_string("crypto_box_seed_keypair failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(pair, 0, public_key)
  lean_ctor_set(pair, 1, secret_key)

  return lean_io_result_mk_ok(pair)

alloy c extern "lean_crypto_box_easy"
def boxEasy (message : ByteArray) (nonce : ByteArray) (publicKey : ByteArray) (secretKey : ByteArray) : IO ByteArray :=
  size_t nonce_size = lean_sarray_size(nonce)
  size_t expected_nonce_size = crypto_box_NONCEBYTES
  if (nonce_size != expected_nonce_size) {
    lean_object* error_msg = lean_mk_string("Invalid nonce size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t public_key_size = lean_sarray_size(publicKey)
  size_t expected_public_key_size = crypto_box_PUBLICKEYBYTES
  if (public_key_size != expected_public_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid public key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t secret_key_size = lean_sarray_size(secretKey)
  size_t expected_secret_key_size = crypto_box_SECRETKEYBYTES
  if (secret_key_size != expected_secret_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid secret key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  size_t ciphertext_len = message_len + crypto_box_MACBYTES

  lean_object* ciphertext = lean_alloc_sarray(sizeof(unsigned char), ciphertext_len, ciphertext_len)

  int result = crypto_box_easy(
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(publicKey),
    lean_sarray_cptr(secretKey)
  )

  if (result != 0) {
    lean_dec(ciphertext)
    lean_object* error_msg = lean_mk_string("crypto_box_easy failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(ciphertext)

alloy c extern "lean_crypto_box_open_easy"
def boxOpenEasy (ciphertext : ByteArray) (nonce : ByteArray) (publicKey : ByteArray) (secretKey : ByteArray) : IO ByteArray :=
  size_t nonce_size = lean_sarray_size(nonce)
  size_t expected_nonce_size = crypto_box_NONCEBYTES
  if (nonce_size != expected_nonce_size) {
    lean_object* error_msg = lean_mk_string("Invalid nonce size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t public_key_size = lean_sarray_size(publicKey)
  size_t expected_public_key_size = crypto_box_PUBLICKEYBYTES
  if (public_key_size != expected_public_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid public key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t secret_key_size = lean_sarray_size(secretKey)
  size_t expected_secret_key_size = crypto_box_SECRETKEYBYTES
  if (secret_key_size != expected_secret_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid secret key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t ciphertext_len = lean_sarray_size(ciphertext)
  if (ciphertext_len < crypto_box_MACBYTES) {
    lean_object* error_msg = lean_mk_string("Ciphertext too short")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = ciphertext_len - crypto_box_MACBYTES
  lean_object* message = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)

  int result = crypto_box_open_easy(
    lean_sarray_cptr(message),
    lean_sarray_cptr(ciphertext), ciphertext_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(publicKey),
    lean_sarray_cptr(secretKey)
  )

  if (result != 0) {
    lean_dec(message)
    lean_object* error_msg = lean_mk_string("crypto_box_open_easy failed (authentication failed)")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(message)

alloy c extern "lean_crypto_box_detached"
def boxDetached (message : ByteArray) (nonce : ByteArray) (publicKey : ByteArray) (secretKey : ByteArray) : IO (ByteArray × ByteArray) :=
  size_t nonce_size = lean_sarray_size(nonce)
  size_t expected_nonce_size = crypto_box_NONCEBYTES
  if (nonce_size != expected_nonce_size) {
    lean_object* error_msg = lean_mk_string("Invalid nonce size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t public_key_size = lean_sarray_size(publicKey)
  size_t expected_public_key_size = crypto_box_PUBLICKEYBYTES
  if (public_key_size != expected_public_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid public key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t secret_key_size = lean_sarray_size(secretKey)
  size_t expected_secret_key_size = crypto_box_SECRETKEYBYTES
  if (secret_key_size != expected_secret_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid secret key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  lean_object* ciphertext = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)
  lean_object* mac = lean_alloc_sarray(sizeof(unsigned char), crypto_box_MACBYTES, crypto_box_MACBYTES)

  int result = crypto_box_detached(
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(mac),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(publicKey),
    lean_sarray_cptr(secretKey)
  )

  if (result != 0) {
    lean_dec(ciphertext)
    lean_dec(mac)
    lean_object* error_msg = lean_mk_string("crypto_box_detached failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(pair, 0, ciphertext)
  lean_ctor_set(pair, 1, mac)

  return lean_io_result_mk_ok(pair)

alloy c extern "lean_crypto_box_open_detached" 
def boxOpenDetached (ciphertext : ByteArray) (mac : ByteArray) (nonce : ByteArray) (publicKey : ByteArray) (secretKey : ByteArray) : IO ByteArray :=
  size_t nonce_size = lean_sarray_size(nonce)
  size_t expected_nonce_size = crypto_box_NONCEBYTES
  if (nonce_size != expected_nonce_size) {
    lean_object* error_msg = lean_mk_string("Invalid nonce size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t public_key_size = lean_sarray_size(publicKey)
  size_t expected_public_key_size = crypto_box_PUBLICKEYBYTES
  if (public_key_size != expected_public_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid public key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t secret_key_size = lean_sarray_size(secretKey)
  size_t expected_secret_key_size = crypto_box_SECRETKEYBYTES
  if (secret_key_size != expected_secret_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid secret key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t mac_size = lean_sarray_size(mac)
  size_t expected_mac_size = crypto_box_MACBYTES
  if (mac_size != expected_mac_size) {
    lean_object* error_msg = lean_mk_string("Invalid MAC size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t ciphertext_len = lean_sarray_size(ciphertext)
  lean_object* message = lean_alloc_sarray(sizeof(unsigned char), ciphertext_len, ciphertext_len)

  int result = crypto_box_open_detached(
    lean_sarray_cptr(message),
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(mac),
    ciphertext_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(publicKey),
    lean_sarray_cptr(secretKey)
  )

  if (result != 0) {
    lean_dec(message)
    lean_object* error_msg = lean_mk_string("crypto_box_open_detached failed (authentication failed)")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(message)

alloy c extern "lean_crypto_box_beforenm"
def boxBeforenm (publicKey : ByteArray) (secretKey : ByteArray) : IO ByteArray :=
  size_t public_key_size = lean_sarray_size(publicKey)
  size_t expected_public_key_size = crypto_box_PUBLICKEYBYTES
  if (public_key_size != expected_public_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid public key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t secret_key_size = lean_sarray_size(secretKey)
  size_t expected_secret_key_size = crypto_box_SECRETKEYBYTES
  if (secret_key_size != expected_secret_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid secret key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* shared_secret = lean_alloc_sarray(
    sizeof(unsigned char),
    crypto_box_BEFORENMBYTES,
    crypto_box_BEFORENMBYTES)

  int result = crypto_box_beforenm(
    lean_sarray_cptr(shared_secret),
    lean_sarray_cptr(publicKey),
    lean_sarray_cptr(secretKey)
  )

  if (result != 0) {
    lean_dec(shared_secret)
    lean_object* error_msg = lean_mk_string("crypto_box_beforenm failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(shared_secret)

alloy c extern "lean_crypto_box_easy_afternm"
def boxEasyAfternm (message : ByteArray) (nonce : ByteArray) (sharedSecret : ByteArray) : IO ByteArray :=
  size_t nonce_size = lean_sarray_size(nonce)
  size_t expected_nonce_size = crypto_box_NONCEBYTES
  if (nonce_size != expected_nonce_size) {
    lean_object* error_msg = lean_mk_string("Invalid nonce size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t shared_secret_size = lean_sarray_size(sharedSecret)
  size_t expected_shared_secret_size = crypto_box_BEFORENMBYTES
  if (shared_secret_size != expected_shared_secret_size) {
    lean_object* error_msg = lean_mk_string("Invalid shared secret size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  size_t ciphertext_len = message_len + crypto_box_MACBYTES

  lean_object* ciphertext = lean_alloc_sarray(sizeof(unsigned char), ciphertext_len, ciphertext_len)

  int result = crypto_box_easy_afternm(
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(sharedSecret)
  )

  if (result != 0) {
    lean_dec(ciphertext)
    lean_object* error_msg = lean_mk_string("crypto_box_easy_afternm failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(ciphertext)

alloy c extern "lean_crypto_box_open_easy_afternm"
def boxOpenEasyAfternm (ciphertext : ByteArray) (nonce : ByteArray) (sharedSecret : ByteArray) : IO ByteArray :=
  size_t nonce_size = lean_sarray_size(nonce)
  size_t expected_nonce_size = crypto_box_NONCEBYTES
  if (nonce_size != expected_nonce_size) {
    lean_object* error_msg = lean_mk_string("Invalid nonce size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t shared_secret_size = lean_sarray_size(sharedSecret)
  size_t expected_shared_secret_size = crypto_box_BEFORENMBYTES
  if (shared_secret_size != expected_shared_secret_size) {
    lean_object* error_msg = lean_mk_string("Invalid shared secret size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t ciphertext_len = lean_sarray_size(ciphertext)
  if (ciphertext_len < crypto_box_MACBYTES) {
    lean_object* error_msg = lean_mk_string("Ciphertext too short")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = ciphertext_len - crypto_box_MACBYTES
  lean_object* message = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)

  int result = crypto_box_open_easy_afternm(
    lean_sarray_cptr(message),
    lean_sarray_cptr(ciphertext), ciphertext_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(sharedSecret)
  )

  if (result != 0) {
    lean_dec(message)
    lean_object* error_msg = lean_mk_string("crypto_box_open_easy_afternm failed (authentication failed)")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(message)

alloy c extern "lean_crypto_box_detached_afternm"
def boxDetachedAfternm (message : ByteArray) (nonce : ByteArray) (sharedSecret : ByteArray) : IO (ByteArray × ByteArray) :=
  size_t nonce_size = lean_sarray_size(nonce)
  size_t expected_nonce_size = crypto_box_NONCEBYTES
  if (nonce_size != expected_nonce_size) {
    lean_object* error_msg = lean_mk_string("Invalid nonce size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t shared_secret_size = lean_sarray_size(sharedSecret)
  size_t expected_shared_secret_size = crypto_box_BEFORENMBYTES
  if (shared_secret_size != expected_shared_secret_size) {
    lean_object* error_msg = lean_mk_string("Invalid shared secret size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  lean_object* ciphertext = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)
  lean_object* mac = lean_alloc_sarray(sizeof(unsigned char), crypto_box_MACBYTES, crypto_box_MACBYTES)

  int result = crypto_box_detached_afternm(
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(mac),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(sharedSecret)
  )

  if (result != 0) {
    lean_dec(ciphertext)
    lean_dec(mac)
    lean_object* error_msg = lean_mk_string("crypto_box_detached_afternm failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(pair, 0, ciphertext)
  lean_ctor_set(pair, 1, mac)

  return lean_io_result_mk_ok(pair)

alloy c extern "lean_crypto_box_open_detached_afternm"
def boxOpenDetachedAfternm (ciphertext : ByteArray) (mac : ByteArray) (nonce : ByteArray) (sharedSecret : ByteArray) : IO ByteArray :=
  size_t nonce_size = lean_sarray_size(nonce)
  size_t expected_nonce_size = crypto_box_NONCEBYTES
  if (nonce_size != expected_nonce_size) {
    lean_object* error_msg = lean_mk_string("Invalid nonce size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t shared_secret_size = lean_sarray_size(sharedSecret)
  size_t expected_shared_secret_size = crypto_box_BEFORENMBYTES
  if (shared_secret_size != expected_shared_secret_size) {
    lean_object* error_msg = lean_mk_string("Invalid shared secret size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t mac_size = lean_sarray_size(mac)
  size_t expected_mac_size = crypto_box_MACBYTES
  if (mac_size != expected_mac_size) {
    lean_object* error_msg = lean_mk_string("Invalid MAC size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t ciphertext_len = lean_sarray_size(ciphertext)
  lean_object* message = lean_alloc_sarray(sizeof(unsigned char), ciphertext_len, ciphertext_len)

  int result = crypto_box_open_detached_afternm(
    lean_sarray_cptr(message),
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(mac),
    ciphertext_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(sharedSecret)
  )

  if (result != 0) {
    lean_dec(message)
    lean_object* error_msg = lean_mk_string("crypto_box_open_detached_afternm failed (authentication failed)")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(message)

alloy c extern "lean_crypto_box_seal"
def boxSeal (message : ByteArray) (publicKey : ByteArray) : IO ByteArray :=
  size_t public_key_size = lean_sarray_size(publicKey)
  size_t expected_public_key_size = crypto_box_PUBLICKEYBYTES
  if (public_key_size != expected_public_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid public key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = lean_sarray_size(message)
  size_t sealed_len = message_len + crypto_box_SEALBYTES

  lean_object* sealed = lean_alloc_sarray(sizeof(unsigned char), sealed_len, sealed_len)

  int result = crypto_box_seal(
    lean_sarray_cptr(sealed),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(publicKey)
  )

  if (result != 0) {
    lean_dec(sealed)
    lean_object* error_msg = lean_mk_string("crypto_box_seal failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(sealed)

alloy c extern "lean_crypto_box_seal_open"
def boxSealOpen (sealed : ByteArray) (publicKey : ByteArray) (secretKey : ByteArray) : IO ByteArray :=
  size_t public_key_size = lean_sarray_size(publicKey)
  size_t expected_public_key_size = crypto_box_PUBLICKEYBYTES
  if (public_key_size != expected_public_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid public key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t secret_key_size = lean_sarray_size(secretKey)
  size_t expected_secret_key_size = crypto_box_SECRETKEYBYTES
  if (secret_key_size != expected_secret_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid secret key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t sealed_len = lean_sarray_size(sealed)
  if (sealed_len < crypto_box_SEALBYTES) {
    lean_object* error_msg = lean_mk_string("Sealed message too short")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = sealed_len - crypto_box_SEALBYTES
  lean_object* message = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len)

  int result = crypto_box_seal_open(
    lean_sarray_cptr(message),
    lean_sarray_cptr(sealed), sealed_len,
    lean_sarray_cptr(publicKey),
    lean_sarray_cptr(secretKey)
  )

  if (result != 0) {
    lean_dec(message)
    lean_object* error_msg = lean_mk_string("crypto_box_seal_open failed (authentication failed)")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(message)

alloy c extern "lean_crypto_box_messagebytes_max"
def boxMessageBytesMax : BaseIO USize :=
  size_t max_bytes = crypto_box_messagebytes_max()
  return lean_io_result_mk_ok(lean_box_usize(max_bytes))

end Sodium.FFI
