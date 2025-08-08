import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI

-- Key exchange constants
def KX_PUBLICKEYBYTES : UInt32 := 32
def KX_SECRETKEYBYTES : UInt32 := 32
def KX_SEEDBYTES : UInt32 := 32
def KX_SESSIONKEYBYTES : UInt32 := 32

/- Key Generation Functions -/

alloy c extern "lean_crypto_kx_keypair"
def kxKeypair : BaseIO (ByteArray × ByteArray) :=
  lean_object* publicKey = lean_alloc_sarray(sizeof(unsigned char), crypto_kx_PUBLICKEYBYTES, crypto_kx_PUBLICKEYBYTES)
  lean_object* secretKey = lean_alloc_sarray(sizeof(unsigned char), crypto_kx_SECRETKEYBYTES, crypto_kx_SECRETKEYBYTES)

  int result = crypto_kx_keypair(
    lean_sarray_cptr(publicKey),
    lean_sarray_cptr(secretKey)
  )

  if (result != 0) {
    lean_dec_ref(publicKey)
    lean_dec_ref(secretKey)
    lean_object* error_msg = lean_mk_string("Key exchange keypair generation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(pair, 0, publicKey)
  lean_ctor_set(pair, 1, secretKey)

  return lean_io_result_mk_ok(pair)

alloy c extern "lean_crypto_kx_seed_keypair"
def kxSeedKeypair (seed : ByteArray) : IO (ByteArray × ByteArray) :=
  if (lean_sarray_size(seed) != crypto_kx_SEEDBYTES) {
    lean_object* error_msg = lean_mk_string("Seed must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* publicKey = lean_alloc_sarray(sizeof(unsigned char), crypto_kx_PUBLICKEYBYTES, crypto_kx_PUBLICKEYBYTES)
  lean_object* secretKey = lean_alloc_sarray(sizeof(unsigned char), crypto_kx_SECRETKEYBYTES, crypto_kx_SECRETKEYBYTES)

  int result = crypto_kx_seed_keypair(
    lean_sarray_cptr(publicKey),
    lean_sarray_cptr(secretKey),
    lean_sarray_cptr(seed)
  )

  if (result != 0) {
    lean_dec_ref(publicKey)
    lean_dec_ref(secretKey)
    lean_object* error_msg = lean_mk_string("Key exchange seed keypair generation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(pair, 0, publicKey)
  lean_ctor_set(pair, 1, secretKey)

  return lean_io_result_mk_ok(pair)

/- Session Key Derivation Functions -/

alloy c extern "lean_crypto_kx_client_session_keys"
def kxClientSessionKeys (clientPk : ByteArray) (clientSk : ByteArray) (serverPk : ByteArray) : IO (ByteArray × ByteArray) :=
  if (lean_sarray_size(clientPk) != crypto_kx_PUBLICKEYBYTES) {
    lean_object* error_msg = lean_mk_string("Client public key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(clientSk) != crypto_kx_SECRETKEYBYTES) {
    lean_object* error_msg = lean_mk_string("Client secret key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(serverPk) != crypto_kx_PUBLICKEYBYTES) {
    lean_object* error_msg = lean_mk_string("Server public key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* rxKey = lean_alloc_sarray(sizeof(unsigned char), crypto_kx_SESSIONKEYBYTES, crypto_kx_SESSIONKEYBYTES)
  lean_object* txKey = lean_alloc_sarray(sizeof(unsigned char), crypto_kx_SESSIONKEYBYTES, crypto_kx_SESSIONKEYBYTES)

  int result = crypto_kx_client_session_keys(
    lean_sarray_cptr(rxKey),
    lean_sarray_cptr(txKey),
    lean_sarray_cptr(clientPk),
    lean_sarray_cptr(clientSk),
    lean_sarray_cptr(serverPk)
  )

  if (result != 0) {
    lean_dec_ref(rxKey)
    lean_dec_ref(txKey)
    lean_object* error_msg = lean_mk_string("Client session key derivation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(pair, 0, rxKey)
  lean_ctor_set(pair, 1, txKey)

  return lean_io_result_mk_ok(pair)

alloy c extern "lean_crypto_kx_server_session_keys"
def kxServerSessionKeys (serverPk : ByteArray) (serverSk : ByteArray) (clientPk : ByteArray) : IO (ByteArray × ByteArray) :=
  if (lean_sarray_size(serverPk) != crypto_kx_PUBLICKEYBYTES) {
    lean_object* error_msg = lean_mk_string("Server public key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(serverSk) != crypto_kx_SECRETKEYBYTES) {
    lean_object* error_msg = lean_mk_string("Server secret key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  if (lean_sarray_size(clientPk) != crypto_kx_PUBLICKEYBYTES) {
    lean_object* error_msg = lean_mk_string("Client public key must be 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* rxKey = lean_alloc_sarray(sizeof(unsigned char), crypto_kx_SESSIONKEYBYTES, crypto_kx_SESSIONKEYBYTES)
  lean_object* txKey = lean_alloc_sarray(sizeof(unsigned char), crypto_kx_SESSIONKEYBYTES, crypto_kx_SESSIONKEYBYTES)

  int result = crypto_kx_server_session_keys(
    lean_sarray_cptr(rxKey),
    lean_sarray_cptr(txKey),
    lean_sarray_cptr(serverPk),
    lean_sarray_cptr(serverSk),
    lean_sarray_cptr(clientPk)
  )

  if (result != 0) {
    lean_dec_ref(rxKey)
    lean_dec_ref(txKey)
    lean_object* error_msg = lean_mk_string("Server session key derivation failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(pair, 0, rxKey)
  lean_ctor_set(pair, 1, txKey)

  return lean_io_result_mk_ok(pair)

end Sodium.FFI
