import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI.KeyExch

variable {σ : Type}

alloy c section
extern lean_obj_res lean_sodium_malloc(b_lean_obj_arg, size_t, lean_obj_arg);
extern lean_obj_res sodium_secure_to_lean(void*);
extern void* sodium_secure_of_lean(b_lean_obj_arg);
end

-- Constants for crypto_kx
def PUBLICKEYBYTES : Nat := 32
def SECRETKEYBYTES : Nat := 32
def SEEDBYTES : Nat := 32
def SESSIONKEYBYTES : Nat := 32

alloy c extern "lean_crypto_kx_keypair"
def keypair {τ : @& Sodium σ} : IO (ByteVector PUBLICKEYBYTES × SecretVector τ SECRETKEYBYTES) :=
  lean_object* public_key = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_kx_PUBLICKEYBYTES,
    crypto_kx_PUBLICKEYBYTES);

  lean_object* secret_key_io = lean_sodium_malloc(τ, crypto_kx_SECRETKEYBYTES, _1);

  if (lean_io_result_is_error(secret_key_io)) {
    lean_dec(public_key);
    return secret_key_io;
  }

  lean_object* secret_key = lean_io_result_take_value(secret_key_io);
  void* secret_key_ref = sodium_secure_of_lean(lean_ctor_get(secret_key, 0));
  sodium_mprotect_readwrite(secret_key_ref);

  int err = crypto_kx_keypair(lean_sarray_cptr(public_key), (uint8_t*) secret_key_ref);

  if (err != 0) {
    sodium_munlock(secret_key_ref, crypto_kx_SECRETKEYBYTES);
    lean_dec(public_key);
    lean_dec(secret_key);
    lean_object* error_msg = lean_mk_string("crypto_kx_keypair failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  sodium_mprotect_noaccess(secret_key_ref);

  lean_object* ret = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(ret, 0, public_key);
  lean_ctor_set(ret, 1, secret_key);

  return lean_io_result_mk_ok(ret);

alloy c extern "lean_crypto_kx_seed_keypair"
def seedKeypair {τ : @& Sodium σ} (seed : @& SecretVector τ SEEDBYTES) : IO (ByteVector PUBLICKEYBYTES × SecretVector τ SECRETKEYBYTES) :=
  size_t seed_len = lean_ctor_get_usize(seed, 1);

  if (seed_len != crypto_kx_SEEDBYTES) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_kx_seed_keypair");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* public_key = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_kx_PUBLICKEYBYTES,
    crypto_kx_PUBLICKEYBYTES);

  lean_object* secret_key_io = lean_sodium_malloc(τ, crypto_kx_SECRETKEYBYTES, _2);

  if (lean_io_result_is_error(secret_key_io)) {
    lean_dec(public_key);
    return secret_key_io;
  }

  lean_object* secret_key = lean_io_result_take_value(secret_key_io);
  void* secret_key_ref = sodium_secure_of_lean(lean_ctor_get(secret_key, 0));
  void* seed_ref = sodium_secure_of_lean(lean_ctor_get(seed, 0));

  sodium_mprotect_readwrite(secret_key_ref);
  sodium_mprotect_readonly(seed_ref);

  int err = crypto_kx_seed_keypair(
    lean_sarray_cptr(public_key),
    (uint8_t*) secret_key_ref,
    (uint8_t*) seed_ref);

  sodium_mprotect_noaccess(secret_key_ref);
  sodium_mprotect_noaccess(seed_ref);

  if (err != 0) {
    sodium_munlock(secret_key_ref, crypto_kx_SECRETKEYBYTES);
    lean_dec(public_key);
    lean_dec(secret_key);
    lean_object* error_msg = lean_mk_string("crypto_kx_seed_keypair failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* ret = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(ret, 0, public_key);
  lean_ctor_set(ret, 1, secret_key);
  return lean_io_result_mk_ok(ret);

alloy c extern "lean_crypto_kx_client_session_keys"
def clientSessionKeys {τ : @& Sodium σ}
    (clientPublicKey : @& ByteVector PUBLICKEYBYTES)
    (clientSecretKey : @& SecretVector τ SECRETKEYBYTES)
    (serverPublicKey : @& ByteVector PUBLICKEYBYTES)
    : IO (Option (SecretVector τ SESSIONKEYBYTES × SecretVector τ SESSIONKEYBYTES)) :=
  size_t client_sk_len = lean_ctor_get_usize(clientSecretKey, 1);

  if (
    lean_sarray_size(clientPublicKey) != crypto_kx_PUBLICKEYBYTES ||
    lean_sarray_size(serverPublicKey) != crypto_kx_PUBLICKEYBYTES ||
    client_sk_len != crypto_kx_SECRETKEYBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_kx_client_session_keys");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* rx_key_io = lean_sodium_malloc(τ, crypto_kx_SESSIONKEYBYTES, _4);
  if (lean_io_result_is_error(rx_key_io)) {
    return rx_key_io;
  }

  lean_object* tx_key_io = lean_sodium_malloc(τ, crypto_kx_SESSIONKEYBYTES, _4);
  if (lean_io_result_is_error(tx_key_io)) {
    lean_dec(rx_key_io);
    return tx_key_io;
  }

  lean_object* rx_key = lean_io_result_take_value(rx_key_io);
  lean_object* tx_key = lean_io_result_take_value(tx_key_io);

  void* rx_key_ref = sodium_secure_of_lean(lean_ctor_get(rx_key, 0));
  void* tx_key_ref = sodium_secure_of_lean(lean_ctor_get(tx_key, 0));
  void* client_sk_ref = sodium_secure_of_lean(lean_ctor_get(clientSecretKey, 0));

  sodium_mprotect_readwrite(rx_key_ref);
  sodium_mprotect_readwrite(tx_key_ref);
  sodium_mprotect_readonly(client_sk_ref);

  int err = crypto_kx_client_session_keys(
    (uint8_t*) rx_key_ref,
    (uint8_t*) tx_key_ref,
    lean_sarray_cptr(clientPublicKey),
    (uint8_t*) client_sk_ref,
    lean_sarray_cptr(serverPublicKey));

  sodium_mprotect_noaccess(rx_key_ref);
  sodium_mprotect_noaccess(tx_key_ref);
  sodium_mprotect_noaccess(client_sk_ref);

  if (err != 0) {
    sodium_munlock(rx_key_ref, crypto_kx_SESSIONKEYBYTES);
    sodium_munlock(tx_key_ref, crypto_kx_SESSIONKEYBYTES);
    lean_dec(rx_key);
    lean_dec(tx_key);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, rx_key);
  lean_ctor_set(pair, 1, tx_key);
  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, pair);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_kx_server_session_keys"
def serverSessionKeys {τ : @& Sodium σ}
    (serverPublicKey : @& ByteVector PUBLICKEYBYTES)
    (serverSecretKey : @& SecretVector τ SECRETKEYBYTES)
    (clientPublicKey : @& ByteVector PUBLICKEYBYTES)
    : IO (Option (SecretVector τ SESSIONKEYBYTES × SecretVector τ SESSIONKEYBYTES)) :=
  size_t server_sk_len = lean_ctor_get_usize(serverSecretKey, 1);

  if (
    lean_sarray_size(serverPublicKey) != crypto_kx_PUBLICKEYBYTES ||
    lean_sarray_size(clientPublicKey) != crypto_kx_PUBLICKEYBYTES ||
    server_sk_len != crypto_kx_SECRETKEYBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_kx_server_session_keys");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* rx_key_io = lean_sodium_malloc(τ, crypto_kx_SESSIONKEYBYTES, _4);
  if (lean_io_result_is_error(rx_key_io)) {
    return rx_key_io;
  }

  lean_object* tx_key_io = lean_sodium_malloc(τ, crypto_kx_SESSIONKEYBYTES, _4);
  if (lean_io_result_is_error(tx_key_io)) {
    lean_dec(rx_key_io);
    return tx_key_io;
  }

  lean_object* rx_key = lean_io_result_take_value(rx_key_io);
  lean_object* tx_key = lean_io_result_take_value(tx_key_io);

  void* rx_key_ref = sodium_secure_of_lean(lean_ctor_get(rx_key, 0));
  void* tx_key_ref = sodium_secure_of_lean(lean_ctor_get(tx_key, 0));
  void* server_sk_ref = sodium_secure_of_lean(lean_ctor_get(serverSecretKey, 0));

  sodium_mprotect_readwrite(rx_key_ref);
  sodium_mprotect_readwrite(tx_key_ref);
  sodium_mprotect_readonly(server_sk_ref);

  int err = crypto_kx_server_session_keys(
    (uint8_t*) rx_key_ref,
    (uint8_t*) tx_key_ref,
    lean_sarray_cptr(serverPublicKey),
    (uint8_t*) server_sk_ref,
    lean_sarray_cptr(clientPublicKey));

  sodium_mprotect_noaccess(rx_key_ref);
  sodium_mprotect_noaccess(tx_key_ref);
  sodium_mprotect_noaccess(server_sk_ref);

  if (err != 0) {
    sodium_munlock(rx_key_ref, crypto_kx_SESSIONKEYBYTES);
    sodium_munlock(tx_key_ref, crypto_kx_SESSIONKEYBYTES);
    lean_dec(rx_key);
    lean_dec(tx_key);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, rx_key);
  lean_ctor_set(pair, 1, tx_key);
  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, pair);
  return lean_io_result_mk_ok(some);

end Sodium.FFI.KeyExch
