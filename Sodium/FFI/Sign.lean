import Sodium.FFI.Basic

universe u

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI.Sign

variable {σ : Type u}

alloy c section
extern lean_obj_res lean_sodium_malloc(b_lean_obj_arg, size_t, lean_obj_arg);
extern lean_obj_res sodium_secure_to_lean(void*);
extern void* sodium_secure_of_lean(b_lean_obj_arg);
end

-- Constants for crypto_sign (Ed25519)
def PUBLICKEYBYTES : Nat := 32
def SECRETKEYBYTES : Nat := 64
def SEEDBYTES : Nat := 32
def BYTES : Nat := 64

alloy c extern "lean_crypto_sign_keypair"
def keypair {τ : @& Sodium σ} : IO (ByteVector PUBLICKEYBYTES × SecretVector τ SECRETKEYBYTES) :=
  lean_object* public_key = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_sign_PUBLICKEYBYTES,
    crypto_sign_PUBLICKEYBYTES);

  lean_object* secret_key_io = lean_sodium_malloc(τ, crypto_sign_SECRETKEYBYTES, _1);

  if (lean_io_result_is_error(secret_key_io)) {
    lean_dec(public_key);
    return secret_key_io;
  }

  lean_object* secret_key = lean_io_result_take_value(secret_key_io);
  void* secret_key_ref = sodium_secure_of_lean(lean_ctor_get(secret_key, 0));
  sodium_mprotect_readwrite(secret_key_ref);

  int err = crypto_sign_keypair(lean_sarray_cptr(public_key), (uint8_t*) secret_key_ref);

  if (err != 0) {
    sodium_munlock(secret_key_ref, crypto_sign_SECRETKEYBYTES);
    lean_dec(public_key);
    lean_dec(secret_key);
    lean_object* error_msg = lean_mk_string("crypto_sign_keypair failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  sodium_mprotect_noaccess(secret_key_ref);

  lean_object* ret = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(ret, 0, public_key);
  lean_ctor_set(ret, 1, secret_key);

  return lean_io_result_mk_ok(ret);

alloy c extern "lean_crypto_sign_seed_keypair"
def seedKeypair {τ : @& Sodium σ} (seed : @& SecretVector τ SEEDBYTES) : IO (ByteVector PUBLICKEYBYTES × SecretVector τ SECRETKEYBYTES) :=
  size_t seed_len = lean_ctor_get_usize(seed, 1);

  if (seed_len != crypto_sign_SEEDBYTES) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_sign_seed_keypair");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* public_key = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_sign_PUBLICKEYBYTES,
    crypto_sign_PUBLICKEYBYTES);

  lean_object* secret_key_io = lean_sodium_malloc(τ, crypto_sign_SECRETKEYBYTES, _2);

  if (lean_io_result_is_error(secret_key_io)) {
    lean_dec(public_key);
    return secret_key_io;
  }

  lean_object* secret_key = lean_io_result_take_value(secret_key_io);
  void* secret_key_ref = sodium_secure_of_lean(lean_ctor_get(secret_key, 0));
  void* seed_ref = sodium_secure_of_lean(lean_ctor_get(seed, 0));

  sodium_mprotect_readwrite(secret_key_ref);
  sodium_mprotect_readonly(seed_ref);

  int err = crypto_sign_seed_keypair(
    lean_sarray_cptr(public_key),
    (uint8_t*) secret_key_ref,
    (uint8_t*) seed_ref);

  sodium_mprotect_noaccess(secret_key_ref);
  sodium_mprotect_noaccess(seed_ref);

  if (err != 0) {
    sodium_munlock(secret_key_ref, crypto_sign_SECRETKEYBYTES);
    lean_dec(public_key);
    lean_dec(secret_key);
    lean_object* error_msg = lean_mk_string("crypto_sign_seed_keypair failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* ret = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(ret, 0, public_key);
  lean_ctor_set(ret, 1, secret_key);
  return lean_io_result_mk_ok(ret);

alloy c extern "lean_crypto_sign"
def sign {τ : @& Sodium σ} {n : Nat}
    (message : @& ByteVector n)
    (secretKey : @& SecretVector τ SECRETKEYBYTES)
    : IO (ByteVector (BYTES + n)) :=
  size_t sk_len = lean_ctor_get_usize(secretKey, 1);
  size_t msg_len = lean_sarray_size(message);

  if (sk_len != crypto_sign_SECRETKEYBYTES) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_sign");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  size_t signed_msg_len = msg_len + crypto_sign_BYTES;
  lean_object* signed_message = lean_alloc_sarray(
    sizeof(uint8_t),
    signed_msg_len,
    signed_msg_len);

  void* sk_ref = sodium_secure_of_lean(lean_ctor_get(secretKey, 0));
  sodium_mprotect_readonly(sk_ref);

  unsigned long long signed_message_len;
  int err = crypto_sign(
    lean_sarray_cptr(signed_message),
    &signed_message_len,
    lean_sarray_cptr(message),
    (unsigned long long) msg_len,
    (uint8_t*) sk_ref);

  sodium_mprotect_noaccess(sk_ref);

  if (err != 0) {
    lean_dec(signed_message);
    lean_object* error_msg = lean_mk_string("crypto_sign failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  return lean_io_result_mk_ok(signed_message);

alloy c extern "lean_crypto_sign_open"
def signOpen {n : Nat}
    (signedMessage : @& ByteVector (BYTES + n))
    (publicKey : @& ByteVector PUBLICKEYBYTES)
    : Option (ByteVector n) :=
  size_t signed_msg_len = lean_sarray_size(signedMessage);
  size_t pk_len = lean_sarray_size(publicKey);

  if (
    pk_len != crypto_sign_PUBLICKEYBYTES ||
    signed_msg_len < crypto_sign_BYTES
  ) {
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return none;
  }

  size_t message_len = signed_msg_len - crypto_sign_BYTES;
  lean_object* message = lean_alloc_sarray(
    sizeof(uint8_t),
    message_len,
    message_len);

  unsigned long long message_len_out;
  int err = crypto_sign_open(
    lean_sarray_cptr(message),
    &message_len_out,
    lean_sarray_cptr(signedMessage),
    (unsigned long long) signed_msg_len,
    lean_sarray_cptr(publicKey));

  if (err != 0) {
    lean_dec(message);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return none;
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, message);
  return some;

alloy c extern "lean_crypto_sign_detached"
def signDetached {τ : @& Sodium σ} {n : Nat}
    (message : @& ByteVector n)
    (secretKey : @& SecretVector τ SECRETKEYBYTES)
    : IO (ByteVector BYTES) :=
  size_t sk_len = lean_ctor_get_usize(secretKey, 1);

  size_t msg_len = lean_sarray_size(message);

  if (sk_len != crypto_sign_SECRETKEYBYTES) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_sign_detached");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* signature = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_sign_BYTES,
    crypto_sign_BYTES);

  void* sk_ref = sodium_secure_of_lean(lean_ctor_get(secretKey, 0));
  sodium_mprotect_readonly(sk_ref);

  unsigned long long signature_len;
  int err = crypto_sign_detached(
    lean_sarray_cptr(signature),
    &signature_len,
    lean_sarray_cptr(message),
    (unsigned long long) msg_len,
    (uint8_t*) sk_ref);

  sodium_mprotect_noaccess(sk_ref);

  if (err != 0) {
    lean_dec(signature);
    lean_object* error_msg = lean_mk_string("crypto_sign_detached failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  return lean_io_result_mk_ok(signature);

alloy c extern "lean_crypto_sign_verify_detached"
def verifyDetached {n : Nat}
    (signature : @& ByteVector BYTES)
    (message : @& ByteVector n)
    (publicKey : @& ByteVector PUBLICKEYBYTES)
    : Bool :=
  size_t sig_len = lean_sarray_size(signature);
  size_t msg_len = lean_sarray_size(message);
  size_t pk_len = lean_sarray_size(publicKey);

  if (
    sig_len != crypto_sign_BYTES ||
    pk_len != crypto_sign_PUBLICKEYBYTES
  ) {
    return 0;
  }

  int err = crypto_sign_verify_detached(
    lean_sarray_cptr(signature),
    lean_sarray_cptr(message),
    (unsigned long long) msg_len,
    lean_sarray_cptr(publicKey));

  if (err == 0) {
    return 1;
  } else {
    return 0;
  }

-- Conversion functions from Ed25519 to Curve25519
alloy c extern "lean_crypto_sign_ed25519_pk_to_curve25519"
def ed25519PkToCurve25519
    (ed25519Pk : @& ByteVector PUBLICKEYBYTES)
    : IO (ByteVector 32) :=
  if (lean_sarray_size(ed25519Pk) != crypto_sign_PUBLICKEYBYTES) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_sign_ed25519_pk_to_curve25519");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* curve25519_pk = lean_alloc_sarray(
    sizeof(uint8_t),
    32,
    32);

  int err = crypto_sign_ed25519_pk_to_curve25519(
    lean_sarray_cptr(curve25519_pk),
    lean_sarray_cptr(ed25519Pk));

  if (err != 0) {
    lean_dec(curve25519_pk);
    lean_object* error_msg = lean_mk_string("crypto_sign_ed25519_pk_to_curve25519 failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  return lean_io_result_mk_ok(curve25519_pk);

alloy c extern "lean_crypto_sign_ed25519_sk_to_curve25519"
def ed25519SkToCurve25519 {τ : @& Sodium σ}
    (ed25519Sk : @& SecretVector τ SECRETKEYBYTES)
    : IO (SecretVector τ 32) :=
  size_t sk_len = lean_ctor_get_usize(ed25519Sk, 1);

  if (sk_len != crypto_sign_SECRETKEYBYTES) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_sign_ed25519_sk_to_curve25519");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* curve25519_sk_io = lean_sodium_malloc(τ, 32, _2);

  if (lean_io_result_is_error(curve25519_sk_io)) {
    return curve25519_sk_io;
  }

  lean_object* curve25519_sk = lean_io_result_take_value(curve25519_sk_io);
  void* curve25519_sk_ref = sodium_secure_of_lean(lean_ctor_get(curve25519_sk, 0));
  void* ed25519_sk_ref = sodium_secure_of_lean(lean_ctor_get(ed25519Sk, 0));

  sodium_mprotect_readwrite(curve25519_sk_ref);
  sodium_mprotect_readonly(ed25519_sk_ref);

  int err = crypto_sign_ed25519_sk_to_curve25519(
    (uint8_t*) curve25519_sk_ref,
    (uint8_t*) ed25519_sk_ref);

  sodium_mprotect_noaccess(curve25519_sk_ref);
  sodium_mprotect_noaccess(ed25519_sk_ref);

  if (err != 0) {
    sodium_munlock(curve25519_sk_ref, 32);
    lean_dec(curve25519_sk);
    lean_object* error_msg = lean_mk_string("crypto_sign_ed25519_sk_to_curve25519 failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  return lean_io_result_mk_ok(curve25519_sk);

end Sodium.FFI.Sign
