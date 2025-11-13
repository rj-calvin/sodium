import Sodium.FFI.Basic

universe u

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI.SecretBox

variable {n m : Nat} {σ : Type u}

alloy c section
extern lean_obj_res lean_sodium_malloc(b_lean_obj_arg, size_t, lean_obj_arg);
extern lean_obj_res sodium_secure_to_lean(void*);
extern void* sodium_secure_of_lean(b_lean_obj_arg);
end

-- Constants for crypto_secretbox
def KEYBYTES : Nat := 32
def NONCEBYTES : Nat := 24
def MACBYTES : Nat := 16

alloy c extern "lean_crypto_secretbox_keygen"
def keygen {τ : @& Sodium σ} : IO (SecretVector τ KEYBYTES) :=
  lean_object* secret_key_io = lean_sodium_malloc(τ, crypto_secretbox_KEYBYTES, _1);

  if (lean_io_result_is_error(secret_key_io)) {
    return secret_key_io;
  }

  lean_object* secret_key = lean_io_result_take_value(secret_key_io);
  void* secret_key_ref = sodium_secure_of_lean(lean_ctor_get(secret_key, 0));

  sodium_mprotect_readwrite(secret_key_ref);
  crypto_secretbox_keygen((uint8_t*) secret_key_ref);
  sodium_mprotect_noaccess(secret_key_ref);

  return lean_io_result_mk_ok(secret_key);

alloy c extern "lean_crypto_secretbox_easy"
def easy {τ : @& Sodium σ} (message : @& ByteVector n) (nonce : @& ByteVector NONCEBYTES)
    (secretKey : @& SecretVector τ KEYBYTES) : IO (ByteVector (MACBYTES + n)) :=
  size_t message_len = lean_sarray_size(message);
  size_t sk_len = lean_ctor_get_usize(secretKey, 1);

  if (
    lean_sarray_size(nonce) != crypto_secretbox_NONCEBYTES ||
    sk_len != crypto_secretbox_KEYBYTES ||
    message_len > crypto_secretbox_MESSAGEBYTES_MAX - crypto_secretbox_MACBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_secretbox_easy");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* ciphertext = lean_alloc_sarray(
    sizeof(uint8_t),
    message_len + crypto_secretbox_MACBYTES,
    message_len + crypto_secretbox_MACBYTES);

  void* secret_key = sodium_secure_of_lean(lean_ctor_get(secretKey, 0));
  sodium_mprotect_readonly(secret_key);

  int err = crypto_secretbox_easy(
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    (uint8_t*) secret_key);

  sodium_mprotect_noaccess(secret_key);

  if (err != 0) {
    lean_dec(ciphertext);
    lean_object* error_msg = lean_mk_string("crypto_secretbox_easy failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  return lean_io_result_mk_ok(ciphertext);

alloy c extern "lean_crypto_secretbox_open_easy"
def openEasy {τ : @& Sodium σ} (ciphertext : @& ByteVector (MACBYTES + n)) (nonce : @& ByteVector NONCEBYTES)
    (secretKey : @& SecretVector τ KEYBYTES) : IO (Option (ByteVector n)) :=
  size_t ciphertext_len = lean_sarray_size(ciphertext);
  size_t sk_len = lean_ctor_get_usize(secretKey, 1);

  if (
    lean_sarray_size(nonce) != crypto_secretbox_NONCEBYTES ||
    sk_len != crypto_secretbox_KEYBYTES ||
    ciphertext_len < crypto_secretbox_MACBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_secretbox_open_easy");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* message = lean_alloc_sarray(
    sizeof(uint8_t),
    ciphertext_len - crypto_secretbox_MACBYTES,
    ciphertext_len - crypto_secretbox_MACBYTES);

  void* secret_key = sodium_secure_of_lean(lean_ctor_get(secretKey, 0));
  sodium_mprotect_readonly(secret_key);

  int err = crypto_secretbox_open_easy(
    lean_sarray_cptr(message),
    lean_sarray_cptr(ciphertext), ciphertext_len,
    lean_sarray_cptr(nonce),
    (uint8_t*) secret_key);

  sodium_mprotect_noaccess(secret_key);

  if (err != 0) {
    lean_dec(message);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, message);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_secretbox_detached"
def detached {τ : @& Sodium σ} (message : @& ByteVector n) (nonce : @& ByteVector NONCEBYTES)
    (secretKey : @& SecretVector τ KEYBYTES) : IO (ByteVector n × ByteVector MACBYTES) :=
  size_t message_len = lean_sarray_size(message);
  size_t sk_len = lean_ctor_get_usize(secretKey, 1);

  if (
    lean_sarray_size(nonce) != crypto_secretbox_NONCEBYTES ||
    sk_len != crypto_secretbox_KEYBYTES ||
    message_len > crypto_secretbox_MESSAGEBYTES_MAX
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_secretbox_detached");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* ciphertext = lean_alloc_sarray(
    sizeof(uint8_t),
    message_len,
    message_len);
  lean_object* mac = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_secretbox_MACBYTES,
    crypto_secretbox_MACBYTES);

  void* secret_key = sodium_secure_of_lean(lean_ctor_get(secretKey, 0));
  sodium_mprotect_readonly(secret_key);

  int err = crypto_secretbox_detached(
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(mac),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    (uint8_t*) secret_key);

  sodium_mprotect_noaccess(secret_key);

  if (err != 0) {
    lean_dec(ciphertext);
    lean_dec(mac);
    lean_object* error_msg = lean_mk_string("crypto_secretbox_detached failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* ret = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(ret, 0, ciphertext);
  lean_ctor_set(ret, 1, mac);
  return lean_io_result_mk_ok(ret);

alloy c extern "lean_crypto_secretbox_open_detached"
def openDetached {τ : @& Sodium σ} (ciphertext : @& ByteVector n) (mac : @& ByteVector MACBYTES) (nonce : @& ByteVector NONCEBYTES)
    (secretKey : @& SecretVector τ KEYBYTES) : IO (Option (ByteVector n)) :=
  size_t ciphertext_len = lean_sarray_size(ciphertext);
  size_t sk_len = lean_ctor_get_usize(secretKey, 1);

  if (
    lean_sarray_size(nonce) != crypto_secretbox_NONCEBYTES ||
    lean_sarray_size(mac) != crypto_secretbox_MACBYTES ||
    sk_len != crypto_secretbox_KEYBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_secretbox_open_detached");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* message = lean_alloc_sarray(
    sizeof(uint8_t),
    ciphertext_len,
    ciphertext_len);

  void* secret_key = sodium_secure_of_lean(lean_ctor_get(secretKey, 0));
  sodium_mprotect_readonly(secret_key);

  int err = crypto_secretbox_open_detached(
    lean_sarray_cptr(message),
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(mac),
    ciphertext_len,
    lean_sarray_cptr(nonce),
    (uint8_t*) secret_key);

  sodium_mprotect_noaccess(secret_key);

  if (err != 0) {
    lean_dec(message);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, message);
  return lean_io_result_mk_ok(some);

end Sodium.FFI.SecretBox
