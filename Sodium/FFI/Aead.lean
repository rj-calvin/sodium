import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI.Aead

variable {n m : Nat} {σ : Type}

alloy c section
extern lean_obj_res lean_sodium_malloc(b_lean_obj_arg, size_t, lean_obj_arg);
extern lean_obj_res sodium_secure_to_lean(void*);
extern void* sodium_secure_of_lean(b_lean_obj_arg);
end

-- Constants for crypto_aead_xchacha20poly1305_ietf
def KEYBYTES : Nat := 32
def NONCEBYTES : Nat := 24
def ABYTES : Nat := 16

alloy c extern "lean_crypto_aead_xchacha20poly1305_ietf_keygen"
def keygen {τ : @& Sodium σ} : IO (SecureVector τ KEYBYTES) :=
  lean_object* secret_key_io = lean_sodium_malloc(τ, crypto_aead_xchacha20poly1305_ietf_KEYBYTES, _1);

  if (lean_io_result_is_error(secret_key_io)) {
    return secret_key_io;
  }

  lean_object* secret_key = lean_io_result_take_value(secret_key_io);
  void* secret_key_ref = sodium_secure_of_lean(lean_ctor_get(secret_key, 0));

  sodium_mprotect_readwrite(secret_key_ref);
  crypto_aead_xchacha20poly1305_ietf_keygen((uint8_t*) secret_key_ref);
  sodium_mprotect_noaccess(secret_key_ref);

  return lean_io_result_mk_ok(secret_key);

alloy c extern "lean_crypto_aead_xchacha20poly1305_ietf_encrypt"
def encrypt {τ : @& Sodium σ} (message : @& ByteVector n) (additionalData : @& ByteVector m)
    (nonce : @& ByteVector NONCEBYTES) (key : @& SecureVector τ KEYBYTES)
    : IO (ByteVector (ABYTES + n)) :=
  size_t message_len = lean_sarray_size(message);
  size_t ad_len = lean_sarray_size(additionalData);
  size_t key_len = lean_ctor_get_usize(key, 1);

  if (
    lean_sarray_size(nonce) != crypto_aead_xchacha20poly1305_ietf_NPUBBYTES ||
    key_len != crypto_aead_xchacha20poly1305_ietf_KEYBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_aead_xchacha20poly1305_ietf_encrypt");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* ciphertext = lean_alloc_sarray(
    sizeof(uint8_t),
    message_len + crypto_aead_xchacha20poly1305_ietf_ABYTES,
    message_len + crypto_aead_xchacha20poly1305_ietf_ABYTES);

  void* key_ptr = sodium_secure_of_lean(lean_ctor_get(key, 0));
  sodium_mprotect_readonly(key_ptr);

  unsigned long long ciphertext_len;
  int err = crypto_aead_xchacha20poly1305_ietf_encrypt(
    lean_sarray_cptr(ciphertext), &ciphertext_len,
    lean_sarray_cptr(message), message_len,
    ad_len > 0 ? lean_sarray_cptr(additionalData) : NULL, ad_len,
    NULL,
    lean_sarray_cptr(nonce),
    (uint8_t*) key_ptr);

  sodium_mprotect_noaccess(key_ptr);

  if (err != 0) {
    lean_dec(ciphertext);
    lean_object* error_msg = lean_mk_string("crypto_aead_xchacha20poly1305_ietf_encrypt failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  return lean_io_result_mk_ok(ciphertext);

alloy c extern "lean_crypto_aead_xchacha20poly1305_ietf_decrypt"
def decrypt {τ : @& Sodium σ} (ciphertext : @& ByteVector (ABYTES + n))
    (additionalData : @& ByteVector m) (nonce : @& ByteVector NONCEBYTES)
    (key : @& SecureVector τ KEYBYTES) : IO (Option (ByteVector n)) :=
  size_t ciphertext_len = lean_sarray_size(ciphertext);
  size_t ad_len = lean_sarray_size(additionalData);
  size_t key_len = lean_ctor_get_usize(key, 1);

  if (
    lean_sarray_size(nonce) != crypto_aead_xchacha20poly1305_ietf_NPUBBYTES ||
    key_len != crypto_aead_xchacha20poly1305_ietf_KEYBYTES ||
    ciphertext_len < crypto_aead_xchacha20poly1305_ietf_ABYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_aead_xchacha20poly1305_ietf_decrypt");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* message = lean_alloc_sarray(
    sizeof(uint8_t),
    ciphertext_len - crypto_aead_xchacha20poly1305_ietf_ABYTES,
    ciphertext_len - crypto_aead_xchacha20poly1305_ietf_ABYTES);

  void* key_ptr = sodium_secure_of_lean(lean_ctor_get(key, 0));
  sodium_mprotect_readonly(key_ptr);

  unsigned long long message_len;
  int err = crypto_aead_xchacha20poly1305_ietf_decrypt(
    lean_sarray_cptr(message), &message_len,
    NULL,
    lean_sarray_cptr(ciphertext), ciphertext_len,
    ad_len > 0 ? lean_sarray_cptr(additionalData) : NULL, ad_len,
    lean_sarray_cptr(nonce),
    (uint8_t*) key_ptr);

  sodium_mprotect_noaccess(key_ptr);

  if (err != 0) {
    lean_dec(message);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, message);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_aead_xchacha20poly1305_ietf_encrypt_detached"
def encryptDetached {τ : @& Sodium σ} (message : @& ByteVector n) (additionalData : @& ByteVector m)
    (nonce : @& ByteVector NONCEBYTES) (key : @& SecureVector τ KEYBYTES)
    : IO (ByteVector n × ByteVector ABYTES) :=
  size_t message_len = lean_sarray_size(message);
  size_t ad_len = lean_sarray_size(additionalData);
  size_t key_len = lean_ctor_get_usize(key, 1);

  if (
    lean_sarray_size(nonce) != crypto_aead_xchacha20poly1305_ietf_NPUBBYTES ||
    key_len != crypto_aead_xchacha20poly1305_ietf_KEYBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_aead_xchacha20poly1305_ietf_encrypt_detached");
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
    crypto_aead_xchacha20poly1305_ietf_ABYTES,
    crypto_aead_xchacha20poly1305_ietf_ABYTES);

  void* key_ptr = sodium_secure_of_lean(lean_ctor_get(key, 0));
  sodium_mprotect_readonly(key_ptr);

  unsigned long long mac_len;
  int err = crypto_aead_xchacha20poly1305_ietf_encrypt_detached(
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(mac), &mac_len,
    lean_sarray_cptr(message), message_len,
    ad_len > 0 ? lean_sarray_cptr(additionalData) : NULL, ad_len,
    NULL,
    lean_sarray_cptr(nonce),
    (uint8_t*) key_ptr);

  sodium_mprotect_noaccess(key_ptr);

  if (err != 0) {
    lean_dec(ciphertext);
    lean_dec(mac);
    lean_object* error_msg = lean_mk_string("crypto_aead_xchacha20poly1305_ietf_encrypt_detached failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* ret = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(ret, 0, ciphertext);
  lean_ctor_set(ret, 1, mac);
  return lean_io_result_mk_ok(ret);

alloy c extern "lean_crypto_aead_xchacha20poly1305_ietf_decrypt_detached"
def decryptDetached {τ : @& Sodium σ} (ciphertext : @& ByteVector n) (mac : @& ByteVector ABYTES)
    (additionalData : @& ByteVector m) (nonce : @& ByteVector NONCEBYTES)
    (key : @& SecureVector τ KEYBYTES) : IO (Option (ByteVector n)) :=
  size_t ciphertext_len = lean_sarray_size(ciphertext);
  size_t ad_len = lean_sarray_size(additionalData);
  size_t key_len = lean_ctor_get_usize(key, 1);

  if (
    lean_sarray_size(nonce) != crypto_aead_xchacha20poly1305_ietf_NPUBBYTES ||
    lean_sarray_size(mac) != crypto_aead_xchacha20poly1305_ietf_ABYTES ||
    key_len != crypto_aead_xchacha20poly1305_ietf_KEYBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_aead_xchacha20poly1305_ietf_decrypt_detached");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* message = lean_alloc_sarray(
    sizeof(uint8_t),
    ciphertext_len,
    ciphertext_len);

  void* key_ptr = sodium_secure_of_lean(lean_ctor_get(key, 0));
  sodium_mprotect_readonly(key_ptr);

  int err = crypto_aead_xchacha20poly1305_ietf_decrypt_detached(
    lean_sarray_cptr(message),
    NULL,
    lean_sarray_cptr(ciphertext), ciphertext_len,
    lean_sarray_cptr(mac),
    ad_len > 0 ? lean_sarray_cptr(additionalData) : NULL, ad_len,
    lean_sarray_cptr(nonce),
    (uint8_t*) key_ptr);

  sodium_mprotect_noaccess(key_ptr);

  if (err != 0) {
    lean_dec(message);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, message);
  return lean_io_result_mk_ok(some);

end Sodium.FFI.Aead