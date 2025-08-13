import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI.Box

variable {n m : Nat} {σ : Type}

alloy c section
extern lean_obj_res lean_sodium_malloc(b_lean_obj_arg, size_t, lean_obj_arg);
extern lean_obj_res sodium_secure_to_lean(void*);
extern void* sodium_secure_of_lean(b_lean_obj_arg);
end

-- Constants for crypto_box
def PUBLICKEYBYTES : Nat := 32
def SECRETKEYBYTES : Nat := 32
def NONCEBYTES : Nat := 24
def MACBYTES : Nat := 16
def SEEDBYTES : Nat := 32
def BEFORENMBYTES : Nat := 32
def SEALBYTES : Nat := 48  -- PUBLICKEYBYTES + MACBYTES

abbrev SHAREDBYTES : Nat := BEFORENMBYTES

alloy c extern "lean_crypto_box_keypair"
def keypair {τ : @& Sodium σ} : IO (ByteVector PUBLICKEYBYTES × SecureVector τ SECRETKEYBYTES) :=
  lean_object* public_key = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_box_PUBLICKEYBYTES,
    crypto_box_PUBLICKEYBYTES)

  lean_object* secret_key_io = lean_sodium_malloc(τ, crypto_box_SECRETKEYBYTES, _1);

  if (lean_io_result_is_error(secret_key_io)) {
    return secret_key_io;
  }

  lean_object* secret_key = lean_io_result_take_value(secret_key_io);
  void* secret_key_ref = sodium_secure_of_lean(lean_ctor_get(secret_key, 0));
  sodium_mprotect_readwrite(secret_key_ref);

  int err = crypto_box_keypair(lean_sarray_cptr(public_key), (uint8_t*) secret_key_ref);

  if (err != 0) {
    sodium_munlock(secret_key_ref, crypto_box_SECRETKEYBYTES);
    lean_dec(public_key);
    lean_dec(secret_key);
    lean_object* error_msg = lean_mk_string("crypto_box_keypair failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  sodium_mprotect_noaccess(secret_key_ref);

  lean_object* ret = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(ret, 0, public_key);
  lean_ctor_set(ret, 1, secret_key);

  return lean_io_result_mk_ok(ret);

alloy c extern "lean_crypto_box_seed_keypair"
def seedKeypair {τ : @& Sodium σ} (seed : @& SecureVector τ SEEDBYTES) : IO (ByteVector PUBLICKEYBYTES × SecureVector τ SECRETKEYBYTES) :=
  size_t seed_len = lean_ctor_get_usize(seed, 1);

  if (seed_len != crypto_box_SEEDBYTES) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_box_seed_keypair");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* public_key = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_box_PUBLICKEYBYTES,
    crypto_box_PUBLICKEYBYTES);

  lean_object* secret_key_io = lean_sodium_malloc(τ, crypto_box_SECRETKEYBYTES, _2);

  if (lean_io_result_is_error(secret_key_io)) {
    lean_dec(public_key);
    return secret_key_io;
  }

  lean_object* secret_key = lean_io_result_take_value(secret_key_io);
  void* secret_key_ref = sodium_secure_of_lean(lean_ctor_get(secret_key, 0));
  void* seed_ref = sodium_secure_of_lean(lean_ctor_get(seed, 0));

  sodium_mprotect_readwrite(secret_key_ref);
  sodium_mprotect_readonly(seed_ref);

  int err = crypto_box_seed_keypair(
    lean_sarray_cptr(public_key),
    (uint8_t*) secret_key_ref,
    (uint8_t*) seed_ref);

  sodium_mprotect_noaccess(secret_key_ref);
  sodium_mprotect_noaccess(seed_ref);

  if (err != 0) {
    sodium_munlock(secret_key_ref, crypto_box_SECRETKEYBYTES);
    lean_dec(public_key);
    lean_dec(secret_key);
    lean_object* error_msg = lean_mk_string("crypto_box_seed_keypair failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* ret = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(ret, 0, public_key);
  lean_ctor_set(ret, 1, secret_key);
  return lean_io_result_mk_ok(ret);

alloy c extern "lean_crypto_box_easy"
def easy {τ : @& Sodium σ} (message : @& ByteVector n) (nonce : @& ByteVector NONCEBYTES)
    (publicKey : @& ByteVector PUBLICKEYBYTES) (secretKey : @& SecureVector τ SECRETKEYBYTES)
    : IO (Option (ByteVector (MACBYTES + n))) :=
  size_t message_len = lean_sarray_size(message);
  size_t sk_len = lean_ctor_get_usize(secretKey, 1);

  if (
    lean_sarray_size(nonce) != crypto_box_NONCEBYTES ||
    lean_sarray_size(publicKey) != crypto_box_PUBLICKEYBYTES ||
    sk_len != crypto_box_SECRETKEYBYTES ||
    message_len > crypto_box_MESSAGEBYTES_MAX - crypto_box_MACBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_box_easy");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* ciphertext = lean_alloc_sarray(
    sizeof(uint8_t),
    message_len + crypto_box_MACBYTES,
    message_len + crypto_box_MACBYTES);

  void* secret_key = sodium_secure_of_lean(lean_ctor_get(secretKey, 0));
  sodium_mprotect_readonly(secret_key);

  int err = crypto_box_easy(
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(publicKey),
    (uint8_t*) secret_key);

  sodium_mprotect_noaccess(secret_key);

  if (err != 0) {
    lean_dec(ciphertext);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, ciphertext);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_box_open_easy"
def openEasy {τ : @& Sodium σ} (cipher : @& ByteVector (MACBYTES + n)) (nonce : @& ByteVector NONCEBYTES)
    (publicKey : @& ByteVector PUBLICKEYBYTES) (secretKey : @& SecureVector τ SECRETKEYBYTES)
    : IO (Option (ByteVector n)) :=
  size_t ciphertext_len = lean_sarray_size(cipher);
  size_t sk_len = lean_ctor_get_usize(secretKey, 1);

  if (
    lean_sarray_size(nonce) != crypto_box_NONCEBYTES ||
    lean_sarray_size(publicKey) != crypto_box_PUBLICKEYBYTES ||
    sk_len != crypto_box_SECRETKEYBYTES ||
    ciphertext_len < crypto_box_MACBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_box_open_easy");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* message = lean_alloc_sarray(
    sizeof(uint8_t),
    ciphertext_len - crypto_box_MACBYTES,
    ciphertext_len - crypto_box_MACBYTES);

  void* secret_key = sodium_secure_of_lean(lean_ctor_get(secretKey, 0));
  sodium_mprotect_readonly(secret_key);

  int err = crypto_box_open_easy(
    lean_sarray_cptr(message),
    lean_sarray_cptr(cipher), ciphertext_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(publicKey),
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

alloy c extern "lean_crypto_box_beforenm"
def beforenm {τ : @& Sodium σ}
    (publicKey : @& ByteVector PUBLICKEYBYTES)
    (secretKey : @& SecureVector τ SECRETKEYBYTES)
    : IO (Option (SecureVector τ SHAREDBYTES)) :=
  size_t sk_len = lean_ctor_get_usize(secretKey, 1);

  if (
    lean_sarray_size(publicKey) != crypto_box_PUBLICKEYBYTES ||
    sk_len != crypto_box_SECRETKEYBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_box_beforenm");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* shared_secret_io = lean_sodium_malloc(τ, crypto_box_BEFORENMBYTES, _3);

  if (lean_io_result_is_error(shared_secret_io)) {
    return shared_secret_io;
  }

  lean_object* shared_secret = lean_io_result_take_value(shared_secret_io);
  void* shared_secret_ref = sodium_secure_of_lean(lean_ctor_get(shared_secret, 0));
  void* secret_key_ref = sodium_secure_of_lean(lean_ctor_get(secretKey, 0));

  sodium_mprotect_readwrite(shared_secret_ref);
  sodium_mprotect_readonly(secret_key_ref);

  int err = crypto_box_beforenm(
    (uint8_t*) shared_secret_ref,
    lean_sarray_cptr(publicKey),
    (uint8_t*) secret_key_ref);

  sodium_mprotect_noaccess(shared_secret_ref);
  sodium_mprotect_noaccess(secret_key_ref);

  if (err != 0) {
    sodium_munlock(shared_secret_ref, crypto_box_BEFORENMBYTES);
    lean_dec(shared_secret);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, shared_secret);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_box_easy_afternm"
def easyAfternm {τ : @& Sodium σ}
    (message : @& ByteVector n)
    (nonce : @& ByteVector NONCEBYTES)
    (sharedSecret : @& SecureVector τ SHAREDBYTES)
    : IO (ByteVector (MACBYTES + n)) :=
  size_t message_len = lean_sarray_size(message);
  size_t shared_len = lean_ctor_get_usize(sharedSecret, 1);

  if (
    lean_sarray_size(nonce) != crypto_box_NONCEBYTES ||
    shared_len != crypto_box_BEFORENMBYTES ||
    message_len > crypto_box_MESSAGEBYTES_MAX - crypto_box_MACBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_box_easy_afternm");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* ciphertext = lean_alloc_sarray(
    sizeof(uint8_t),
    message_len + crypto_box_MACBYTES,
    message_len + crypto_box_MACBYTES);

  void* shared_secret = sodium_secure_of_lean(lean_ctor_get(sharedSecret, 0));
  sodium_mprotect_readonly(shared_secret);

  int err = crypto_box_easy_afternm(
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    (uint8_t*) shared_secret);

  sodium_mprotect_noaccess(shared_secret);

  if (err != 0) {
    lean_dec(ciphertext);
    lean_object* error_msg = lean_mk_string("crypto_box_easy_afternm failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  return lean_io_result_mk_ok(ciphertext);

alloy c extern "lean_crypto_box_open_easy_afternm"
def openEasyAfternm {τ : @& Sodium σ}
    (ciphertext : @& ByteVector (MACBYTES + n))
    (nonce : @& ByteVector NONCEBYTES)
    (sharedSecret : @& SecureVector τ SHAREDBYTES)
    : IO (Option (ByteVector n)) :=
  size_t ciphertext_len = lean_sarray_size(ciphertext);
  size_t shared_len = lean_ctor_get_usize(sharedSecret, 1);

  if (
    lean_sarray_size(nonce) != crypto_box_NONCEBYTES ||
    shared_len != crypto_box_BEFORENMBYTES ||
    ciphertext_len < crypto_box_MACBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_box_open_easy_afternm");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* message = lean_alloc_sarray(
    sizeof(uint8_t),
    ciphertext_len - crypto_box_MACBYTES,
    ciphertext_len - crypto_box_MACBYTES);

  void* shared_secret = sodium_secure_of_lean(lean_ctor_get(sharedSecret, 0));
  sodium_mprotect_readonly(shared_secret);

  int err = crypto_box_open_easy_afternm(
    lean_sarray_cptr(message),
    lean_sarray_cptr(ciphertext), ciphertext_len,
    lean_sarray_cptr(nonce),
    (uint8_t*) shared_secret);

  sodium_mprotect_noaccess(shared_secret);

  if (err != 0) {
    lean_dec(message);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, message);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_box_detached_afternm"
def detachedAfternm {τ : @& Sodium σ}
    (message : @& ByteVector n)
    (nonce : @& ByteVector NONCEBYTES)
    (sharedSecret : @& SecureVector τ SHAREDBYTES)
    : IO (ByteVector n × ByteVector MACBYTES) :=
  size_t message_len = lean_sarray_size(message);
  size_t shared_len = lean_ctor_get_usize(sharedSecret, 1);

  if (
    lean_sarray_size(nonce) != crypto_box_NONCEBYTES ||
    shared_len != crypto_box_BEFORENMBYTES ||
    message_len > crypto_box_MESSAGEBYTES_MAX
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_box_detached_afternm");
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
    crypto_box_MACBYTES,
    crypto_box_MACBYTES);

  void* shared_secret = sodium_secure_of_lean(lean_ctor_get(sharedSecret, 0));
  sodium_mprotect_readonly(shared_secret);

  int err = crypto_box_detached_afternm(
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(mac),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    (uint8_t*) shared_secret);

  sodium_mprotect_noaccess(shared_secret);

  if (err != 0) {
    lean_dec(ciphertext);
    lean_dec(mac);
    lean_object* error_msg = lean_mk_string("crypto_box_detached_afternm failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* ret = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(ret, 0, ciphertext);
  lean_ctor_set(ret, 1, mac);
  return lean_io_result_mk_ok(ret);

alloy c extern "lean_crypto_box_open_detached_afternm"
def openDetachedAfternm {τ : @& Sodium σ}
    (ciphertext : @& ByteVector n)
    (mac : @& ByteVector MACBYTES)
    (nonce : @& ByteVector NONCEBYTES)
    (sharedSecret : @& SecureVector τ SHAREDBYTES)
    : IO (Option (ByteVector n)) :=
  size_t ciphertext_len = lean_sarray_size(ciphertext);
  size_t shared_len = lean_ctor_get_usize(sharedSecret, 1);

  if (
    lean_sarray_size(nonce) != crypto_box_NONCEBYTES ||
    lean_sarray_size(mac) != crypto_box_MACBYTES ||
    shared_len != crypto_box_BEFORENMBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_box_open_detached_afternm");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* message = lean_alloc_sarray(
    sizeof(uint8_t),
    ciphertext_len,
    ciphertext_len);

  void* shared_secret = sodium_secure_of_lean(lean_ctor_get(sharedSecret, 0));
  sodium_mprotect_readonly(shared_secret);

  int err = crypto_box_open_detached_afternm(
    lean_sarray_cptr(message),
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(mac),
    ciphertext_len,
    lean_sarray_cptr(nonce),
    (uint8_t*) shared_secret);

  sodium_mprotect_noaccess(shared_secret);

  if (err != 0) {
    lean_dec(message);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, message);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_box_detached"
def detached {τ : @& Sodium σ}
    (message : @& ByteVector n)
    (nonce : @& ByteVector NONCEBYTES)
    (publicKey : @& ByteVector PUBLICKEYBYTES)
    (secretKey : @& SecureVector τ SECRETKEYBYTES)
    : IO (Option (ByteVector n × ByteVector MACBYTES)) :=
  size_t message_len = lean_sarray_size(message);
  size_t sk_len = lean_ctor_get_usize(secretKey, 1);

  if (
    lean_sarray_size(nonce) != crypto_box_NONCEBYTES ||
    lean_sarray_size(publicKey) != crypto_box_PUBLICKEYBYTES ||
    sk_len != crypto_box_SECRETKEYBYTES ||
    message_len > crypto_box_MESSAGEBYTES_MAX
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_box_detached");
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
    crypto_box_MACBYTES,
    crypto_box_MACBYTES);

  void* secret_key = sodium_secure_of_lean(lean_ctor_get(secretKey, 0));
  sodium_mprotect_readonly(secret_key);

  int err = crypto_box_detached(
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(mac),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(publicKey),
    (uint8_t*) secret_key);

  sodium_mprotect_noaccess(secret_key);

  if (err != 0) {
    lean_dec(ciphertext);
    lean_dec(mac);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* ret = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(ret, 0, ciphertext);
  lean_ctor_set(ret, 1, mac);
  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, ret);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_box_open_detached"
def openDetached {τ : @& Sodium σ}
    (ciphertext : @& ByteVector n)
    (mac : @& ByteVector MACBYTES)
    (nonce : @& ByteVector NONCEBYTES)
    (publicKey : @& ByteVector PUBLICKEYBYTES)
    (secretKey : @& SecureVector τ SECRETKEYBYTES)
    : IO (Option (ByteVector n)) :=
  size_t ciphertext_len = lean_sarray_size(ciphertext);
  size_t sk_len = lean_ctor_get_usize(secretKey, 1);

  if (
    lean_sarray_size(nonce) != crypto_box_NONCEBYTES ||
    lean_sarray_size(publicKey) != crypto_box_PUBLICKEYBYTES ||
    lean_sarray_size(mac) != crypto_box_MACBYTES ||
    sk_len != crypto_box_SECRETKEYBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_box_open_detached");
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

  int err = crypto_box_open_detached(
    lean_sarray_cptr(message),
    lean_sarray_cptr(ciphertext),
    lean_sarray_cptr(mac),
    ciphertext_len,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(publicKey),
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

alloy c extern "lean_crypto_box_seal"
def easyAnonymous {τ : @& Sodium σ}
    (message : @& ByteVector n)
    (publicKey : @& ByteVector PUBLICKEYBYTES)
    : IO (Option (ByteVector (SEALBYTES + n))) :=
  size_t message_len = lean_sarray_size(message);

  if (
    lean_sarray_size(publicKey) != crypto_box_PUBLICKEYBYTES ||
    message_len > crypto_box_MESSAGEBYTES_MAX - crypto_box_SEALBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_box_seal");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* sealed = lean_alloc_sarray(
    sizeof(uint8_t),
    message_len + crypto_box_SEALBYTES,
    message_len + crypto_box_SEALBYTES);

  int err = crypto_box_seal(
    lean_sarray_cptr(sealed),
    lean_sarray_cptr(message), message_len,
    lean_sarray_cptr(publicKey));

  if (err != 0) {
    lean_dec(sealed);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, sealed);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_box_seal_open"
def openAnonymous {τ : @& Sodium σ}
    (sealed : @& ByteVector (SEALBYTES + n))
    (publicKey : @& ByteVector PUBLICKEYBYTES)
    (secretKey : @& SecureVector τ SECRETKEYBYTES)
    : IO (Option (ByteVector n)) :=
  size_t sealed_len = lean_sarray_size(sealed);
  size_t sk_len = lean_ctor_get_usize(secretKey, 1);

  if (
    lean_sarray_size(publicKey) != crypto_box_PUBLICKEYBYTES ||
    sk_len != crypto_box_SECRETKEYBYTES ||
    sealed_len < crypto_box_SEALBYTES
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_box_seal_open");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* message = lean_alloc_sarray(
    sizeof(uint8_t),
    sealed_len - crypto_box_SEALBYTES,
    sealed_len - crypto_box_SEALBYTES);

  void* secret_key = sodium_secure_of_lean(lean_ctor_get(secretKey, 0));
  sodium_mprotect_readonly(secret_key);

  int err = crypto_box_seal_open(
    lean_sarray_cptr(message),
    lean_sarray_cptr(sealed), sealed_len,
    lean_sarray_cptr(publicKey),
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

end Sodium.FFI.Box
