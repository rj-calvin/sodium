import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI.SecretStream

variable {n m : Nat} {σ : Type}

alloy c section
extern lean_obj_res lean_sodium_malloc(b_lean_obj_arg, size_t, lean_obj_arg);
extern lean_obj_res sodium_secure_to_lean(void*);
extern void* sodium_secure_of_lean(b_lean_obj_arg);
end

-- Constants for crypto_secretstream_xchacha20poly1305
def KEYBYTES : Nat := 32
def HEADERBYTES : Nat := 24
def ABYTES : Nat := 16
def TAGBYTES : Nat := 1

inductive Tag
  | message
  | push
  | rekey
  | final
  deriving TypeName, BEq, DecidableEq, Inhabited

-- Message tags
@[match_pattern] def STREAM_TAG_MESSAGE : UInt8 := 0x00
@[match_pattern] def STREAM_TAG_PUSH : UInt8 := 0x01
@[match_pattern] def STREAM_TAG_REKEY : UInt8 := 0x02
@[match_pattern] def STREAM_TAG_FINAL : UInt8 := 0x03

-- Opaque extern type for stream state
private alloy c opaque_extern_type StreamState => crypto_secretstream_xchacha20poly1305_state where
  finalize(state) := sodium_free(state)

-- Workaround for cross-module access to StreamState
alloy c section
LEAN_EXPORT lean_obj_res stream_state_to_lean(crypto_secretstream_xchacha20poly1305_state* state) {
  return _alloy_to_l___private_Sodium_FFI_SecretStream_0__Sodium_FFI_SecretStream_StreamState(state);
}

LEAN_EXPORT crypto_secretstream_xchacha20poly1305_state* stream_state_of_lean(b_lean_obj_arg obj) {
  return _alloy_of_l___private_Sodium_FFI_SecretStream_0__Sodium_FFI_SecretStream_StreamState(obj);
}
end

structure SecretStream (_ : Sodium σ) where
  private mk ::
  private state : StreamState.nonemptyType.type

noncomputable instance {τ : Sodium σ} : Nonempty (SecretStream τ) :=
  ⟨{ state := Classical.choice StreamState.nonemptyType.property }⟩

noncomputable instance {τ : Sodium σ} : Inhabited (SecretStream τ) :=
  ⟨{ state := Classical.choice StreamState.nonemptyType.property }⟩

alloy c extern "lean_crypto_secretstream_xchacha20poly1305_keygen"
def keygen {τ : @& Sodium σ} : IO (SecretVector τ KEYBYTES) :=
  lean_object* secret_key_io = lean_sodium_malloc(τ, crypto_secretstream_xchacha20poly1305_KEYBYTES, _1);

  if (lean_io_result_is_error(secret_key_io)) {
    return secret_key_io;
  }

  lean_object* secret_key = lean_io_result_take_value(secret_key_io);
  void* secret_key_ref = sodium_secure_of_lean(lean_ctor_get(secret_key, 0));

  sodium_mprotect_readwrite(secret_key_ref);
  crypto_secretstream_xchacha20poly1305_keygen((uint8_t*) secret_key_ref);
  sodium_mprotect_noaccess(secret_key_ref);

  return lean_io_result_mk_ok(secret_key);

alloy c extern "lean_crypto_secretstream_xchacha20poly1305_init_push"
def streamInitPush {τ : @& Sodium σ} (key : @& SecretVector τ KEYBYTES)
    : IO (SecretStream τ × ByteVector HEADERBYTES) :=
  size_t key_len = lean_ctor_get_usize(key, 1);

  if (key_len != crypto_secretstream_xchacha20poly1305_KEYBYTES) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_secretstream_xchacha20poly1305_init_push");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  crypto_secretstream_xchacha20poly1305_state* state =
    (crypto_secretstream_xchacha20poly1305_state*)sodium_malloc(
      sizeof(crypto_secretstream_xchacha20poly1305_state));

  if (state == NULL) {
    lean_object* error_msg = lean_mk_string("Failed to allocate secure memory for stream state");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  sodium_mlock(state, sizeof(crypto_secretstream_xchacha20poly1305_state));

  lean_object* header = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_secretstream_xchacha20poly1305_HEADERBYTES,
    crypto_secretstream_xchacha20poly1305_HEADERBYTES);

  void* key_ptr = sodium_secure_of_lean(lean_ctor_get(key, 0));
  sodium_mprotect_readonly(key_ptr);

  int err = crypto_secretstream_xchacha20poly1305_init_push(
    state,
    lean_sarray_cptr(header),
    (uint8_t*) key_ptr);

  sodium_mprotect_noaccess(key_ptr);

  if (err != 0) {
    sodium_munlock(state, sizeof(crypto_secretstream_xchacha20poly1305_state));
    sodium_free(state);
    lean_dec(header);
    lean_object* error_msg = lean_mk_string("crypto_secretstream_xchacha20poly1305_init_push failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  sodium_mprotect_noaccess(state);

  lean_object* stream_state = to_lean<StreamState>(state);
  lean_object* stream = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(stream, 0, stream_state);

  lean_object* ret = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(ret, 0, stream);
  lean_ctor_set(ret, 1, header);
  return lean_io_result_mk_ok(ret);

alloy c extern "lean_crypto_secretstream_xchacha20poly1305_push"
def streamPush {τ : @& Sodium σ} (stream : @& SecretStream τ)
    (message : @& ByteVector n) (additionalData : @& ByteVector m) (tag : Tag)
    : IO (ByteVector (ABYTES + n)) :=
  crypto_secretstream_xchacha20poly1305_state* state =
    of_lean<StreamState>(lean_ctor_get(stream, 0));

  size_t message_len = lean_sarray_size(message);
  size_t ad_len = lean_sarray_size(additionalData);

  lean_object* ciphertext = lean_alloc_sarray(
    sizeof(uint8_t),
    message_len + crypto_secretstream_xchacha20poly1305_ABYTES,
    message_len + crypto_secretstream_xchacha20poly1305_ABYTES);

  sodium_mprotect_readwrite(state);

  unsigned long long ciphertext_len;
  int err = crypto_secretstream_xchacha20poly1305_push(
    state,
    lean_sarray_cptr(ciphertext), &ciphertext_len,
    lean_sarray_cptr(message), message_len,
    ad_len > 0 ? lean_sarray_cptr(additionalData) : NULL, ad_len,
    tag);

  sodium_mprotect_noaccess(state);

  if (err != 0) {
    lean_dec(ciphertext);
    lean_object* error_msg = lean_mk_string("crypto_secretstream_xchacha20poly1305_push failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  return lean_io_result_mk_ok(ciphertext);

alloy c extern "lean_crypto_secretstream_xchacha20poly1305_init_pull"
def streamInitPull {τ : @& Sodium σ}
    (header : @& ByteVector HEADERBYTES) (key : @& SecretVector τ KEYBYTES)
    : IO (SecretStream τ) :=
  size_t key_len = lean_ctor_get_usize(key, 1);
  size_t header_len = lean_sarray_size(header);

  if (key_len != crypto_secretstream_xchacha20poly1305_KEYBYTES ||
      header_len != crypto_secretstream_xchacha20poly1305_HEADERBYTES) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_secretstream_xchacha20poly1305_init_pull");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  crypto_secretstream_xchacha20poly1305_state* state =
    (crypto_secretstream_xchacha20poly1305_state*)sodium_malloc(
      sizeof(crypto_secretstream_xchacha20poly1305_state));

  if (state == NULL) {
    lean_object* error_msg = lean_mk_string("Failed to allocate secure memory for stream state");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  sodium_mlock(state, sizeof(crypto_secretstream_xchacha20poly1305_state));

  void* key_ptr = sodium_secure_of_lean(lean_ctor_get(key, 0));
  sodium_mprotect_readonly(key_ptr);

  int err = crypto_secretstream_xchacha20poly1305_init_pull(
    state,
    lean_sarray_cptr(header),
    (uint8_t*) key_ptr);

  sodium_mprotect_noaccess(key_ptr);

  if (err != 0) {
    sodium_munlock(state, sizeof(crypto_secretstream_xchacha20poly1305_state));
    sodium_free(state);
    lean_object* error_msg = lean_mk_string("crypto_secretstream_xchacha20poly1305_init_pull failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  sodium_mprotect_noaccess(state);

  lean_object* stream_state = to_lean<StreamState>(state);
  lean_object* stream = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(stream, 0, stream_state);

  return lean_io_result_mk_ok(stream);

alloy c extern "lean_crypto_secretstream_xchacha20poly1305_pull"
def streamPull {τ : @& Sodium σ} (stream : @& SecretStream τ)
    (ciphertext : @& ByteVector (ABYTES + n)) (additionalData : @& ByteVector m)
    : IO (Option (ByteVector n × Tag)) :=
  crypto_secretstream_xchacha20poly1305_state* state =
    of_lean<StreamState>(lean_ctor_get(stream, 0));

  size_t ciphertext_len = lean_sarray_size(ciphertext);
  size_t ad_len = lean_sarray_size(additionalData);

  if (ciphertext_len < crypto_secretstream_xchacha20poly1305_ABYTES) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_secretstream_xchacha20poly1305_pull");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* message = lean_alloc_sarray(
    sizeof(uint8_t),
    ciphertext_len - crypto_secretstream_xchacha20poly1305_ABYTES,
    ciphertext_len - crypto_secretstream_xchacha20poly1305_ABYTES);

  sodium_mprotect_readwrite(state);

  unsigned char tag;
  int err = crypto_secretstream_xchacha20poly1305_pull(
    state,
    lean_sarray_cptr(message), NULL, &tag,
    lean_sarray_cptr(ciphertext), ciphertext_len,
    ad_len > 0 ? lean_sarray_cptr(additionalData) : NULL, ad_len);

  sodium_mprotect_noaccess(state);

  if (err != 0) {
    lean_dec(message);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, message);
  lean_ctor_set(pair, 1, lean_box(tag));
  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, pair);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_secretstream_xchacha20poly1305_rekey"
def streamRekey {τ : @& Sodium σ} (stream : @& SecretStream τ) : BaseIO Unit :=
  crypto_secretstream_xchacha20poly1305_state* state =
    of_lean<StreamState>(lean_ctor_get(stream, 0));

  sodium_mprotect_readwrite(state);
  crypto_secretstream_xchacha20poly1305_rekey(state);
  sodium_mprotect_noaccess(state);

  return lean_io_result_mk_ok(lean_box(0));

end Sodium.FFI.SecretStream
