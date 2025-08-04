import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI

-- Constants for crypto_secretstream_xchacha20poly1305
def SECRETSTREAM_XCHACHA20POLY1305_KEYBYTES : USize := 32
def SECRETSTREAM_XCHACHA20POLY1305_HEADERBYTES : USize := 24
def SECRETSTREAM_XCHACHA20POLY1305_ABYTES : USize := 17
def SECRETSTREAM_XCHACHA20POLY1305_MESSAGEBYTES_MAX : USize := 0x3fffffec00

-- Tag constants for message types
def SECRETSTREAM_XCHACHA20POLY1305_TAG_MESSAGE : UInt8 := 0
def SECRETSTREAM_XCHACHA20POLY1305_TAG_PUSH : UInt8 := 1
def SECRETSTREAM_XCHACHA20POLY1305_TAG_REKEY : UInt8 := 2
def SECRETSTREAM_XCHACHA20POLY1305_TAG_FINAL : UInt8 := 3

alloy c extern "lean_crypto_secretstream_xchacha20poly1305_keygen"
def keygen : IO ByteArray :=
  lean_object* key = lean_alloc_sarray(
    sizeof(unsigned char),
    crypto_secretstream_xchacha20poly1305_KEYBYTES,
    crypto_secretstream_xchacha20poly1305_KEYBYTES)
  crypto_secretstream_xchacha20poly1305_keygen(lean_sarray_cptr(key))
  return lean_io_result_mk_ok(key)

alloy c opaque_extern_type PushState => crypto_secretstream_xchacha20poly1305_state where
  finalize(s) := free(s)

alloy c opaque_extern_type PullState => crypto_secretstream_xchacha20poly1305_state where
  finalize(s) := free(s)

alloy c extern "lean_crypto_secretstream_xchacha20poly1305_init_push"
-- Internal C FFI function
def initPush (key : ByteArray) : IO (PushState × ByteArray) :=
  size_t key_size = lean_sarray_size(key)
  size_t expected_size = crypto_secretstream_xchacha20poly1305_KEYBYTES
  if (key_size != expected_size) {
    lean_object* error_msg = lean_mk_string("Invalid key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  crypto_secretstream_xchacha20poly1305_state* state =
    (crypto_secretstream_xchacha20poly1305_state*)malloc(sizeof(crypto_secretstream_xchacha20poly1305_state))

  lean_object* header = lean_alloc_sarray(
    sizeof(unsigned char),
    crypto_secretstream_xchacha20poly1305_HEADERBYTES,
    crypto_secretstream_xchacha20poly1305_HEADERBYTES)

  int result = crypto_secretstream_xchacha20poly1305_init_push(
    state,
    lean_sarray_cptr(header),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    free(state)
    lean_dec(header)
    lean_object* error_msg = lean_mk_string("init_push failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(pair, 0, to_lean<PushState>(state))
  lean_ctor_set(pair, 1, header)

  return lean_io_result_mk_ok(pair)

alloy c extern "lean_crypto_secretstream_xchacha20poly1305_init_pull"
def initPull (key : ByteArray) (header : ByteArray) : IO PullState :=
  size_t key_size = lean_sarray_size(key)
  size_t expected_key_size = crypto_secretstream_xchacha20poly1305_KEYBYTES
  if (key_size != expected_key_size) {
    lean_object* error_msg = lean_mk_string("Invalid key size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t header_size = lean_sarray_size(header)
  size_t expected_header_size = crypto_secretstream_xchacha20poly1305_HEADERBYTES
  if (header_size != expected_header_size) {
    lean_object* error_msg = lean_mk_string("Invalid header size")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  crypto_secretstream_xchacha20poly1305_state* state =
    (crypto_secretstream_xchacha20poly1305_state*)malloc(sizeof(crypto_secretstream_xchacha20poly1305_state))

  int result = crypto_secretstream_xchacha20poly1305_init_pull(
    state,
    lean_sarray_cptr(header),
    lean_sarray_cptr(key)
  )

  if (result != 0) {
    free(state)
    lean_object* error_msg = lean_mk_string("init_pull failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(to_lean<PullState>(state))

alloy c extern "lean_crypto_secretstream_xchacha20poly1305_push"
def push (state : @& PushState) (message : ByteArray) (additionalData : Option ByteArray) (tag : UInt8) : IO ByteArray :=
  crypto_secretstream_xchacha20poly1305_state* st = of_lean<PushState>(state)

  size_t message_len = lean_sarray_size(message)

  if (message_len > crypto_secretstream_xchacha20poly1305_MESSAGEBYTES_MAX) {
    lean_object* error_msg = lean_mk_string("Message too large for secret stream")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t ciphertext_len = message_len + crypto_secretstream_xchacha20poly1305_ABYTES

  lean_object* ciphertext = lean_alloc_sarray(sizeof(unsigned char), ciphertext_len, ciphertext_len)
  unsigned long long ciphertext_len_actual;

  const unsigned char* ad_ptr = NULL;
  size_t ad_len = 0;

  if (lean_obj_tag(additionalData) == 1) {
    lean_object* ad_val = lean_ctor_get(additionalData, 0)
    ad_ptr = lean_sarray_cptr(ad_val)
    ad_len = lean_sarray_size(ad_val)
  }

  int result = crypto_secretstream_xchacha20poly1305_push(
    st,
    lean_sarray_cptr(ciphertext), &ciphertext_len_actual,
    lean_sarray_cptr(message), message_len,
    ad_ptr, ad_len,
    tag
  )

  if (result != 0) {
    lean_dec(ciphertext)
    lean_object* error_msg = lean_mk_string("push failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(ciphertext)

alloy c extern "lean_crypto_secretstream_xchacha20poly1305_pull"
def pull (state : @& PullState) (ciphertext : ByteArray) (additionalData : Option ByteArray) : IO (ByteArray × UInt8) :=
  crypto_secretstream_xchacha20poly1305_state* st = of_lean<PullState>(state)

  size_t ciphertext_len = lean_sarray_size(ciphertext)

  if (ciphertext_len < crypto_secretstream_xchacha20poly1305_ABYTES) {
    lean_object* error_msg = lean_mk_string("Ciphertext too short")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  size_t message_len = ciphertext_len - crypto_secretstream_xchacha20poly1305_ABYTES;
  lean_object* message = lean_alloc_sarray(sizeof(unsigned char), message_len, message_len);
  unsigned long long message_len_actual;
  unsigned char tag;

  const unsigned char* ad_ptr = NULL;
  size_t ad_len = 0;

  if (lean_obj_tag(additionalData) == 1) {
    lean_object* ad_val = lean_ctor_get(additionalData, 0)
    ad_ptr = lean_sarray_cptr(ad_val)
    ad_len = lean_sarray_size(ad_val)
  }

  int result = crypto_secretstream_xchacha20poly1305_pull(
    st,
    lean_sarray_cptr(message), &message_len_actual,
    &tag,
    lean_sarray_cptr(ciphertext), ciphertext_len,
    ad_ptr, ad_len
  )

  if (result != 0) {
    lean_dec(message)
    lean_object* error_msg = lean_mk_string("pull failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* pair = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(pair, 0, message)
  lean_ctor_set(pair, 1, lean_box(tag))

  return lean_io_result_mk_ok(pair)

alloy c extern "lean_crypto_secretstream_xchacha20poly1305_rekey"
def rekey (state : @& PushState) : IO Unit :=
  crypto_secretstream_xchacha20poly1305_state* st = of_lean<PushState>(state)
  crypto_secretstream_xchacha20poly1305_rekey(st)
  return lean_io_result_mk_ok(lean_box(0))

end Sodium.FFI
