import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI

-- Constants based on libsodium's crypto_generichash values
def GENERICHASH_BYTES : USize := 32
def GENERICHASH_BYTES_MIN : USize := 16
def GENERICHASH_BYTES_MAX : USize := 64
def GENERICHASH_KEYBYTES : USize := 32
def GENERICHASH_KEYBYTES_MIN : USize := 16
def GENERICHASH_KEYBYTES_MAX : USize := 64

alloy c extern "lean_crypto_generichash"
def genericHash (outlen : USize) (input : ByteArray) (key : Option ByteArray) : IO ByteArray :=
  lean_object* out = lean_alloc_sarray(sizeof(unsigned char), outlen, outlen)
  unsigned char* out_ptr = lean_sarray_cptr(out)

  const unsigned char* in_ptr = lean_sarray_cptr(input)
  unsigned long long in_len = lean_sarray_size(input)

  const unsigned char* key_ptr = NULL
  size_t key_len = 0

  if (lean_obj_tag(key) == 1) {
    lean_object* key_val = lean_ctor_get(key, 0)
    key_ptr = lean_sarray_cptr(key_val)
    key_len = lean_sarray_size(key_val)
  }

  int result = crypto_generichash(out_ptr, outlen, in_ptr, in_len, key_ptr, key_len)

  if (result != 0) {
    lean_dec(out)
    lean_object* error_msg = lean_mk_string("crypto_generichash failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(out)

alloy c opaque_extern_type State => crypto_generichash_state where
  finalize(s) := free(s)

alloy c extern "lean_crypto_generichash_init"
def init (keylen : USize) (outlen : USize) (key : Option ByteArray) : IO State :=
  crypto_generichash_state* state = (crypto_generichash_state*)malloc(sizeof(crypto_generichash_state))

  const unsigned char* key_ptr = NULL
  size_t key_len = 0

  if (lean_obj_tag(key) == 1) {
    lean_object* key_val = lean_ctor_get(key, 0)
    key_ptr = lean_sarray_cptr(key_val)
    key_len = lean_sarray_size(key_val)
  }

  int result = crypto_generichash_init(state, key_ptr, key_len, outlen)

  if (result != 0) {
    free(state)
    lean_object* error_msg = lean_mk_string("crypto_generichash_init failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(to_lean<State>(state))

alloy c extern "lean_crypto_generichash_update"
def update (state : @& State) (input : ByteArray) : IO Unit :=
  crypto_generichash_state* st = of_lean<State>(state)
  const unsigned char* in_ptr = lean_sarray_cptr(input)
  unsigned long long in_len = lean_sarray_size(input)

  int result = crypto_generichash_update(st, in_ptr, in_len)

  if (result != 0) {
    lean_object* error_msg = lean_mk_string("crypto_generichash_update failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(lean_box(0))

alloy c extern "lean_crypto_generichash_final"
def final (state : @& State) (outlen : USize) : IO ByteArray :=
  crypto_generichash_state* st = of_lean<State>(state)
  lean_object* out = lean_alloc_sarray(sizeof(unsigned char), outlen, outlen)
  unsigned char* out_ptr = lean_sarray_cptr(out)

  int result = crypto_generichash_final(st, out_ptr, outlen)

  if (result != 0) {
    lean_dec(out)
    lean_object* error_msg = lean_mk_string("crypto_generichash_final failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  return lean_io_result_mk_ok(out)

end Sodium.FFI
