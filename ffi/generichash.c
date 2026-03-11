#include "ffi.h"

LEAN_EXPORT lean_obj_res lean_sodium_generichash(b_lean_obj_arg input, b_lean_obj_arg key) {
  lean_object* data;
  uint8_t* ptr = NULL;
  size_t len = 0;

  if (!lean_is_scalar(key)) {
    data = lean_ctor_get(key, 0);
    ptr = lean_sarray_cptr(data);
    len = lean_sarray_size(data);
  }

  lean_object* ret = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_generichash_BYTES_MAX,
    crypto_generichash_BYTES_MAX);

  crypto_generichash(
    lean_sarray_cptr(ret),
    lean_sarray_size(ret),
    lean_sarray_cptr(input),
    lean_sarray_size(input),
    ptr,
    len);

  return ret;
}

LEAN_EXPORT lean_obj_res lean_sodium_generichash_init(b_lean_obj_arg key) {
  lean_object* data;
  uint8_t* ptr = NULL;
  size_t len = 0;

  if (!lean_is_scalar(key)) {
    data = lean_ctor_get(key, 0);
    ptr = lean_sarray_cptr(data);
    len = lean_sarray_size(data);
  }

  lean_object* state = lean_alloc_sarray(
    sizeof(uint8_t),
    sizeof(crypto_generichash_state),
    sizeof(crypto_generichash_state));

  crypto_generichash_init(
    (crypto_generichash_state*) lean_sarray_cptr(state),
    ptr,
    len,
    crypto_generichash_BYTES_MAX);

  lean_object* stream = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(stream, 0, state);
  return stream;
}

LEAN_EXPORT lean_obj_res lean_sodium_generichash_update(lean_obj_arg stream, b_lean_obj_arg input) {
  crypto_generichash_update(
    (crypto_generichash_state*) lean_sarray_cptr(lean_ctor_get(stream, 0)),
    lean_sarray_cptr(input),
    lean_sarray_size(input));

  return stream;
}

LEAN_EXPORT lean_obj_res lean_sodium_generichash_final(b_lean_obj_arg stream) {
  lean_object* ret = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_generichash_BYTES_MAX,
    crypto_generichash_BYTES_MAX);

  crypto_generichash_final(
    (crypto_generichash_state*) lean_sarray_cptr(lean_ctor_get(stream, 0)),
    lean_sarray_cptr(ret),
    crypto_generichash_BYTES_MAX);

  return ret;
}
