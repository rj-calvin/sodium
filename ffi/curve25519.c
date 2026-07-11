#include "ffi.h"

LEAN_EXPORT lean_obj_res lean_sodium_scalarmult_base(b_lean_obj_arg n) {
  lean_object* q = lean_alloc_sarray(sizeof(uint8_t), crypto_scalarmult_BYTES, crypto_scalarmult_BYTES);

  if (crypto_scalarmult_base(lean_sarray_cptr(q), lean_sarray_cptr(n)) != 0) {
    lean_dec(q);
    return lean_box(0);
  }

  return lean_mk_option_some(q);
}

LEAN_EXPORT lean_obj_res lean_sodium_scalarmult(b_lean_obj_arg n, b_lean_obj_arg p) {
  lean_object* q = lean_alloc_sarray(sizeof(uint8_t), crypto_scalarmult_BYTES, crypto_scalarmult_BYTES);

  if (crypto_scalarmult(lean_sarray_cptr(q), lean_sarray_cptr(n), lean_sarray_cptr(p)) != 0) {
    lean_dec(q);
    return lean_box(0);
  }

  return lean_mk_option_some(q);
}
