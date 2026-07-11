#include "ffi.h"

LEAN_EXPORT lean_obj_res lean_sodium_core_hsalsa20(b_lean_obj_arg in) {
  static const uint8_t zero[crypto_core_hsalsa20_INPUTBYTES] = {0};
  lean_object* out = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_core_hsalsa20_OUTPUTBYTES,
    crypto_core_hsalsa20_OUTPUTBYTES);
  crypto_core_hsalsa20(lean_sarray_cptr(out), zero, lean_sarray_cptr(in), NULL);
  return out;
}

LEAN_EXPORT lean_obj_res lean_sodium_core_hchacha20(b_lean_obj_arg in) {
  static const uint8_t zero[crypto_core_hchacha20_INPUTBYTES] = {0};
  lean_object* out = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_core_hchacha20_OUTPUTBYTES,
    crypto_core_hchacha20_OUTPUTBYTES);
  crypto_core_hchacha20(lean_sarray_cptr(out), zero, lean_sarray_cptr(in), NULL);
  return out;
}
