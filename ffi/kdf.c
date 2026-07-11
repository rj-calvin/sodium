#include "ffi.h"
#include <string.h>

LEAN_EXPORT lean_obj_res lean_sodium_kdf_blake2b_derive(b_lean_obj_arg n, uint64_t idx, b_lean_obj_arg ctx, b_lean_obj_arg key) {
  size_t len = lean_usize_of_nat(n);
  lean_object* out = lean_alloc_sarray(sizeof(uint8_t), len, len);

  if (len < crypto_kdf_blake2b_BYTES_MIN || len > crypto_kdf_blake2b_BYTES_MAX ||
      crypto_kdf_blake2b_derive_from_key(
        lean_sarray_cptr(out),
        len,
        idx,
        (const char*) lean_sarray_cptr(ctx),
        lean_sarray_cptr(key)) != 0) {
    memset(lean_sarray_cptr(out), 0, len);
  }

  return out;
}
