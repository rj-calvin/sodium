#include "ffi.h"

LEAN_EXPORT lean_obj_res lean_sodium_kdf_derive_from_key(b_lean_obj_arg tau, uint64_t idx, b_lean_obj_arg ctx, b_lean_obj_arg key, lean_obj_arg world) {
  void* ptr = sodium_malloc(32);
  void* mptr = secure_obj_of_lean(lean_ctor_get(key, 0));
  sodium_mprotect_readonly(mptr);
  int err = crypto_kdf_blake2b_derive_from_key(ptr, 32, idx, (const char*) lean_sarray_cptr(ctx), mptr);
  sodium_mprotect_noaccess(ptr);
  sodium_mprotect_noaccess(mptr);

  if (err != 0) {
    sodium_free(ptr);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("crypto_kdf_blake2b_derive_from_key failed")));
  }

  lean_object* ret = lean_alloc_ctor(0, 1, sizeof(size_t));
  lean_ctor_set(ret, 0, secure_obj_to_lean(ptr));
  lean_ctor_set_usize(ret, 1, 32);
  return lean_io_result_mk_ok(ret);
}
