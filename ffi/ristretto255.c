#include "ffi.h"

LEAN_EXPORT lean_obj_res lean_sodium_ristretto255_scalar_random(b_lean_obj_arg tau, lean_obj_arg world) {
  void* ptr = sodium_malloc(32);
  crypto_core_ristretto255_scalar_random(ptr);
  sodium_mprotect_noaccess(ptr);
  lean_object* ret = lean_alloc_ctor(0, 1, sizeof(size_t));
  lean_ctor_set(ret, 0, secure_obj_to_lean(ptr));
  lean_ctor_set_usize(ret, 1, 32);
  return lean_io_result_mk_ok(ret);
}

LEAN_EXPORT lean_obj_res lean_sodium_ristretto255_scalar_reduce(b_lean_obj_arg tau, b_lean_obj_arg hash, lean_obj_arg world) {
  void* ptr = sodium_malloc(32);
  crypto_core_ristretto255_scalar_reduce(ptr, lean_sarray_cptr(hash));
  sodium_mprotect_noaccess(ptr);
  lean_object* ret = lean_alloc_ctor(0, 1, sizeof(size_t));
  lean_ctor_set(ret, 0, secure_obj_to_lean(ptr));
  lean_ctor_set_usize(ret, 1, 32);
  return lean_io_result_mk_ok(ret);
}
