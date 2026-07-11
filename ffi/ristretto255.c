#include "ffi.h"

LEAN_EXPORT lean_obj_res lean_sodium_ristretto255_scalar_random(lean_obj_arg world) {
  void* ptr = sodium_malloc(32);
  crypto_core_ristretto255_scalar_random(ptr);
  sodium_mprotect_noaccess(ptr);
  lean_object* ret = lean_alloc_ctor(0, 1, sizeof(size_t));
  lean_ctor_set(ret, 0, secure_obj_to_lean(ptr));
  lean_ctor_set_usize(ret, 1, 32);
  return lean_io_result_mk_ok(ret);
}

LEAN_EXPORT lean_obj_res lean_sodium_ristretto255_scalar_reduce(b_lean_obj_arg hash, lean_obj_arg world) {
  void* ptr = sodium_malloc(32);
  crypto_core_ristretto255_scalar_reduce(ptr, lean_sarray_cptr(hash));
  sodium_mprotect_noaccess(ptr);
  lean_object* ret = lean_alloc_ctor(0, 1, sizeof(size_t));
  lean_ctor_set(ret, 0, secure_obj_to_lean(ptr));
  lean_ctor_set_usize(ret, 1, 32);
  return lean_io_result_mk_ok(ret);
}

LEAN_EXPORT lean_obj_res lean_sodium_scalarmult_ristretto255_base(b_lean_obj_arg n) {
  lean_object* q = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_scalarmult_ristretto255_BYTES,
    crypto_scalarmult_ristretto255_BYTES);

  if (crypto_scalarmult_ristretto255_base(lean_sarray_cptr(q), lean_sarray_cptr(n)) != 0) {
    lean_dec(q);
    return lean_box(0);
  }

  return lean_mk_option_some(q);
}

LEAN_EXPORT lean_obj_res lean_sodium_scalarmult_ristretto255(b_lean_obj_arg n, b_lean_obj_arg p) {
  lean_object* q = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_scalarmult_ristretto255_BYTES,
    crypto_scalarmult_ristretto255_BYTES);

  if (crypto_scalarmult_ristretto255(lean_sarray_cptr(q), lean_sarray_cptr(n), lean_sarray_cptr(p)) != 0) {
    lean_dec(q);
    return lean_box(0);
  }

  return lean_mk_option_some(q);
}

LEAN_EXPORT lean_obj_res lean_sodium_core_ristretto255_add(b_lean_obj_arg p, b_lean_obj_arg q) {
  lean_object* r = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_core_ristretto255_BYTES,
    crypto_core_ristretto255_BYTES);

  if (crypto_core_ristretto255_add(lean_sarray_cptr(r), lean_sarray_cptr(p), lean_sarray_cptr(q)) != 0) {
    lean_dec(r);
    return lean_box(0);
  }

  return lean_mk_option_some(r);
}

LEAN_EXPORT lean_obj_res lean_sodium_core_ristretto255_sub(b_lean_obj_arg p, b_lean_obj_arg q) {
  lean_object* r = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_core_ristretto255_BYTES,
    crypto_core_ristretto255_BYTES);

  if (crypto_core_ristretto255_sub(lean_sarray_cptr(r), lean_sarray_cptr(p), lean_sarray_cptr(q)) != 0) {
    lean_dec(r);
    return lean_box(0);
  }

  return lean_mk_option_some(r);
}

LEAN_EXPORT lean_obj_res lean_sodium_core_ristretto255_from_hash(b_lean_obj_arg r) {
  lean_object* p = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_core_ristretto255_BYTES,
    crypto_core_ristretto255_BYTES);
  crypto_core_ristretto255_from_hash(lean_sarray_cptr(p), lean_sarray_cptr(r));
  return p;
}

LEAN_EXPORT uint8_t lean_sodium_core_ristretto255_is_valid_point(b_lean_obj_arg p) {
  return crypto_core_ristretto255_is_valid_point(lean_sarray_cptr(p)) == 1;
}

LEAN_EXPORT lean_obj_res lean_sodium_core_ristretto255_scalar_reduce(b_lean_obj_arg s) {
  lean_object* r = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_core_ristretto255_SCALARBYTES,
    crypto_core_ristretto255_SCALARBYTES);
  crypto_core_ristretto255_scalar_reduce(lean_sarray_cptr(r), lean_sarray_cptr(s));
  return r;
}

LEAN_EXPORT lean_obj_res lean_sodium_core_ristretto255_scalar_add(b_lean_obj_arg x, b_lean_obj_arg y) {
  lean_object* z = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_core_ristretto255_SCALARBYTES,
    crypto_core_ristretto255_SCALARBYTES);
  crypto_core_ristretto255_scalar_add(lean_sarray_cptr(z), lean_sarray_cptr(x), lean_sarray_cptr(y));
  return z;
}

LEAN_EXPORT lean_obj_res lean_sodium_core_ristretto255_scalar_mul(b_lean_obj_arg x, b_lean_obj_arg y) {
  lean_object* z = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_core_ristretto255_SCALARBYTES,
    crypto_core_ristretto255_SCALARBYTES);
  crypto_core_ristretto255_scalar_mul(lean_sarray_cptr(z), lean_sarray_cptr(x), lean_sarray_cptr(y));
  return z;
}

LEAN_EXPORT lean_obj_res lean_sodium_core_ristretto255_scalar_negate(b_lean_obj_arg s) {
  lean_object* neg = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_core_ristretto255_SCALARBYTES,
    crypto_core_ristretto255_SCALARBYTES);
  crypto_core_ristretto255_scalar_negate(lean_sarray_cptr(neg), lean_sarray_cptr(s));
  return neg;
}
