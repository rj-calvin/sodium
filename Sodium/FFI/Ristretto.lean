import Sodium.FFI.Basic

universe u

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI.Ristretto

variable {σ : Type u}

alloy c section
extern lean_obj_res lean_sodium_malloc(b_lean_obj_arg, size_t, lean_obj_arg);
extern lean_obj_res sodium_secure_to_lean(void*);
extern void* sodium_secure_of_lean(b_lean_obj_arg);
end

def BYTES : Nat := 32
def HASHBYTES : Nat := 64
def SCALARBYTES : Nat := 32
def NONREDUCEDSCALARBYTES : Nat := 64

alloy c extern "lean_crypto_core_ristretto255_is_valid_point"
def isValidPoint (p : @& ByteVector BYTES) : Bool :=
  size_t len = lean_sarray_size(p);
  if (len != crypto_core_ristretto255_BYTES) {
    return false;
  }
  return crypto_core_ristretto255_is_valid_point(lean_sarray_cptr(p)) == 1;

alloy c extern "lean_crypto_core_ristretto255_add"
def add (p q : @& ByteVector BYTES) : Option (ByteVector BYTES) :=
  size_t len_p = lean_sarray_size(p);
  size_t len_q = lean_sarray_size(q);

  if (len_p != crypto_core_ristretto255_BYTES || len_q != crypto_core_ristretto255_BYTES) {
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return none;
  }

  lean_object* r = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_core_ristretto255_BYTES,
    crypto_core_ristretto255_BYTES);

  if (crypto_core_ristretto255_add(
        lean_sarray_cptr(r),
        lean_sarray_cptr(p),
        lean_sarray_cptr(q)) != 0) {
    lean_dec(r);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return none;
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, r);
  return some;

alloy c extern "lean_crypto_core_ristretto255_sub"
def sub (p q : @& ByteVector BYTES) : Option (ByteVector BYTES) :=
  size_t len_p = lean_sarray_size(p);
  size_t len_q = lean_sarray_size(q);

  if (len_p != crypto_core_ristretto255_BYTES || len_q != crypto_core_ristretto255_BYTES) {
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return none;
  }

  lean_object* r = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_core_ristretto255_BYTES,
    crypto_core_ristretto255_BYTES);

  if (crypto_core_ristretto255_sub(
        lean_sarray_cptr(r),
        lean_sarray_cptr(p),
        lean_sarray_cptr(q)) != 0) {
    lean_dec(r);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return none;
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, r);
  return some;

alloy c extern "lean_crypto_core_ristretto255_from_hash"
def fromHash (h : @& ByteVector HASHBYTES) : Option (ByteVector BYTES) :=
  size_t len_h = lean_sarray_size(h);

  if (len_h != crypto_core_ristretto255_HASHBYTES) {
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return none;
  }

  lean_object* p = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_core_ristretto255_BYTES,
    crypto_core_ristretto255_BYTES);

  if (crypto_core_ristretto255_from_hash(
        lean_sarray_cptr(p),
        lean_sarray_cptr(h)) != 0) {
    lean_dec(p);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return none;
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, p);
  return some;

alloy c extern "lean_crypto_core_ristretto255_random"
def random : IO (ByteVector BYTES) :=
  lean_object* p = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_core_ristretto255_BYTES,
    crypto_core_ristretto255_BYTES);

  crypto_core_ristretto255_random(lean_sarray_cptr(p));

  return lean_io_result_mk_ok(p);

alloy c extern "lean_crypto_core_ristretto255_scalar_random"
def scalarRandom {τ : @& Sodium σ} : IO (SecretVector τ SCALARBYTES) :=
  lean_obj_res scalar_io = lean_sodium_malloc(τ, crypto_core_ristretto255_SCALARBYTES, _1);
  if (lean_io_result_is_error(scalar_io)) {
    return scalar_io;
  }

  lean_object* scalar = lean_io_result_take_value(scalar_io);
  void* scalar_ref = sodium_secure_of_lean(lean_ctor_get(scalar, 0));

  sodium_mprotect_readwrite(scalar_ref);
  crypto_core_ristretto255_scalar_random((unsigned char*) scalar_ref);
  sodium_mprotect_noaccess(scalar_ref);

  return lean_io_result_mk_ok(scalar);

alloy c extern "lean_crypto_core_ristretto255_scalar_invert"
def scalarInvert {τ : @& Sodium σ}
    (s : @& SecretVector τ SCALARBYTES)
    : IO (Option (SecretVector τ SCALARBYTES)) :=
  size_t s_len = lean_ctor_get_usize(s, 1);
  if (s_len != crypto_core_ristretto255_SCALARBYTES) {
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_obj_res recip_io = lean_sodium_malloc(τ, crypto_core_ristretto255_SCALARBYTES, _2);
  if (lean_io_result_is_error(recip_io)) {
    return recip_io;
  }

  lean_object* recip = lean_io_result_take_value(recip_io);
  void* recip_ref = sodium_secure_of_lean(lean_ctor_get(recip, 0));
  void* s_ref = sodium_secure_of_lean(lean_ctor_get(s, 0));

  sodium_mprotect_readwrite(recip_ref);
  sodium_mprotect_readonly(s_ref);

  int err = crypto_core_ristretto255_scalar_invert((unsigned char*) recip_ref, (const unsigned char*) s_ref);

  sodium_mprotect_noaccess(recip_ref);
  sodium_mprotect_noaccess(s_ref);

  if (err != 0) {
    sodium_munlock(recip_ref, crypto_core_ristretto255_SCALARBYTES);
    lean_dec(recip);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    lean_object* ok = lean_io_result_mk_ok(none);
    return ok;
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, recip);
  lean_object* ok = lean_io_result_mk_ok(some);
  return ok;

alloy c extern "lean_crypto_core_ristretto255_scalar_unary"
def scalarNegate {τ : @& Sodium σ}
    (s : @& SecretVector τ SCALARBYTES) : IO (Option (SecretVector τ SCALARBYTES)) :=
  size_t s_len = lean_ctor_get_usize(s, 1);
  if (s_len != crypto_core_ristretto255_SCALARBYTES) {
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_obj_res out_io = lean_sodium_malloc(τ, crypto_core_ristretto255_SCALARBYTES, _2);
  if (lean_io_result_is_error(out_io)) {
    return out_io;
  }

  lean_object* out = lean_io_result_take_value(out_io);
  void* out_ref = sodium_secure_of_lean(lean_ctor_get(out, 0));
  void* s_ref = sodium_secure_of_lean(lean_ctor_get(s, 0));

  sodium_mprotect_readwrite(out_ref);
  sodium_mprotect_readonly(s_ref);
  crypto_core_ristretto255_scalar_negate((unsigned char*) out_ref, (const unsigned char*) s_ref);
  sodium_mprotect_noaccess(out_ref);
  sodium_mprotect_noaccess(s_ref);

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, out);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_core_ristretto255_scalar_complement"
def scalarComplement {τ : @& Sodium σ}
    (s : @& SecretVector τ SCALARBYTES) : IO (Option (SecretVector τ SCALARBYTES)) :=
  size_t s_len = lean_ctor_get_usize(s, 1);
  if (s_len != crypto_core_ristretto255_SCALARBYTES) {
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_obj_res out_io = lean_sodium_malloc(τ, crypto_core_ristretto255_SCALARBYTES, _2);
  if (lean_io_result_is_error(out_io)) {
    return out_io;
  }

  lean_object* out = lean_io_result_take_value(out_io);
  void* out_ref = sodium_secure_of_lean(lean_ctor_get(out, 0));
  void* s_ref = sodium_secure_of_lean(lean_ctor_get(s, 0));

  sodium_mprotect_readwrite(out_ref);
  sodium_mprotect_readonly(s_ref);
  crypto_core_ristretto255_scalar_complement((unsigned char*) out_ref, (const unsigned char*) s_ref);
  sodium_mprotect_noaccess(out_ref);
  sodium_mprotect_noaccess(s_ref);

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, out);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_core_ristretto255_scalar_add"
def scalarAdd {τ : @& Sodium σ}
    (x y : @& SecretVector τ SCALARBYTES) : IO (Option (SecretVector τ SCALARBYTES)) :=
  size_t x_len = lean_ctor_get_usize(x, 1);
  size_t y_len = lean_ctor_get_usize(y, 1);
  if (x_len != crypto_core_ristretto255_SCALARBYTES || y_len != crypto_core_ristretto255_SCALARBYTES) {
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_obj_res out_io = lean_sodium_malloc(τ, crypto_core_ristretto255_SCALARBYTES, _3);
  if (lean_io_result_is_error(out_io)) {
    return out_io;
  }

  lean_object* out = lean_io_result_take_value(out_io);
  void* out_ref = sodium_secure_of_lean(lean_ctor_get(out, 0));
  void* x_ref = sodium_secure_of_lean(lean_ctor_get(x, 0));
  void* y_ref = sodium_secure_of_lean(lean_ctor_get(y, 0));

  sodium_mprotect_readwrite(out_ref);
  sodium_mprotect_readonly(x_ref);
  sodium_mprotect_readonly(y_ref);

  crypto_core_ristretto255_scalar_add(
    (unsigned char*) out_ref,
    (const unsigned char*) x_ref,
    (const unsigned char*) y_ref);

  sodium_mprotect_noaccess(out_ref);
  sodium_mprotect_noaccess(x_ref);
  sodium_mprotect_noaccess(y_ref);

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, out);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_core_ristretto255_scalar_sub"
def scalarSub {τ : @& Sodium σ}
    (x y : @& SecretVector τ SCALARBYTES) : IO (Option (SecretVector τ SCALARBYTES)) :=
  size_t x_len = lean_ctor_get_usize(x, 1);
  size_t y_len = lean_ctor_get_usize(y, 1);
  if (x_len != crypto_core_ristretto255_SCALARBYTES || y_len != crypto_core_ristretto255_SCALARBYTES) {
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_obj_res out_io = lean_sodium_malloc(τ, crypto_core_ristretto255_SCALARBYTES, _3);
  if (lean_io_result_is_error(out_io)) {
    return out_io;
  }

  lean_object* out = lean_io_result_take_value(out_io);
  void* out_ref = sodium_secure_of_lean(lean_ctor_get(out, 0));
  void* x_ref = sodium_secure_of_lean(lean_ctor_get(x, 0));
  void* y_ref = sodium_secure_of_lean(lean_ctor_get(y, 0));

  sodium_mprotect_readwrite(out_ref);
  sodium_mprotect_readonly(x_ref);
  sodium_mprotect_readonly(y_ref);

  crypto_core_ristretto255_scalar_sub(
    (unsigned char*) out_ref,
    (const unsigned char*) x_ref,
    (const unsigned char*) y_ref);

  sodium_mprotect_noaccess(out_ref);
  sodium_mprotect_noaccess(x_ref);
  sodium_mprotect_noaccess(y_ref);

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, out);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_core_ristretto255_scalar_mul"
def scalarMul {τ : @& Sodium σ}
    (x y : @& SecretVector τ SCALARBYTES) : IO (Option (SecretVector τ SCALARBYTES)) :=
  size_t x_len = lean_ctor_get_usize(x, 1);
  size_t y_len = lean_ctor_get_usize(y, 1);
  if (x_len != crypto_core_ristretto255_SCALARBYTES || y_len != crypto_core_ristretto255_SCALARBYTES) {
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_obj_res out_io = lean_sodium_malloc(τ, crypto_core_ristretto255_SCALARBYTES, _3);
  if (lean_io_result_is_error(out_io)) {
    return out_io;
  }

  lean_object* out = lean_io_result_take_value(out_io);
  void* out_ref = sodium_secure_of_lean(lean_ctor_get(out, 0));
  void* x_ref = sodium_secure_of_lean(lean_ctor_get(x, 0));
  void* y_ref = sodium_secure_of_lean(lean_ctor_get(y, 0));

  sodium_mprotect_readwrite(out_ref);
  sodium_mprotect_readonly(x_ref);
  sodium_mprotect_readonly(y_ref);

  crypto_core_ristretto255_scalar_mul(
    (unsigned char*) out_ref,
    (const unsigned char*) x_ref,
    (const unsigned char*) y_ref);

  sodium_mprotect_noaccess(out_ref);
  sodium_mprotect_noaccess(x_ref);
  sodium_mprotect_noaccess(y_ref);

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, out);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_core_ristretto255_scalar_reduce"
def scalarReduce {τ : @& Sodium σ}
    (wide : @& ByteVector NONREDUCEDSCALARBYTES) : IO (Option (SecretVector τ SCALARBYTES)) :=
  size_t wide_len = lean_sarray_size(wide);
  if (wide_len != crypto_core_ristretto255_NONREDUCEDSCALARBYTES) {
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_obj_res out_io = lean_sodium_malloc(τ, crypto_core_ristretto255_SCALARBYTES, _2);
  if (lean_io_result_is_error(out_io)) {
    return out_io;
  }

  lean_object* out = lean_io_result_take_value(out_io);
  void* out_ref = sodium_secure_of_lean(lean_ctor_get(out, 0));

  sodium_mprotect_readwrite(out_ref);
  crypto_core_ristretto255_scalar_reduce(
    (unsigned char*) out_ref,
    lean_sarray_cptr(wide));
  sodium_mprotect_noaccess(out_ref);

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, out);
  return lean_io_result_mk_ok(some);

alloy c extern "lean_crypto_scalarmult_ristretto255"
def scalarmult {τ : @& Sodium σ}
    (scalar : @& SecretVector τ SCALARBYTES)
    (point : @& ByteVector BYTES)
    : IO (Option (ByteVector BYTES)) :=
  size_t scalar_len = lean_ctor_get_usize(scalar, 1);
  size_t point_len = lean_sarray_size(point);

  if (scalar_len != crypto_scalarmult_ristretto255_SCALARBYTES || point_len != crypto_scalarmult_ristretto255_BYTES) {
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* out = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_scalarmult_ristretto255_BYTES,
    crypto_scalarmult_ristretto255_BYTES);

  void* scalar_ref = sodium_secure_of_lean(lean_ctor_get(scalar, 0));
  sodium_mprotect_readonly(scalar_ref);

  int err = crypto_scalarmult_ristretto255(
    lean_sarray_cptr(out),
    (const unsigned char*) scalar_ref,
    lean_sarray_cptr(point));

  sodium_mprotect_noaccess(scalar_ref);

  if (err != 0) {
    lean_dec(out);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    lean_object* ok = lean_io_result_mk_ok(none);
    return ok;
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, out);
  lean_object* ok = lean_io_result_mk_ok(some);
  return ok;

alloy c extern "lean_crypto_scalarmult_ristretto255_base"
def scalarbase {τ : @& Sodium σ}
    (scalar : @& SecretVector τ SCALARBYTES)
    : IO (Option (ByteVector BYTES)) :=
  size_t scalar_len = lean_ctor_get_usize(scalar, 1);
  if (scalar_len != crypto_scalarmult_ristretto255_SCALARBYTES) {
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* out = lean_alloc_sarray(
    sizeof(uint8_t),
    crypto_scalarmult_ristretto255_BYTES,
    crypto_scalarmult_ristretto255_BYTES);

  void* scalar_ref = sodium_secure_of_lean(lean_ctor_get(scalar, 0));
  sodium_mprotect_readonly(scalar_ref);

  int err = crypto_scalarmult_ristretto255_base(
    lean_sarray_cptr(out),
    (const unsigned char*) scalar_ref);

  sodium_mprotect_noaccess(scalar_ref);

  if (err != 0) {
    lean_dec(out);
    lean_object* none = lean_alloc_ctor(0, 0, 0);
    return lean_io_result_mk_ok(none);
  }

  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, out);
  return lean_io_result_mk_ok(some);

end Sodium.FFI.Ristretto
