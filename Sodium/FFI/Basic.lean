import Alloy.C
open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI

alloy c opaque_extern_type SecureMem => void where
  finalize(ptr) := sodium_free(ptr)

structure Secure where
  private ptr : SecureMem
  size : USize

-- Quotient type that ensures size consistency
def SecureWithSize (size : USize) := {secure : Secure // secure.size = size}

alloy c extern "lean_sodium_init"
def sodiumInit : BaseIO Int32 :=
  int result = sodium_init()
  return lean_io_result_mk_ok(lean_box(result))

alloy c extern "lean_randombytes_buf"
def randomBytes (size : USize) : BaseIO ByteArray :=
  lean_object* arr = lean_alloc_sarray(sizeof(unsigned char), size, size)
  randombytes(lean_sarray_cptr(arr), size)
  return lean_io_result_mk_ok(arr)

alloy c extern "lean_randombytes_uniform"
def randomUInt32 (sup : UInt32) : BaseIO UInt32 :=
  uint32_t result = randombytes_uniform(sup)
  return lean_io_result_mk_ok(lean_box_uint32(result))

alloy c extern "lean_sodium_memcmp"
def sodiumMemcmp (b1 : SecureMem) (b2 : SecureMem) : IO Int32 :=
  size_t len1 = lean_sarray_size(b1)
  size_t len2 = lean_sarray_size(b2)
  if (len1 != len2) {
    lean_object* error_msg = lean_mk_string("Buffer sizes must be equal for comparison")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  int result = sodium_memcmp(lean_sarray_cptr(b1), lean_sarray_cptr(b2), len1)
  return lean_io_result_mk_ok(lean_box(result))

alloy c extern "lean_sodium_memzero"
def sodiumMemzero (buffer : ByteArray) : BaseIO Unit :=
  size_t len = lean_sarray_size(buffer)
  sodium_memzero(lean_sarray_cptr(buffer), len)
  return lean_io_result_mk_ok(lean_box(0))

alloy c extern "lean_sodium_malloc"
def sodiumMalloc (size : USize) : IO (SecureWithSize size) :=
  void* ptr = sodium_malloc(size)

  if (ptr == NULL) {
    lean_internal_panic_out_of_memory()
  }

  lean_object* secure_mem = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(secure_mem, 0, to_lean<SecureMem>(ptr))
  lean_ctor_set(secure_mem, 1, lean_box_usize(size))

  lean_object* subtype = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(subtype, 0, secure_mem)
  lean_ctor_set(subtype, 1, lean_box(0))

  return lean_io_result_mk_ok(subtype)

alloy c extern "lean_sodium_mlock"
def sodiumMlock (secure_mem : @& Secure) : IO Unit :=
  lean_object* ptr_obj = lean_ctor_get(secure_mem, 0)
  lean_object* size_obj = lean_ctor_get(secure_mem, 1)
  void* mem_ptr = of_lean<SecureMem>(ptr_obj)
  size_t mem_size = lean_unbox_usize(size_obj)
  int result = sodium_mlock(mem_ptr, mem_size)
  if (result != 0) {
    lean_object* error_msg = lean_mk_string("sodium_mlock failed - cannot lock memory")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }
  return lean_io_result_mk_ok(lean_box(0))

alloy c extern "lean_sodium_munlock"
def sodiumMunlock (secure_mem : @& Secure) : IO Unit :=
  lean_object* ptr_obj = lean_ctor_get(secure_mem, 0)
  lean_object* size_obj = lean_ctor_get(secure_mem, 1)
  void* mem_ptr = of_lean<SecureMem>(ptr_obj)
  size_t mem_size = lean_unbox_usize(size_obj)
  int result = sodium_munlock(mem_ptr, mem_size)
  if (result != 0) {
    lean_object* error_msg = lean_mk_string("sodium_munlock failed")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }
  return lean_io_result_mk_ok(lean_box(0))

end Sodium.FFI
