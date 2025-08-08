import Lean.Data.Json
import Alloy.C

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h> <string.h>

structure Sodium (σ : Type) where private mk ::

namespace Sodium

alloy c extern "lean_sodium_init"
def init (σ : Type) : IO (Sodium σ) :=
  if (sodium_init() < 0) {
    lean_object* error_msg = lean_mk_string("Failed to initialize LibSodium")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  lean_object* ctx = lean_alloc_ctor(0, 0, 0)
  return lean_io_result_mk_ok(ctx)

variable {σ : Type}

private alloy c opaque_extern_type SecurePointed => void where
  finalize(ptr) := sodium_free(ptr)

-- Workaround solution for cross-module access to SecurePointed.
alloy c section
LEAN_EXPORT lean_obj_res sodium_secure_to_lean(void* ptr) {
  return _alloy_to_l___private_Sodium_FFI_Basic_0__Sodium_SecurePointed(ptr);
}

LEAN_EXPORT void* sodium_secure_of_lean(b_lean_obj_arg obj) {
  return _alloy_of_l___private_Sodium_FFI_Basic_0__Sodium_SecurePointed(obj);
}
end

structure SecureArray (_ : Sodium σ) where
  private mk ::
  private ref : SecurePointed.nonemptyType.type
  size : USize

namespace SecureArray

alloy c extern "lean_sodium_malloc"
def new (ctx : @& Sodium σ) (size : USize) : IO (SecureArray ctx) :=
  void* ptr = sodium_malloc(size);

  if (ptr == NULL) {
    lean_object* error_msg = lean_mk_string("Failed to allocate secure memory");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  sodium_memzero(ptr, size);
  sodium_mlock(ptr, size);
  sodium_mprotect_noaccess(ptr);

  lean_object* secure_pointed = to_lean<SecurePointed>(ptr);
  lean_object* secure_ref = lean_alloc_ctor(0, 1, sizeof(size_t));
  lean_ctor_set(secure_ref, 0, secure_pointed);
  lean_ctor_set_usize(secure_ref, 1, size);

  return lean_io_result_mk_ok(secure_ref);

alloy c extern "lean_sodium_is_zero"
def isZero {ctx : @& Sodium σ} (buf : @& SecureArray ctx) : Bool :=
  size_t len = lean_ctor_get_usize(buf, 1);
  void* ptr = of_lean<SecurePointed>(lean_ctor_get(buf, 0));
  int result = sodium_is_zero(ptr, len);
  return result == 1;

alloy c extern "lean_sodium_memcmp"
def compare {ctx : @& Sodium σ} (b1 : @& SecureArray ctx) (b2 : @& SecureArray ctx) : Ordering :=
  size_t len1 = lean_ctor_get_usize(b1, 1);
  size_t len2 = lean_ctor_get_usize(b2, 2);

  if (len1 != len2) {
    return len1 < len2 ? 0 : 2;
  }

  void* ptr1 = of_lean<SecurePointed>(lean_ctor_get(b1, 0));
  void* ptr2 = of_lean<SecurePointed>(lean_ctor_get(b2, 0));
  int result = sodium_compare(ptr1, ptr2, len1);
  return result + 1;

instance {τ : Sodium σ} : Ord (SecureArray τ) := ⟨compare⟩

end SecureArray

structure EntropyArray (_ : Sodium σ) where
  private mk ::
  private ref : SecurePointed.nonemptyType.type
  off : USize
  size : USize

noncomputable instance {τ : Sodium σ} : Inhabited (EntropyArray τ) :=
  ⟨{ ref := Classical.choice SecurePointed.nonemptyType.property, off := 0, size := 0 }⟩

namespace EntropyArray

alloy c extern "lean_sodium_randombytes_buf"
def new (τ : @& Sodium σ) (size : USize) : IO (EntropyArray τ) :=
  if (size == 0) {
    lean_object* error_msg = lean_mk_string("Cannot allocate zero-sized secure memory");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  void* ptr = sodium_malloc(size);

  if (ptr == NULL) {
    lean_object* error_msg = lean_mk_string("Failed to allocate secure memory");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  sodium_mlock(ptr, size);
  randombytes_buf(ptr, size);
  sodium_mprotect_readonly(ptr);

  lean_object* secure_pointed = to_lean<SecurePointed>(ptr);
  lean_object* secure_ref = lean_alloc_ctor(0, 1, 2);
  lean_ctor_set(secure_ref, 0, secure_pointed);
  lean_ctor_set_usize(secure_ref, 1, 0);
  lean_ctor_set_usize(secure_ref, 2, size);

  return lean_io_result_mk_ok(secure_ref);

alloy c extern "lean_sodium_randombytes_buf_refresh"
def refresh {τ : @& Sodium σ} (arr : EntropyArray τ) : BaseIO (EntropyArray τ) :=
  void* ptr = of_lean<SecurePointed>(lean_ctor_get(arr, 0));
  size_t size = lean_ctor_get_usize(arr, 2);

  sodium_mprotect_readwrite(ptr);
  randombytes_buf(ptr, size);
  sodium_mprotect_readonly(ptr);

  lean_ctor_set_usize(arr, 1, 0);
  return arr;

/--
Copy a slice from an EntropyArray to a ByteArray for safe data extraction.
Extracted data is zeroed from the source EntropyArray.
-/
alloy c extern "lean_entropy_copy_slice"
def extract (τ : @& Sodium σ) (src : EntropyArray τ) (len : USize) : BaseIO (ByteArray × EntropyArray τ) :=
  size_t off = lean_ctor_get_usize(src, 1);
  size_t size = lean_ctor_get_usize(src, 2);
  size_t clamped_len = (off >= size) ? 0 : (off + len > size) ? (size - off) : len;

  if (clamped_len == 0) {
    lean_object* empty_dest = lean_alloc_sarray(sizeof(uint8_t), 0, 0);
    lean_object* result_pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result_pair, 0, empty_dest);
    lean_ctor_set(result_pair, 1, src);
    return lean_io_result_mk_ok(result_pair);
  }

  void* secure_ptr = of_lean<SecurePointed>(lean_ctor_get(src, 0));

  lean_object* dest = lean_alloc_sarray(sizeof(uint8_t), clamped_len, clamped_len);

  sodium_mprotect_readwrite(secure_ptr);
  memcpy(lean_sarray_cptr(dest), ((uint8_t*)secure_ptr) + off, clamped_len);
  sodium_memzero(((uint8_t*)secure_ptr) + off, clamped_len);
  sodium_mprotect_readonly(secure_ptr);

  lean_ctor_set_usize(src, 1, off + clamped_len);

  lean_object* result_pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(result_pair, 0, dest);
  lean_ctor_set(result_pair, 1, src);

  return lean_io_result_mk_ok(result_pair);

end EntropyArray

end Sodium
