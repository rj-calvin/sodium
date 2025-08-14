import Sodium.Data.ByteVector

import Alloy.C

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h> <string.h> <stdio.h> <stdlib.h>

structure Sodium (σ : Type) where private mk ::

namespace Sodium

alloy c extern "lean_sodium_init"
def init (σ : Type) : IO (Sodium σ) :=
  if (sodium_init() < 0) {
    lean_object* error_msg = lean_mk_string("Failed to initialize LibSodium")
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* ctx = lean_alloc_ctor(0, 0, 0)
  return lean_io_result_mk_ok(ctx)

variable {n m : USize} {σ : Type}

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

structure SecureVector (_ : Sodium σ) (n : USize) where
  private mk ::
  private ref : SecurePointed.nonemptyType.type
  usize : USize
  usize_rfl : usize = n

noncomputable instance {τ : Sodium σ} : Nonempty (SecureVector τ n) :=
  ⟨{ ref := Classical.choice SecurePointed.nonemptyType.property, usize := n, usize_rfl := rfl }⟩

noncomputable instance {τ : Sodium σ} : Inhabited (SecureVector τ n) :=
  ⟨{ ref := Classical.choice SecurePointed.nonemptyType.property, usize := n, usize_rfl := rfl }⟩

namespace SecureVector

abbrev size {τ : Sodium σ} (x : SecureVector τ n) : Nat := x.usize.toNat

alloy c extern "lean_sodium_malloc"
def new {τ : @& Sodium σ} (size : USize) : IO (SecureVector τ size) :=
  void* ptr = sodium_malloc(size);

  if (ptr == NULL) {
    lean_object* error_msg = lean_mk_string("Failed to allocate secure memory");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }

  randombytes_buf(ptr, size);
  sodium_mprotect_noaccess(ptr);

  lean_object* secure_pointed = to_lean<SecurePointed>(ptr);
  lean_object* secure_ref = lean_alloc_ctor(0, 1, sizeof(size_t));
  lean_ctor_set(secure_ref, 0, secure_pointed);
  lean_ctor_set_usize(secure_ref, 1, size);

  return lean_io_result_mk_ok(secure_ref);

alloy c extern "lean_sodium_is_zero"
def isZero {τ : @& Sodium σ} (buf : @& SecureVector τ n) : Bool :=
  size_t len = lean_ctor_get_usize(buf, 1);
  void* ptr = of_lean<SecurePointed>(lean_ctor_get(buf, 0));
  sodium_mprotect_readonly(ptr);
  int result = sodium_is_zero(ptr, len);
  sodium_mprotect_noaccess(ptr);
  return result == 1;

alloy c extern "lean_sodium_memcmp"
def compare {τ : @& Sodium σ} (b1 : @& SecureVector τ n) (b2 : @& SecureVector τ m) : Ordering :=
  size_t len1 = lean_ctor_get_usize(b1, 1);
  size_t len2 = lean_ctor_get_usize(b2, 1);

  if (len1 != len2) {
    return len1 < len2 ? 0 : 2;
  }

  void* ptr1 = of_lean<SecurePointed>(lean_ctor_get(b1, 0));
  void* ptr2 = of_lean<SecurePointed>(lean_ctor_get(b2, 0));
  sodium_mprotect_readonly(ptr1);
  sodium_mprotect_readonly(ptr2);
  int result = sodium_compare(ptr1, ptr2, len1);
  sodium_mprotect_noaccess(ptr2);
  sodium_mprotect_noaccess(ptr1);
  return result + 1;

instance {τ : Sodium σ} : Ord (SecureVector τ n) := ⟨compare⟩

instance {τ : Sodium σ} : BEq (SecureVector τ n) where
  beq x y := compare x y == .eq

alloy c extern "lean_sodium_load_secret_key"
def ofFile {τ : @& Sodium σ} (fileKey : @& SecureVector τ m) (filePath : @& System.FilePath)
    (expectedSize : USize) : IO (SecureVector τ expectedSize) :=
  const char* path = lean_string_cstr(filePath);
  void* file_key_ptr = of_lean<SecurePointed>(lean_ctor_get(fileKey, 0));

  FILE* file = fopen(path, "rb");
  if (file == NULL) {
    lean_object* error_msg = lean_mk_string("Failed to open encrypted file for reading");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }

  unsigned char header[crypto_secretstream_xchacha20poly1305_HEADERBYTES];
  if (fread(header, 1, sizeof(header), file) != sizeof(header)) {
    fclose(file);
    lean_object* error_msg = lean_mk_string("Failed to read encryption header");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }

  crypto_secretstream_xchacha20poly1305_state state;
  sodium_mprotect_readonly(file_key_ptr);
  if (crypto_secretstream_xchacha20poly1305_init_pull(&state, header, (unsigned char*)file_key_ptr) != 0) {
    sodium_mprotect_noaccess(file_key_ptr);
    fclose(file);
    lean_object* error_msg = lean_mk_string("Failed to initialize decryption");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }
  sodium_mprotect_noaccess(file_key_ptr);

  size_t ciphertext_len = expectedSize + crypto_secretstream_xchacha20poly1305_ABYTES;
  unsigned char* ciphertext = (unsigned char*)malloc(ciphertext_len);
  if (ciphertext == NULL) {
    sodium_memzero(&state, sizeof(state));
    fclose(file);
    lean_object* error_msg = lean_mk_string("Failed to allocate memory for ciphertext");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }

  size_t bytes_read = fread(ciphertext, 1, ciphertext_len, file);
  fclose(file);

  if (bytes_read != ciphertext_len) {
    sodium_memzero(ciphertext, ciphertext_len);
    free(ciphertext);
    sodium_memzero(&state, sizeof(state));
    lean_object* error_msg = lean_mk_string("Encrypted file has incorrect size");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }

  void* secure_ptr = sodium_malloc(expectedSize);
  if (secure_ptr == NULL) {
    sodium_memzero(ciphertext, ciphertext_len);
    free(ciphertext);
    sodium_memzero(&state, sizeof(state));
    lean_object* error_msg = lean_mk_string("Failed to allocate secure memory");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }

  sodium_mprotect_readwrite(secure_ptr);

  unsigned long long decrypted_len;
  unsigned char tag;
  if (crypto_secretstream_xchacha20poly1305_pull(&state, (unsigned char*)secure_ptr, &decrypted_len, &tag,
                                                ciphertext, ciphertext_len, NULL, 0) != 0) {
    sodium_memzero(secure_ptr, expectedSize);
    sodium_free(secure_ptr);
    sodium_memzero(ciphertext, ciphertext_len);
    free(ciphertext);
    sodium_memzero(&state, sizeof(state));
    lean_object* error_msg = lean_mk_string("Authentication failed - file may be corrupted or tampered");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }

  sodium_memzero(ciphertext, ciphertext_len);
  free(ciphertext);
  sodium_memzero(&state, sizeof(state));

  if (decrypted_len != expectedSize || tag != crypto_secretstream_xchacha20poly1305_TAG_FINAL) {
    sodium_memzero(secure_ptr, expectedSize);
    sodium_free(secure_ptr);
    lean_object* error_msg = lean_mk_string("Decrypted key size mismatch or invalid final tag");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }

  sodium_mprotect_noaccess(secure_ptr);

  lean_object* secure_pointed = to_lean<SecurePointed>(secure_ptr);
  lean_object* secure_ref = lean_alloc_ctor(0, 1, sizeof(size_t));
  lean_ctor_set(secure_ref, 0, secure_pointed);
  lean_ctor_set_usize(secure_ref, 1, expectedSize);

  return lean_io_result_mk_ok(secure_ref);

alloy c extern "lean_sodium_store_secret_key"
def toFile {τ : @& Sodium σ} (buf : @& SecureVector τ n) (fileKey : @& SecureVector τ m) (filePath : @& System.FilePath) : IO Unit :=
  const char* path = lean_string_cstr(filePath);
  size_t key_size = lean_ctor_get_usize(buf, 1);
  void* secure_ptr = of_lean<SecurePointed>(lean_ctor_get(buf, 0));
  void* file_key_ptr = of_lean<SecurePointed>(lean_ctor_get(fileKey, 0));

  FILE* file = fopen(path, "wb");
  if (file == NULL) {
    lean_object* error_msg = lean_mk_string("Failed to create encrypted file");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }

  crypto_secretstream_xchacha20poly1305_state state;
  unsigned char header[crypto_secretstream_xchacha20poly1305_HEADERBYTES];

  sodium_mprotect_readonly(file_key_ptr);
  if (crypto_secretstream_xchacha20poly1305_init_push(&state, header, (unsigned char*)file_key_ptr) != 0) {
    sodium_mprotect_noaccess(file_key_ptr);
    fclose(file);
    lean_object* error_msg = lean_mk_string("Failed to initialize encryption");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }
  sodium_mprotect_noaccess(file_key_ptr);

  if (fwrite(header, 1, sizeof(header), file) != sizeof(header)) {
    sodium_memzero(&state, sizeof(state));
    fclose(file);
    lean_object* error_msg = lean_mk_string("Failed to write encryption header");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }

  size_t ciphertext_len = key_size + crypto_secretstream_xchacha20poly1305_ABYTES;
  unsigned char* ciphertext = (unsigned char*)malloc(ciphertext_len);
  if (ciphertext == NULL) {
    sodium_memzero(&state, sizeof(state));
    fclose(file);
    lean_object* error_msg = lean_mk_string("Failed to allocate memory for ciphertext");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }

  unsigned long long actual_ciphertext_len;
  sodium_mprotect_readonly(secure_ptr);
  if (crypto_secretstream_xchacha20poly1305_push(&state, ciphertext, &actual_ciphertext_len,
                                               (unsigned char*)secure_ptr, key_size, NULL, 0,
                                               crypto_secretstream_xchacha20poly1305_TAG_FINAL) != 0) {
    sodium_mprotect_noaccess(secure_ptr);
    sodium_memzero(ciphertext, ciphertext_len);
    free(ciphertext);
    sodium_memzero(&state, sizeof(state));
    fclose(file);
    lean_object* error_msg = lean_mk_string("Failed to encrypt key data");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }
  sodium_mprotect_noaccess(secure_ptr);

  if (fwrite(ciphertext, 1, actual_ciphertext_len, file) != actual_ciphertext_len) {
    sodium_memzero(ciphertext, ciphertext_len);
    free(ciphertext);
    sodium_memzero(&state, sizeof(state));
    fclose(file);
    lean_object* error_msg = lean_mk_string("Failed to write encrypted data");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }

  sodium_memzero(ciphertext, ciphertext_len);
  free(ciphertext);
  sodium_memzero(&state, sizeof(state));

  if (fflush(file) != 0) {
    fclose(file);
    lean_object* error_msg = lean_mk_string("Failed to flush encrypted file");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
    return lean_io_result_mk_error(io_error);
  }

  fclose(file);
  return lean_io_result_mk_ok(lean_box(0));

protected def cast {τ : Sodium σ} (h : n = m := by simp) (a : SecureVector τ n) : SecureVector τ m :=
  ⟨a.ref, a.usize, by simpa only [a.usize_rfl]⟩

def cast? {τ : Sodium σ} (a : SecureVector τ n) : Option (SecureVector τ m) :=
  if h : a.usize = m then some ⟨a.ref, a.usize, h⟩
  else none

end SecureVector

structure EntropyVector (_ : Sodium σ) where
  private mk ::
  private ref : SecurePointed.nonemptyType.type
  uoff : USize
  usize : USize

noncomputable instance {τ : Sodium σ} : Nonempty (EntropyVector τ) :=
  ⟨{ ref := Classical.choice SecurePointed.nonemptyType.property, uoff := 0, usize := 0 }⟩

noncomputable instance {τ : Sodium σ} : Inhabited (EntropyVector τ) :=
  ⟨{ ref := Classical.choice SecurePointed.nonemptyType.property, uoff := 0, usize := 0 }⟩

namespace EntropyVector

abbrev size {τ : Sodium σ} (x : EntropyVector τ) : Nat := x.usize.toNat
abbrev off {τ : Sodium σ} (x : EntropyVector τ) : Nat := x.uoff.toNat

alloy c extern "lean_sodium_randombytes_buf"
def new {τ : @& Sodium σ} (size : USize) : IO (EntropyVector τ) :=
  void* ptr = sodium_malloc(size);

  if (ptr == NULL) {
    lean_object* error_msg = lean_mk_string("Failed to allocate secure memory");
    lean_object* io_error = lean_mk_io_user_error(error_msg);
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
def refresh {τ : @& Sodium σ} (arr : EntropyVector τ) : BaseIO (EntropyVector τ) :=
  void* ptr = of_lean<SecurePointed>(lean_ctor_get(arr, 0));
  size_t size = lean_ctor_get_usize(arr, 2);

  sodium_mprotect_readwrite(ptr);
  randombytes_buf(ptr, size);
  sodium_mprotect_readonly(ptr);

  lean_ctor_set_usize(arr, 1, 0);
  return lean_io_result_mk_ok(arr);

/--
Copy a slice from an EntropyArray to a ByteArray for safe data extraction.
Extracted data is zeroed from the source EntropyArray.
-/
alloy c extern "lean_entropy_copy_slice"
def extract {τ : @& Sodium σ} (src : EntropyVector τ) (len : USize) : BaseIO (ByteArray × EntropyVector τ) :=
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

end EntropyVector

end Sodium
