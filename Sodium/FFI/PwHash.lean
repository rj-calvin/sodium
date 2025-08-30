import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h> <string.h>

namespace Sodium.FFI.PwHash

variable {n : Nat} {σ : Type}

alloy c section
extern lean_obj_res lean_sodium_malloc(b_lean_obj_arg, size_t, lean_obj_arg);
extern lean_obj_res sodium_secure_to_lean(void*);
extern void* sodium_secure_of_lean(b_lean_obj_arg);
end

-- Constants for crypto_pwhash (Argon2id default)
def SALTBYTES : Nat := 16
def STRBYTES : Nat := 128
def PASSWD_MIN : Nat := 0
def PASSWD_MAX : Nat := 4294967295

-- Opslimit constants
def OPSLIMIT_INTERACTIVE : Nat := 2
def OPSLIMIT_MODERATE : Nat := 3
def OPSLIMIT_SENSITIVE : Nat := 4

-- Memlimit constants (in bytes)
def MEMLIMIT_INTERACTIVE : Nat := 67108864
def MEMLIMIT_MODERATE : Nat := 268435456
def MEMLIMIT_SENSITIVE : Nat := 1073741824

-- Algorithm identifiers
def ALG_ARGON2ID13 : Nat := 2
def ALG_ARGON2I13 : Nat := 1
def ALG_DEFAULT : Nat := ALG_ARGON2ID13

-- Output size limits
def BYTES_MIN : Nat := 16
def BYTES_MAX : Nat := 4294967295

-- Password hashing for storage/verification (Argon2id default)
alloy c extern "lean_crypto_pwhash_str"
def str {τ : @& Sodium σ} (password : @& SecureVector τ n) (opslimit : USize) (memlimit : USize) : IO String :=
  size_t password_len = lean_ctor_get_usize(password, 1);

  if (password_len > crypto_pwhash_PASSWD_MAX) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_pwhash_str");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  if (opslimit < crypto_pwhash_OPSLIMIT_INTERACTIVE ||
      memlimit < crypto_pwhash_MEMLIMIT_INTERACTIVE) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_pwhash_str");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  char hash_str[crypto_pwhash_STRBYTES];
  void* password_ptr = sodium_secure_of_lean(lean_ctor_get(password, 0));

  sodium_mprotect_readonly(password_ptr);

  int err = crypto_pwhash_str(
    hash_str,
    (char*) password_ptr, password_len,
    opslimit, memlimit);

  sodium_mprotect_noaccess(password_ptr);

  if (err != 0) {
    sodium_memzero(hash_str, sizeof(hash_str));
    lean_object* error_msg = lean_mk_string("crypto_pwhash_str failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* result_str = lean_mk_string(hash_str);
  sodium_memzero(hash_str, sizeof(hash_str));

  return lean_io_result_mk_ok(result_str);

-- Password verification against stored hash
alloy c extern "lean_crypto_pwhash_str_verify"
def strVerify {τ : @& Sodium σ} (hashStr : String) (password : @& SecureVector τ n) : IO Bool :=
  size_t password_len = lean_ctor_get_usize(password, 1);

  if (password_len > crypto_pwhash_PASSWD_MAX) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_pwhash_str_verify");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  void* password_ptr = sodium_secure_of_lean(lean_ctor_get(password, 0));

  sodium_mprotect_readonly(password_ptr);

  int result = crypto_pwhash_str_verify(
    lean_string_cstr(hashStr),
    (char*) password_ptr, password_len);

  sodium_mprotect_noaccess(password_ptr);

  lean_object* bool_result = lean_box(result == 0 ? 1 : 0);
  return lean_io_result_mk_ok(bool_result);

-- Key derivation from password to secure array
alloy c extern "lean_crypto_pwhash"
def derive {τ : @& Sodium σ} (password : @& SecureVector τ n) (salt : @& ByteVector SALTBYTES)
    (outLen : USize) (opslimit : USize := OPSLIMIT_INTERACTIVE) (memlimit : USize := MEMLIMIT_INTERACTIVE) (alg : USize := ALG_DEFAULT) : IO (SecureVector τ outLen) :=
  size_t password_len = lean_ctor_get_usize(password, 1);
  size_t salt_len = lean_sarray_byte_size(salt);

  if (
    password_len > crypto_pwhash_PASSWD_MAX ||
    salt_len != crypto_pwhash_SALTBYTES ||
    outLen < crypto_pwhash_BYTES_MIN ||
    outLen > crypto_pwhash_BYTES_MAX ||
    opslimit < crypto_pwhash_OPSLIMIT_INTERACTIVE ||
    memlimit < crypto_pwhash_MEMLIMIT_INTERACTIVE
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_pwhash_derive_secret");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* secret_key_io = lean_sodium_malloc(τ, outLen, _8);

  if (lean_io_result_is_error(secret_key_io)) {
    return secret_key_io;
  }

  lean_object* secret_key = lean_io_result_take_value(secret_key_io);
  void* secret_key_ref = sodium_secure_of_lean(lean_ctor_get(secret_key, 0));
  void* password_ref = sodium_secure_of_lean(lean_ctor_get(password, 0));

  sodium_mprotect_readwrite(secret_key_ref);
  sodium_mprotect_readonly(password_ref);

  int err = crypto_pwhash(
    (uint8_t*) secret_key_ref, outLen,
    (char*) password_ref, password_len,
    lean_sarray_cptr(salt),
    opslimit, memlimit, alg);

  sodium_mprotect_noaccess(secret_key_ref);
  sodium_mprotect_noaccess(password_ref);

  if (err != 0) {
    lean_dec(secret_key);
    lean_object* error_msg = lean_mk_string("crypto_pwhash failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  return lean_io_result_mk_ok(secret_key);

end Sodium.FFI.PwHash
