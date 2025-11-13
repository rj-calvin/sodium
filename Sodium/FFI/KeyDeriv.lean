import Sodium.FFI.Basic

open scoped Alloy.C

universe u

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI.KeyDeriv

variable {σ : Type u}

alloy c section
extern lean_obj_res lean_sodium_malloc(b_lean_obj_arg, size_t, lean_obj_arg);
extern lean_obj_res sodium_secure_to_lean(void*);
extern void* sodium_secure_of_lean(b_lean_obj_arg);
end

-- Constants for crypto_kdf
def KEYBYTES : Nat := 32
def CONTEXTBYTES : Nat := 8
def BYTES_DEFAULT : Nat := 32
def BYTES_MIN : Nat := 16
def BYTES_MAX : Nat := 64

alloy c extern "lean_crypto_kdf_keygen"
def keygen {τ : @& Sodium σ} : IO (SecretVector τ KEYBYTES) :=
  lean_object* master_key_io = lean_sodium_malloc(τ, crypto_kdf_KEYBYTES, _1);

  if (lean_io_result_is_error(master_key_io)) {
    return master_key_io;
  }

  lean_object* master_key = lean_io_result_take_value(master_key_io);
  void* master_key_ref = sodium_secure_of_lean(lean_ctor_get(master_key, 0));

  sodium_mprotect_readwrite(master_key_ref);
  crypto_kdf_keygen((uint8_t*) master_key_ref);
  sodium_mprotect_noaccess(master_key_ref);

  return lean_io_result_mk_ok(master_key);

alloy c extern "lean_crypto_kdf_derive_from_key"
def derive {τ : @& Sodium σ}
    (subkeyLen : USize)
    (subkeyId : UInt64)
    (context : @& ByteVector CONTEXTBYTES)
    (masterKey : @& SecretVector τ KEYBYTES)
    : IO (SecretVector τ subkeyLen) :=
  size_t master_key_len = lean_ctor_get_usize(masterKey, 1);

  if (
    master_key_len != crypto_kdf_KEYBYTES ||
    subkeyLen < crypto_kdf_BYTES_MIN ||
    subkeyLen > crypto_kdf_BYTES_MAX
  ) {
    lean_object* error_msg = lean_mk_string("spec violation in lean_crypto_kdf_derive_from_key");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  lean_object* secret_subkey_io = lean_sodium_malloc(τ, subkeyLen, _5);

  if (lean_io_result_is_error(secret_subkey_io)) {
    return secret_subkey_io;
  }

  lean_object* secret_subkey = lean_io_result_take_value(secret_subkey_io);
  void* secret_subkey_ref = sodium_secure_of_lean(lean_ctor_get(secret_subkey, 0));
  void* master_key_ref = sodium_secure_of_lean(lean_ctor_get(masterKey, 0));

  sodium_mprotect_readwrite(secret_subkey_ref);
  sodium_mprotect_readonly(master_key_ref);

  int err = crypto_kdf_derive_from_key(
    (uint8_t*) secret_subkey_ref, subkeyLen,
    subkeyId,
    (char*) lean_sarray_cptr(context),
    (uint8_t*) master_key_ref);

  sodium_mprotect_noaccess(secret_subkey_ref);
  sodium_mprotect_noaccess(master_key_ref);

  if (err != 0) {
    lean_dec(secret_subkey);
    lean_object* error_msg = lean_mk_string("crypto_kdf_derive_from_key failed");
    lean_object* io_error = lean_alloc_ctor(7, 1, 0);
    lean_ctor_set(io_error, 0, error_msg);
    return lean_io_result_mk_error(io_error);
  }

  return lean_io_result_mk_ok(secret_subkey);

end Sodium.FFI.KeyDeriv
