import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI.GenericHash

variable {n m : Nat} {σ : Type}

alloy c section
extern lean_obj_res lean_sodium_malloc(b_lean_obj_arg, size_t, lean_obj_arg);
extern lean_obj_res sodium_secure_to_lean(void*);
extern void* sodium_secure_of_lean(b_lean_obj_arg);
end

-- Constants for crypto_generichash (Blake2b)
def BYTES_MIN : Nat := 16
def BYTES_MAX : Nat := 64
def BYTES : Nat := 32
def KEYBYTES_MIN : Nat := 16
def KEYBYTES_MAX : Nat := 64
def KEYBYTES : Nat := 32
def SALTBYTES : Nat := 16
def PERSONALBYTES : Nat := 16

structure HashStream where
  private mk ::
  private state : ByteArray

noncomputable instance : Nonempty HashStream :=
  ⟨{ state := ByteArray.empty }⟩

noncomputable instance : Inhabited HashStream :=
  ⟨{ state := ByteArray.empty }⟩

alloy c extern "lean_crypto_generichash"
def hash (input : @& ByteArray) (key : @& Option (ByteVector KEYBYTES) := none) : ByteVector BYTES :=
  uint8_t* key_ptr = NULL;
  size_t key_len = 0;

  if (!lean_is_scalar(key)) {
    lean_object* key_data = lean_ctor_get(key, 0);
    key_ptr = lean_sarray_cptr(key_data);
    key_len = lean_sarray_size(key_data);
  }

  lean_object* output = lean_alloc_sarray(sizeof(uint8_t), crypto_generichash_BYTES, crypto_generichash_BYTES);

  crypto_generichash(
    lean_sarray_cptr(output), crypto_generichash_BYTES,
    lean_sarray_cptr(input), lean_sarray_size(input),
    key_ptr, key_len);

  return output;

alloy c extern "lean_crypto_generichash_keygen"
def hashKeygen {τ : @& Sodium σ} : IO (SecureVector τ KEYBYTES) :=
  lean_object* key_io = lean_sodium_malloc(τ, crypto_generichash_KEYBYTES, _1);

  if (lean_io_result_is_error(key_io)) {
    return key_io;
  }

  lean_object* key = lean_io_result_take_value(key_io);
  void* key_ref = sodium_secure_of_lean(lean_ctor_get(key, 0));

  sodium_mprotect_readwrite(key_ref);
  crypto_generichash_keygen((uint8_t*) key_ref);
  sodium_mprotect_noaccess(key_ref);

  return lean_io_result_mk_ok(key);

alloy c extern "lean_crypto_generichash_init"
def hashInit (key : @& Option (ByteVector KEYBYTES) := none) : HashStream :=
  uint8_t* key_ptr = NULL;
  size_t key_len = 0;

  if (!lean_is_scalar(key)) {
    lean_object* key_data = lean_ctor_get(key, 0);
    key_ptr = lean_sarray_cptr(key_data);
    key_len = lean_sarray_size(key_data);
  }

  lean_object* state_array = lean_alloc_sarray(
    sizeof(uint8_t),
    sizeof(crypto_generichash_state),
    sizeof(crypto_generichash_state));

  crypto_generichash_state* state = (crypto_generichash_state*)lean_sarray_cptr(state_array);

  crypto_generichash_init(state, key_ptr, key_len, crypto_generichash_BYTES);

  lean_object* stream = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(stream, 0, state_array);

  return stream;

alloy c extern "lean_crypto_generichash_update"
def hashUpdate (stream : HashStream) (input : @& ByteArray) : HashStream :=
  lean_object* state_array = lean_ctor_get(stream, 0);
  crypto_generichash_state* state = (crypto_generichash_state*)lean_sarray_cptr(state_array);

  crypto_generichash_update(
    state,
    lean_sarray_cptr(input),
    lean_sarray_size(input));

  return stream;

alloy c extern "lean_crypto_generichash_final"
def hashFinal (stream : @& HashStream) : ByteVector BYTES :=
  lean_object* state_array = lean_ctor_get(stream, 0);
  crypto_generichash_state* state = (crypto_generichash_state*)lean_sarray_cptr(state_array);
  lean_object* output = lean_alloc_sarray(sizeof(uint8_t), crypto_generichash_BYTES, crypto_generichash_BYTES);

  crypto_generichash_final(state, lean_sarray_cptr(output), crypto_generichash_BYTES);

  return output;

alloy c extern "lean_crypto_generichash_blake2b_salt_personal"
def hashCustom (n : Nat) (h : n ≥ BYTES_MIN ∧ n ≤ BYTES_MAX := by omega) (input : @& ByteArray)
    (salt : @& ByteVector SALTBYTES) (personal : @& ByteVector PERSONALBYTES)
    (key : Option (ByteVector KEYBYTES) := none) : ByteVector n :=
  size_t outlen_sz = lean_usize_of_nat(n);

  uint8_t* key_ptr = NULL;
  size_t key_len = 0;

  if (!lean_is_scalar(key)) {
    lean_object* key_data = lean_ctor_get(key, 0);
    key_ptr = lean_sarray_cptr(key_data);
    key_len = lean_sarray_size(key_data);
  }

  lean_object* output = lean_alloc_sarray(sizeof(uint8_t), outlen_sz, outlen_sz);

  crypto_generichash_blake2b_salt_personal(
    lean_sarray_cptr(output), outlen_sz,
    lean_sarray_cptr(input), lean_sarray_size(input),
    key_ptr, key_len,
    lean_sarray_cptr(salt),
    lean_sarray_cptr(personal));

  return output;

end Sodium.FFI.GenericHash
