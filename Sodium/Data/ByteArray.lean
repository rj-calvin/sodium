import Alloy.C

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h> <string.h>

namespace ByteArray

alloy c extern "lean_sodium_increment"
def succ (buf : @& ByteArray) : ByteArray :=
  size_t len = lean_sarray_size(buf);
  uint8_t* buf_ptr = lean_sarray_cptr(buf);
  lean_object* out = lean_alloc_sarray(sizeof(uint8_t), len, len);
  uint8_t* out_ptr = lean_sarray_cptr(out);
  memcpy(out_ptr, buf_ptr, len);
  sodium_increment(out_ptr, len);
  return out;

alloy c extern "lean_sodium_is_zero_bytes"
def isZero (buf : @& ByteArray) : Bool :=
  size_t len = lean_sarray_size(buf);
  int result = sodium_is_zero(lean_sarray_cptr(buf), len);
  return result == 1;

alloy c extern "lean_sodium_memcmp_bytes"
def compare (b1 : @& ByteArray) (b2 : @& ByteArray) : Ordering :=
  size_t len1 = lean_sarray_size(b1);
  size_t len2 = lean_sarray_size(b2);

  if (len1 != len2) {
    return len1 < len2 ? 0 : 2;
  }

  int result = sodium_compare(lean_sarray_cptr(b1), lean_sarray_cptr(b2), len1);
  return result + 1;

instance : Ord ByteArray := ⟨compare⟩

alloy c extern "lean_sodium_bin2base64"
def toBase64 (buf : @& ByteArray) : String :=
  size_t len = lean_sarray_size(buf);
  size_t maxlen = sodium_base64_encoded_len(len, sodium_base64_VARIANT_URLSAFE);
  lean_object* b64 = lean_alloc_object(maxlen);

  sodium_bin2base64(
    (uint8_t*) b64, maxlen,
    (const uint8_t*) lean_sarray_cptr(buf), len,
    sodium_base64_VARIANT_URLSAFE
  );

  lean_object* str = lean_mk_string((uint8_t*)b64);
  lean_free_object(b64);
  return str;

alloy c extern "lean_sodium_base642bin"
def ofBase64 (str : @& String) : ByteArray :=
  const uint8_t* b64 = (const uint8_t*) lean_string_cstr(str);
  size_t b64_len = lean_string_size(str);
  size_t bin_maxlen = b64_len / 4 * 3;
  lean_object* bin = lean_alloc_sarray(sizeof(uint8_t), bin_maxlen, bin_maxlen);
  size_t bin_len;

  sodium_base642bin(
    (uint8_t*) lean_sarray_cptr(bin), bin_maxlen,
    b64, b64_len,
    NULL, &bin_len, NULL,
    sodium_base64_VARIANT_URLSAFE
  );

  lean_sarray_set_size(bin, bin_len);
  return bin;

end ByteArray
