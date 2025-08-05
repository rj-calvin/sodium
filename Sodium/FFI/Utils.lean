import Sodium.FFI.Basic

open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h> <string.h>

namespace Sodium.FFI

alloy c extern "lean_sodium_compare"
def sodiumCompare (b1 : ByteArray) (b2 : ByteArray) : IO Int32 :=
  size_t len1 = lean_sarray_size(b1)
  size_t len2 = lean_sarray_size(b2)
  if (len1 != len2) {
    lean_object* error_msg = lean_mk_string("Buffer sizes must be equal for comparison")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  int result = sodium_compare(lean_sarray_cptr(b1), lean_sarray_cptr(b2), len1)
  return lean_io_result_mk_ok(lean_box(result))

alloy c extern "lean_sodium_is_zero"
def sodiumIsZero (buffer : ByteArray) : BaseIO Bool :=
  size_t len = lean_sarray_size(buffer)
  int result = sodium_is_zero(lean_sarray_cptr(buffer), len)
  uint8_t is_zero = (result == 1)
  return lean_io_result_mk_ok(lean_box(is_zero))

alloy c extern "lean_sodium_increment"
def sodiumIncrement (buffer : ByteArray) : ByteArray :=
  size_t len = lean_sarray_size(buffer)
  sodium_increment(lean_sarray_cptr(buffer), len)
  lean_inc_ref(buffer)
  return buffer

alloy c extern "lean_crypto_verify_16"
def cryptoVerify16 (x : ByteArray) (y : ByteArray) : IO Bool :=
  size_t x_size = lean_sarray_size(x)
  size_t y_size = lean_sarray_size(y)
  if (x_size != 16 || y_size != 16) {
    lean_object* error_msg = lean_mk_string("Both buffers must be exactly 16 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  int result = crypto_verify_16(lean_sarray_cptr(x), lean_sarray_cptr(y))
  uint8_t is_equal = (result == 0)
  return lean_io_result_mk_ok(lean_box(is_equal))

alloy c extern "lean_crypto_verify_32"
def cryptoVerify32 (x : ByteArray) (y : ByteArray) : IO Bool :=
  size_t x_size = lean_sarray_size(x)
  size_t y_size = lean_sarray_size(y)
  if (x_size != 32 || y_size != 32) {
    lean_object* error_msg = lean_mk_string("Both buffers must be exactly 32 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  int result = crypto_verify_32(lean_sarray_cptr(x), lean_sarray_cptr(y))
  uint8_t is_equal = (result == 0)
  return lean_io_result_mk_ok(lean_box(is_equal))

alloy c extern "lean_crypto_verify_64"
def cryptoVerify64 (x : ByteArray) (y : ByteArray) : IO Bool :=
  size_t x_size = lean_sarray_size(x)
  size_t y_size = lean_sarray_size(y)
  if (x_size != 64 || y_size != 64) {
    lean_object* error_msg = lean_mk_string("Both buffers must be exactly 64 bytes")
    lean_object* io_error = lean_alloc_ctor(7, 1, 0)
    lean_ctor_set(io_error, 0, error_msg)
    return lean_io_result_mk_error(io_error)
  }

  int result = crypto_verify_64(lean_sarray_cptr(x), lean_sarray_cptr(y))
  uint8_t is_equal = (result == 0)
  return lean_io_result_mk_ok(lean_box(is_equal))

alloy c extern "lean_sodium_bin2base64"
def sodiumBin2Base64 (bin : ByteArray) : String :=
  size_t bin_len = lean_sarray_size(bin)
  size_t b64_maxlen = sodium_base64_encoded_len(bin_len, sodium_base64_VARIANT_ORIGINAL)

  lean_object* temp_object = lean_alloc_object(b64_maxlen)
  char* b64 = (char*)temp_object

  char* result = sodium_bin2base64(b64, b64_maxlen,
                                   (const unsigned char*)lean_sarray_cptr(bin), bin_len,
                                   sodium_base64_VARIANT_ORIGINAL)

  lean_object* lean_string = lean_mk_string(b64)
  lean_free_object(temp_object)
  return lean_string

alloy c extern "lean_sodium_bin2base64_url"
def sodiumBin2Base64Url (bin : ByteArray) : String :=
  size_t bin_len = lean_sarray_size(bin)
  size_t b64_maxlen = sodium_base64_encoded_len(bin_len, sodium_base64_VARIANT_URLSAFE_NO_PADDING)

  lean_object* temp_object = lean_alloc_object(b64_maxlen)
  char* b64 = (char*)temp_object

  char* result = sodium_bin2base64(b64, b64_maxlen,
                                   (const unsigned char*)lean_sarray_cptr(bin), bin_len,
                                   sodium_base64_VARIANT_URLSAFE_NO_PADDING)

  lean_object* lean_string = lean_mk_string(b64)
  lean_free_object(temp_object)
  return lean_string

alloy c extern "lean_sodium_base642bin"
def sodiumBase642Bin (b64 : String) : ByteArray :=
  const char* b64_cstr = lean_string_cstr(b64)
  size_t b64_len = strlen(b64_cstr)
  size_t bin_maxlen = b64_len

  lean_object* temp_object = lean_alloc_object(bin_maxlen)
  unsigned char* bin = (unsigned char*)temp_object

  size_t bin_len;
  const char* b64_end;
  int result = sodium_base642bin(bin, bin_maxlen, b64_cstr, b64_len,
                                 NULL, &bin_len, &b64_end,
                                 sodium_base64_VARIANT_ORIGINAL)

  lean_object* byte_array = lean_alloc_sarray(sizeof(unsigned char), bin_len, bin_len)
  memcpy(lean_sarray_cptr(byte_array), bin, bin_len)
  lean_free_object(temp_object)
  return byte_array

alloy c extern "lean_sodium_base642bin_url"
def sodiumBase642BinUrl (b64 : String) : ByteArray :=
  const char* b64_cstr = lean_string_cstr(b64)
  size_t b64_len = strlen(b64_cstr)
  size_t bin_maxlen = b64_len

  lean_object* temp_object = lean_alloc_object(bin_maxlen)
  unsigned char* bin = (unsigned char*)temp_object

  size_t bin_len;
  const char* b64_end;
  int result = sodium_base642bin(bin, bin_maxlen, b64_cstr, b64_len,
                                 NULL, &bin_len, &b64_end,
                                 sodium_base64_VARIANT_URLSAFE_NO_PADDING)

  lean_object* byte_array = lean_alloc_sarray(sizeof(unsigned char), bin_len, bin_len)
  memcpy(lean_sarray_cptr(byte_array), bin, bin_len)
  lean_free_object(temp_object)
  return byte_array

end Sodium.FFI
