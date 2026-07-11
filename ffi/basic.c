#include "ffi.h"
#include <string.h>
#include <lean/lean.h>
#include <sodium.h>

LEAN_EXPORT lean_obj_res lean_sodium_init(lean_obj_arg world) {
  if (sodium_init() < 0) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("Failed to initialize LibSodium")));
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sodium_malloc(size_t size, lean_obj_arg world) {
  void* ptr = sodium_malloc(size);
  randombytes_buf(ptr, size);
  sodium_mprotect_noaccess(ptr);
  lean_object* ret = lean_alloc_ctor(0, 1, sizeof(size_t));
  lean_ctor_set(ret, 0, secure_obj_to_lean(ptr));
  lean_ctor_set_usize(ret, 1, size);
  return lean_io_result_mk_ok(ret);
}

LEAN_EXPORT lean_obj_res lean_sodium_malloc_deterministic(size_t size, b_lean_obj_arg seed, lean_obj_arg world) {
  void* ptr = sodium_malloc(size);
  randombytes_buf_deterministic(ptr, size, lean_sarray_cptr(seed));
  sodium_mprotect_noaccess(ptr);
  lean_object* ret = lean_alloc_ctor(0, 1, sizeof(size_t));
  lean_ctor_set(ret, 0, secure_obj_to_lean(ptr));
  lean_ctor_set_usize(ret, 1, size);
  return lean_io_result_mk_ok(ret);
}

LEAN_EXPORT uint8_t lean_sodium_secure_obj_is_zero(size_t size, b_lean_obj_arg obj) {
  void* ptr = secure_obj_of_lean(lean_ctor_get(obj, 0));
  sodium_mprotect_readonly(ptr);
  int ret = sodium_is_zero(ptr, size);
  sodium_mprotect_noaccess(ptr);
  return ret == 1;
}

LEAN_EXPORT uint8_t lean_sodium_secure_obj_compare(size_t size, b_lean_obj_arg obj1, b_lean_obj_arg obj2) {
  void* ptr1 = secure_obj_of_lean(lean_ctor_get(obj1, 0));
  void* ptr2 = secure_obj_of_lean(lean_ctor_get(obj2, 0));
  sodium_mprotect_readonly(ptr1);
  sodium_mprotect_readonly(ptr2);
  int ret = sodium_compare(ptr1, ptr2, size);
  sodium_mprotect_noaccess(ptr1);
  sodium_mprotect_noaccess(ptr2);
  return ret + 1;
}

LEAN_EXPORT lean_obj_res lean_sodium_randombytes_buf(size_t size, lean_obj_arg world) {
  void* ptr = sodium_malloc(size);
  randombytes_buf(ptr, size);
  sodium_mprotect_readonly(ptr);
  lean_object* ret = lean_alloc_ctor(0, 1, 2 * sizeof(size_t));
  lean_ctor_set(ret, 0, secure_obj_to_lean(ptr));
  lean_ctor_set_usize(ret, 1, 0);
  lean_ctor_set_usize(ret, 2, size);
  return lean_io_result_mk_ok(ret);
}

LEAN_EXPORT lean_obj_res lean_sodium_randombytes_buf_deterministic(size_t size, b_lean_obj_arg seed, lean_obj_arg world) {
  void* ptr = sodium_malloc(size);
  randombytes_buf_deterministic(ptr, size, lean_sarray_cptr(seed));
  sodium_mprotect_readonly(ptr);
  lean_object* ret = lean_alloc_ctor(0, 1, 2 * sizeof(size_t));
  lean_ctor_set(ret, 0, secure_obj_to_lean(ptr));
  lean_ctor_set_usize(ret, 1, 0);
  lean_ctor_set_usize(ret, 2, size);
  return lean_io_result_mk_ok(ret);
}

LEAN_EXPORT lean_obj_res lean_sodium_randombytes_buf_refresh(lean_obj_arg buf, lean_obj_arg world) {
  size_t size = lean_ctor_get_usize(buf, 2);
  void* ptr = secure_obj_of_lean(lean_ctor_get(buf, 0));
  sodium_mprotect_readwrite(ptr);
  randombytes_buf(ptr, size);
  sodium_mprotect_readonly(ptr);
  lean_ctor_set_usize(buf, 1, 0);
  return buf;
}

LEAN_EXPORT lean_obj_res lean_sodium_randombytes_buf_refresh_deterministic(lean_obj_arg buf, b_lean_obj_arg seed, lean_obj_arg world) {
  size_t size = lean_ctor_get_usize(buf, 2);
  void* ptr = secure_obj_of_lean(lean_ctor_get(buf, 0));
  sodium_mprotect_readwrite(ptr);
  randombytes_buf_deterministic(ptr, size, lean_sarray_cptr(seed));
  sodium_mprotect_readonly(ptr);
  lean_ctor_set_usize(buf, 1, 0);
  return buf;
}

LEAN_EXPORT lean_obj_res lean_sodium_randombytes_buf_extract_slice(lean_obj_arg buf, size_t len, lean_obj_arg world) {
  size_t off = lean_ctor_get_usize(buf, 1);
  size_t size = lean_ctor_get_usize(buf, 2);
  len = (off >= size) ? 0 : (off + len > size) ? (size - off) : len;

  if (len == 0) {
    lean_obj_res pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_alloc_sarray(sizeof(uint8_t), 0, 0));
    lean_ctor_set(pair, 1, buf);
    return pair;
  }

  lean_object* out = lean_alloc_sarray(sizeof(uint8_t), len, len);
  uint8_t* ptr = secure_obj_of_lean(lean_ctor_get(buf, 0));
  memcpy(lean_sarray_cptr(out), ptr + off, len);
  sodium_mprotect_readwrite(ptr);
  sodium_memzero(ptr + off, len);
  sodium_mprotect_readonly(ptr);
  lean_ctor_set_usize(buf, 1, off + len);
  lean_object* pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, out);
  lean_ctor_set(pair, 1, buf);
  return pair;
}

LEAN_EXPORT uint8_t lean_sodium_bytes_compare(size_t size, b_lean_obj_arg bytes1, b_lean_obj_arg bytes2) {
  return sodium_compare(lean_sarray_cptr(bytes1), lean_sarray_cptr(bytes2), size) + 1;
}

LEAN_EXPORT uint8_t lean_sodium_bytes_dec_eq(size_t size, b_lean_obj_arg bytes1, b_lean_obj_arg bytes2) {
  return sodium_compare(lean_sarray_cptr(bytes1), lean_sarray_cptr(bytes2), size) == 0;
}

LEAN_EXPORT uint8_t lean_sodium_bytes_dec_lt(size_t size, b_lean_obj_arg bytes1, b_lean_obj_arg bytes2) {
  return sodium_compare(lean_sarray_cptr(bytes1), lean_sarray_cptr(bytes2), size) == -1;
}

LEAN_EXPORT lean_obj_res lean_sodium_bytes_to_base64(b_lean_obj_arg buf) {
  size_t len = lean_sarray_size(buf);
  size_t maxlen = sodium_base64_encoded_len(len, sodium_base64_VARIANT_URLSAFE);
  lean_object* b64 = lean_alloc_string(1, maxlen, 0);
  sodium_bin2base64(lean_to_string(b64)->m_data, maxlen, lean_sarray_cptr(buf), len, sodium_base64_VARIANT_URLSAFE);
  len = strlen(lean_to_string(b64)->m_data);
  lean_to_string(b64)->m_size = len + 1;
  lean_to_string(b64)->m_length = len;
  return b64;
}

LEAN_EXPORT lean_obj_res lean_sodium_bytes_of_base64(b_lean_obj_arg str) {
  size_t size = lean_string_size(str);
  size_t maxlen = size / 4 * 3 + 1;
  size_t binlen;
  lean_object* bin = lean_alloc_sarray(sizeof(uint8_t), maxlen, maxlen);

  if (sodium_base642bin(lean_sarray_cptr(bin), maxlen, lean_string_cstr(str), size, " \r\n\t", &binlen, NULL, sodium_base64_VARIANT_URLSAFE) != 0) {
    lean_dec(bin);
    return lean_box(0);
  }

  lean_sarray_set_size(bin, binlen);
  lean_object* some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, bin);
  return some;
}

LEAN_EXPORT lean_obj_res lean_sodium_bytes_increment(lean_obj_arg bytes, lean_obj_arg world) {
  sodium_increment(lean_sarray_cptr(bytes), lean_sarray_size(bytes));
  return bytes;
}

LEAN_EXPORT lean_obj_res lean_sodium_bytes_increment_vec(size_t n, lean_obj_arg bytes, lean_obj_arg world) {
  sodium_increment(lean_sarray_cptr(bytes), lean_sarray_size(bytes));
  return bytes;
}
