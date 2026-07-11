#include "ffi.h"

LEAN_EXPORT lean_obj_res lean_sodium_aead_xsalsa20poly1305_encrypt(b_lean_obj_arg key, b_lean_obj_arg nonce, b_lean_obj_arg ad, b_lean_obj_arg msg) {
  size_t mlen = lean_sarray_size(msg);
  size_t clen = mlen + crypto_secretbox_MACBYTES;
  lean_object* ct = lean_alloc_sarray(sizeof(uint8_t), clen, clen);
  crypto_secretbox_easy(
    lean_sarray_cptr(ct),
    lean_sarray_cptr(msg),
    mlen,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key));
  return ct;
}

LEAN_EXPORT lean_obj_res lean_sodium_aead_xsalsa20poly1305_decrypt(b_lean_obj_arg key, b_lean_obj_arg nonce, b_lean_obj_arg ad, b_lean_obj_arg ct) {
  size_t clen = lean_sarray_size(ct);

  if (clen < crypto_secretbox_MACBYTES) {
    return lean_box(0);
  }

  size_t mlen = clen - crypto_secretbox_MACBYTES;
  lean_object* msg = lean_alloc_sarray(sizeof(uint8_t), mlen, mlen);

  if (crypto_secretbox_open_easy(
        lean_sarray_cptr(msg),
        lean_sarray_cptr(ct),
        clen,
        lean_sarray_cptr(nonce),
        lean_sarray_cptr(key)) != 0) {
    lean_dec(msg);
    return lean_box(0);
  }

  return lean_mk_option_some(msg);
}

LEAN_EXPORT lean_obj_res lean_sodium_aead_xchacha20poly1305_encrypt(b_lean_obj_arg key, b_lean_obj_arg nonce, b_lean_obj_arg ad, b_lean_obj_arg msg) {
  size_t mlen = lean_sarray_size(msg);
  size_t clen = mlen + crypto_aead_xchacha20poly1305_ietf_ABYTES;
  lean_object* ct = lean_alloc_sarray(sizeof(uint8_t), clen, clen);
  crypto_aead_xchacha20poly1305_ietf_encrypt(
    lean_sarray_cptr(ct),
    NULL,
    lean_sarray_cptr(msg),
    mlen,
    lean_sarray_cptr(ad),
    lean_sarray_size(ad),
    NULL,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key));
  return ct;
}

LEAN_EXPORT lean_obj_res lean_sodium_aead_xchacha20poly1305_decrypt(b_lean_obj_arg key, b_lean_obj_arg nonce, b_lean_obj_arg ad, b_lean_obj_arg ct) {
  size_t clen = lean_sarray_size(ct);

  if (clen < crypto_aead_xchacha20poly1305_ietf_ABYTES) {
    return lean_box(0);
  }

  size_t mlen = clen - crypto_aead_xchacha20poly1305_ietf_ABYTES;
  lean_object* msg = lean_alloc_sarray(sizeof(uint8_t), mlen, mlen);

  if (crypto_aead_xchacha20poly1305_ietf_decrypt(
        lean_sarray_cptr(msg),
        NULL,
        NULL,
        lean_sarray_cptr(ct),
        clen,
        lean_sarray_cptr(ad),
        lean_sarray_size(ad),
        lean_sarray_cptr(nonce),
        lean_sarray_cptr(key)) != 0) {
    lean_dec(msg);
    return lean_box(0);
  }

  return lean_mk_option_some(msg);
}

LEAN_EXPORT lean_obj_res lean_sodium_aead_aegis256_encrypt(b_lean_obj_arg key, b_lean_obj_arg nonce, b_lean_obj_arg ad, b_lean_obj_arg msg) {
  size_t mlen = lean_sarray_size(msg);
  size_t clen = mlen + crypto_aead_aegis256_ABYTES;
  lean_object* ct = lean_alloc_sarray(sizeof(uint8_t), clen, clen);
  crypto_aead_aegis256_encrypt(
    lean_sarray_cptr(ct),
    NULL,
    lean_sarray_cptr(msg),
    mlen,
    lean_sarray_cptr(ad),
    lean_sarray_size(ad),
    NULL,
    lean_sarray_cptr(nonce),
    lean_sarray_cptr(key));
  return ct;
}

LEAN_EXPORT lean_obj_res lean_sodium_aead_aegis256_decrypt(b_lean_obj_arg key, b_lean_obj_arg nonce, b_lean_obj_arg ad, b_lean_obj_arg ct) {
  size_t clen = lean_sarray_size(ct);

  if (clen < crypto_aead_aegis256_ABYTES) {
    return lean_box(0);
  }

  size_t mlen = clen - crypto_aead_aegis256_ABYTES;
  lean_object* msg = lean_alloc_sarray(sizeof(uint8_t), mlen, mlen);

  if (crypto_aead_aegis256_decrypt(
        lean_sarray_cptr(msg),
        NULL,
        NULL,
        lean_sarray_cptr(ct),
        clen,
        lean_sarray_cptr(ad),
        lean_sarray_size(ad),
        lean_sarray_cptr(nonce),
        lean_sarray_cptr(key)) != 0) {
    lean_dec(msg);
    return lean_box(0);
  }

  return lean_mk_option_some(msg);
}
