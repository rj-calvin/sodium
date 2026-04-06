#ifndef LEAN_SODIUM_FFI_H
#define LEAN_SODIUM_FFI_H

#include <lean/lean.h>
#include <sodium.h>

static void noop_finalize(void* p) {
  (void)p;
}

static void secure_obj_finalize(void* ptr) {
  sodium_free(ptr);
}

static void noop_foreach(void* p, b_lean_obj_arg a) {
  (void)p; (void)a;
}

static inline lean_external_class *noop_obj_class(void) {
  static lean_external_class* g_noop_obj_class = NULL;
  if (!g_noop_obj_class) {
    g_noop_obj_class = lean_register_external_class(&noop_finalize, &noop_foreach);
  }
  return g_noop_obj_class;
}

static inline lean_external_class *secure_obj_class(void) {
  static lean_external_class* g_secure_obj_class = NULL;
  if (!g_secure_obj_class) {
    g_secure_obj_class = lean_register_external_class(&secure_obj_finalize, &noop_foreach);
  }
  return g_secure_obj_class;
}

static inline lean_object* secure_obj_to_lean(void* ptr) {
  return lean_alloc_external(secure_obj_class(), ptr);
}

static inline void* secure_obj_of_lean(b_lean_obj_arg obj) {
  return lean_get_external_data(obj);
}

lean_obj_res lean_sodium_malloc(b_lean_obj_arg tau, size_t size, lean_obj_arg world);
lean_obj_res lean_sodium_malloc_deterministic(b_lean_obj_arg tau, size_t size, b_lean_obj_arg seed, lean_obj_arg world);

#endif /* LEAN_SODIUM_FFI_H */
