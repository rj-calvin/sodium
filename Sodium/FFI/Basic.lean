import Alloy.C
open scoped Alloy.C

alloy c include <sodium.h> <lean/lean.h>

namespace Sodium.FFI

alloy c extern "lean_sodium_init"
def sodiumInit : BaseIO Int32 :=
  int result = sodium_init()
  return lean_io_result_mk_ok(lean_box(result))

alloy c extern "lean_randombytes_buf"
def randomBytes (size : USize) : BaseIO ByteArray :=
  lean_object* arr = lean_alloc_sarray(sizeof(unsigned char), size, size)
  randombytes(lean_sarray_cptr(arr), size)
  return lean_io_result_mk_ok(arr)

alloy c extern "lean_randombytes_uniform"
def randomUInt32 (sup : UInt32) : BaseIO UInt32 :=
  uint32_t result = randombytes_uniform(sup)
  return lean_io_result_mk_ok(lean_box_uint32(result))

end Sodium.FFI
