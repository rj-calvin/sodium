import Alloy.C

open scoped Alloy.C

alloy c include <lean/lean.h> <string.h>

namespace ByteArray

/--
  Increment a ByteArray as if it represents a big-endian natural number.
  Returns the incremented ByteArray with the same length as the input.
  If overflow occurs, the result wraps around to zero.
-/
alloy c extern "lean_bytearray_increment"
def succ! (bytes : ByteArray) : ByteArray :=
  size_t size = lean_sarray_size(bytes)
  if (size == 0) {
    lean_inc_ref(bytes)
    return bytes
  }

  lean_object* result = lean_alloc_sarray(1, size, size)
  uint8_t* result_data = lean_sarray_cptr(result)
  uint8_t* input_data = lean_sarray_cptr(bytes)

  memcpy(result_data, input_data, size)

  size_t carry = 1;
  for (size_t i = size; i > 0 && carry; i -= 1) {
    size_t sum = result_data[i-1] + carry
    result_data[i-1] = (uint8_t)(sum & 0xFF)
    carry = sum >> 8
  }

  return result

/--
  Check if a ByteArray increment operation would overflow.
  Returns true if all bytes are 0xFF (maximum value).
-/
alloy c extern "lean_bytearray_would_overflow"
def wouldOverflow (bytes : ByteArray) : Bool :=
  size_t size = lean_sarray_size(bytes)
  if (size == 0) return false

  uint8_t* data = lean_sarray_cptr(bytes)

  for (size_t i = 0; i < size; i += 1) {
    if (data[i] != 0xFF) return false
  }

  return true

/--
  Increment a ByteArray with overflow checking.
  Returns `some incremented_bytes` if successful, `none` if overflow would occur.
-/
def succ? (bytes : ByteArray) : Option ByteArray :=
  if wouldOverflow bytes then none else some bytes.succ!

/--
  This theorem would need to be proven by reasoning about the C implementation
  For now, we trust that the C code correctly preserves size
-/
axiom succ!_preserves_size (bytes : ByteArray) : bytes.succ!.size = bytes.size

/-- succ? preserves size when successful -/
@[simp]
theorem succ?_preserves_size (bytes : ByteArray) :
    ∀ result, succ? bytes = some result → result.size = bytes.size := by
  intro result h
  unfold succ? at h
  split at h
  · simp at h
  · simp at h
    rw [← h]
    exact succ!_preserves_size bytes

/--
  Convert a ByteArray to USize.
  Uses wrapping arithmetic, thus preventing injective guarantees.
-/
alloy c extern "lean_bytearray_compact"
def compact! (bytes : ByteArray) : USize :=
  size_t size = lean_sarray_size(bytes)
  if (size == 0) return 0

  uint8_t* data = lean_sarray_cptr(bytes)
  size_t acc = 1

  for (size_t i = 0; i < size; i += 1) {
    size_t byte_val = data[i]
    if (byte_val < acc) {
      acc = acc * acc + byte_val
    } else {
      acc = byte_val * byte_val + acc
    }
  }

  if (acc == 0) return 1
  return acc

axiom compact!_eq_zero_iff (ns : ByteArray) :
  ns.compact! = 0 ↔ ns.size = 0

end ByteArray
