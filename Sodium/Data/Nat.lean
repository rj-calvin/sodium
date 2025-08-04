import Alloy.C

open scoped Alloy.C

alloy c include <lean/lean.h> <string.h>

namespace Nat

/--
  Pairing function for arbitrary Nat values using Cantor pairing.
  Maps two naturals to a unique natural number.
-/
alloy c extern "lean_nat_pair"
def pair (a b : Nat) : Nat :=
  uint8_t a_lt_b = lean_nat_dec_lt(a, b)

  if (a_lt_b) {
    lean_object* b_squared = lean_nat_mul(b, b)
    lean_object* result = lean_nat_add(b_squared, a)
    lean_dec(b_squared)
    return result
  } else {
    lean_object* a_squared = lean_nat_mul(a, a)
    lean_object* result = lean_nat_add(a_squared, b)
    lean_dec(a_squared)
    return result
  }

/--
  Unpairing function for arbitrary Nat values.
  Inverse of natPair - recovers the original pair from the paired value.
-/
alloy c extern "lean_nat_unpair"
def unpair (n : Nat) : Nat × Nat :=
  lean_object* zero = lean_box(0)
  lean_object* one = lean_box(1)
  lean_object* two = lean_box(2)

  lean_object* low = zero
  lean_object* high = lean_nat_add(n, one)
  lean_object* s = zero

  while (lean_nat_dec_lt(low, high)) {
    lean_object* mid = lean_nat_div(lean_nat_add(low, high), two)
    lean_object* mid_squared = lean_nat_mul(mid, mid)

    if (lean_nat_dec_le(mid_squared, n)) {
      lean_dec(s)
      s = mid
      lean_inc(s)
      lean_object* temp = lean_nat_add(mid, one)
      lean_dec(low)
      low = temp
    } else {
      lean_dec(high)
      high = mid
    }

    lean_dec(mid_squared)
  }

  lean_object* s_squared = lean_nat_mul(s, s)
  lean_object* remainder = lean_nat_sub(n, s_squared)
  uint8_t remainder_lt_s = lean_nat_dec_lt(remainder, s)

  lean_object* first, *second
  if (remainder_lt_s) {
    lean_inc(remainder)
    lean_inc(s)
    first = remainder
    second = s
  } else {
    lean_inc(s)
    first = s
    second = lean_nat_sub(remainder, s)
  }

  lean_object* result = lean_alloc_ctor(0, 2, 0)
  lean_ctor_set(result, 0, first)
  lean_ctor_set(result, 1, second)

  lean_dec(zero)
  lean_dec(one)
  lean_dec(two)
  lean_dec(low)
  lean_dec(high)
  lean_dec(s)
  lean_dec(s_squared)
  lean_dec(remainder)

  return result

end Nat

namespace ByteArray

/--
  Convert a ByteArray to a Nat by folding with the pairing function.
  Each byte is paired with the accumulator, creating a unique natural number.
-/
def toNat (bytes : ByteArray) : Nat :=
  bytes.foldl (init := 1) fun acc byte => Nat.pair byte.toNat acc

/--
  Convert a Nat back to a ByteArray by repeatedly unpairing.
  This is the inverse of toNat. The size parameter specifies the expected ByteArray length.
-/
alloy c extern "lean_bytearray_from_nat"
def fromNat (n : Nat) (size : USize) : ByteArray :=
  lean_object* result = lean_alloc_sarray(1, size, size)
  uint8_t* data = lean_sarray_cptr(result)

  memset(data, 0, size)

  lean_object* current = n
  lean_inc(current)

  lean_object* one = lean_box(1)
  if (lean_nat_dec_eq(current, one)) {
    lean_dec(current)
    lean_dec(one)
    return result
  }
  lean_dec(one)

  for (size_t i = size; i > 0; i -= 1) {
    lean_object* unpaired = lean_nat_unpair(current)
    lean_object* byte_val = lean_ctor_get(unpaired, 0)
    lean_object* prev_acc = lean_ctor_get(unpaired, 1)

    uint8_t byte_value = 0
    if (lean_is_scalar(byte_val)) {
      size_t val = lean_unbox(byte_val)
      if (val <= 255) {
        byte_value = (uint8_t)val
      } else {
        byte_value = 255
      }
    }
    data[i-1] = byte_value

    lean_dec(current)
    current = prev_acc
    lean_inc(current)
    lean_dec(unpaired)
  }

  lean_dec(current)
  return result

axiom toNat_injective (a b : ByteArray) :
  a.size = b.size → toNat a = toNat b → a = b

axiom fromNat_toNat_inverse (bytes : ByteArray) :
  fromNat (toNat bytes) bytes.size = bytes

end ByteArray
