import Sodium.Data.ByteVector

namespace Sodium.Ristretto255

@[extern "lean_sodium_scalarmult_ristretto255_base"]
opaque mulBase (n : @& ByteVector 32) : Option (ByteVector 32)

@[extern "lean_sodium_scalarmult_ristretto255"]
opaque mul (n p : @& ByteVector 32) : Option (ByteVector 32)

@[extern "lean_sodium_core_ristretto255_add"]
opaque add (p q : @& ByteVector 32) : Option (ByteVector 32)

@[extern "lean_sodium_core_ristretto255_sub"]
opaque sub (p q : @& ByteVector 32) : Option (ByteVector 32)

@[extern "lean_sodium_core_ristretto255_from_hash"]
opaque fromHash (r : @& ByteVector 64) : ByteVector 32

@[extern "lean_sodium_core_ristretto255_is_valid_point"]
opaque isValidPoint (p : @& ByteVector 32) : Bool

@[extern "lean_sodium_core_ristretto255_scalar_reduce"]
opaque scalarReduce (s : @& ByteVector 64) : ByteVector 32

@[extern "lean_sodium_core_ristretto255_scalar_add"]
opaque scalarAdd (x y : @& ByteVector 32) : ByteVector 32

@[extern "lean_sodium_core_ristretto255_scalar_mul"]
opaque scalarMul (x y : @& ByteVector 32) : ByteVector 32

@[extern "lean_sodium_core_ristretto255_scalar_negate"]
opaque scalarNeg (s : @& ByteVector 32) : ByteVector 32

end Sodium.Ristretto255
