import Sodium.Data.ByteVector

namespace Sodium.Curve25519

@[extern "lean_sodium_scalarmult_base"]
opaque mulBase (n : @& ByteVector 32) : Option (ByteVector 32)

@[extern "lean_sodium_scalarmult"]
opaque mul (n p : @& ByteVector 32) : Option (ByteVector 32)

end Sodium.Curve25519
