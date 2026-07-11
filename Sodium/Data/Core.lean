import Sodium.Data.ByteVector

namespace Sodium

@[extern "lean_sodium_core_hsalsa20"]
opaque hsalsa20 (input : @& ByteVector 32) : ByteVector 32

@[extern "lean_sodium_core_hchacha20"]
opaque hchacha20 (input : @& ByteVector 32) : ByteVector 32

@[extern "lean_sodium_blake2b32"]
opaque blake2b32 (input : @& ByteVector 32) : ByteVector 32

end Sodium
