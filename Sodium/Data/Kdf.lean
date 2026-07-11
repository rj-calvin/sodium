import Sodium.Data.ByteVector

namespace Sodium.KdfBlake2b

@[extern "lean_sodium_kdf_blake2b_derive"]
opaque derive (n : Nat) (idx : UInt64) (ctx : @& ByteVector 8) (key : @& ByteVector 32) : ByteVector n

end Sodium.KdfBlake2b
