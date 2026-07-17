import Sodium.Crypto.Box
import Sodium.Data.GenericHash

namespace Sodium.Crypto

open Theory

def kxKdf (q cpk spk : ByteVector 32) : ByteVector 32 × ByteVector 32 :=
  let h := genericHash (q.toByteArray ++ cpk.toByteArray ++ spk.toByteArray)
  (h.take 32 (by omega), (h.drop 32).cast (by omega))

def kx : Kx := dhKx Curve25519.spec 32 kxKdf

end Sodium.Crypto
