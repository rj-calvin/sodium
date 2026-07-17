import Sodium.Crypto.Box
import Sodium.Data.GenericHash

namespace Sodium.Crypto

open Theory

def blake2b : Hash where
  name := `blake2b
  outBytes := 64
  keyBytes := 32
  hash := fun input key => genericHash input key

def signRistretto255 : Sign := schnorr Ristretto.spec blake2b rfl

end Sodium.Crypto
