import Sodium.Theory.Basic
import Sodium.Data.Kdf

namespace Sodium.Crypto

open Sodium.Theory

def kdfBlake2b : Kdf where
  name := `blake2b
  keyBytes := 32
  contextBytes := 8
  derive := KdfBlake2b.derive

end Sodium.Crypto
