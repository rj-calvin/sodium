import Sodium.Data.Chunk
import Sodium.Crypto.Monad

universe u v

open Lean Sodium FFI GenericHash Crypto

abbrev Digest := Hash Blake2b

class ToDigest (α : Type u) where
  digest : α → Digest

export ToDigest (digest)

namespace Digest

variable {α : Type u} {β : Type v}

def toName (dig : Digest) : Name := Name.str Blake2b.name dig.toBase64

instance : Inhabited Digest where
  default := GenericHash.hash default |>.cast

instance [Encodable α] : ToDigest α where
  digest x := GenericHash.hash (encode x).compress.toUTF8 |>.cast (by native_decide)

instance [ToChunks α] : ToDigest α where
  digest x := Id.run do
    let mut stream := hashInit
    for chunk in toChunks x do
      stream := hashUpdate stream chunk.compress.toUTF8
    return hashFinal stream |>.cast

instance : ToDigest Unit where
  digest _ := digest (json% null)

instance {n : Nat} : ToDigest (Fin n) where
  digest x := digest (json% $x.toNat)

instance [ToDigest α] [ToDigest β] : ToDigest (α × β) where
  digest x := Id.run do
    let mut stream := hashInit
    stream := hashUpdate stream (digest x.1).toArray
    stream := hashUpdate stream (digest x.2).toArray
    return hashFinal stream |>.cast

instance [ToDigest α] [ToDigest β] : ToDigest (α ⊕ β) where
  digest x := Id.run do
    let mut stream := hashInit
    match x with
    | .inl y =>
      stream := hashUpdate stream (digest <| json% false).toArray
      stream := hashUpdate stream (digest y).toArray
    | .inr z =>
      stream := hashUpdate stream (digest <| json% true).toArray
      stream := hashUpdate stream (digest z).toArray
    return hashFinal stream |>.cast

end Digest

class EqDigest {α : Type u} {β : Type v} [ToDigest α] [ToDigest β] (a : α) (b : β) : Prop where
  eq_digest : digest a = digest b

namespace Lean.Name

open Crypto in
def blake2b {α : Type u} [ToDigest α] (x : α) : Name := Digest.toName (digest x)

end Lean.Name
