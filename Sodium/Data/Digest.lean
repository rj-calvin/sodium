import Sodium.Data.Encodable

namespace Sodium

structure DigestStream where
  private mk ::
  private state : ByteArray

noncomputable instance : Nonempty DigestStream := ⟨⟨.empty⟩⟩

@[extern "lean_sodium_generichash"]
opaque genericHash (input : @& ByteArray) (key : @& Option (ByteVector 32) := none) : ByteVector 64

namespace DigestStream

@[extern "lean_sodium_generichash_init"]
opaque new (key : @& Option (ByteVector 32) := none) : DigestStream

@[extern "lean_sodium_generichash_update"]
opaque add (state : DigestStream) (input : @& ByteArray) : DigestStream

@[extern "lean_sodium_generichash_final"]
opaque get (state : @& DigestStream) : ByteVector 64

end DigestStream

def digest (x : α) (key : Option (ByteVector 32) := none) [Encodable α] : ByteVector 64 :=
  genericHash (encode x).compress.toByteArray key

end Sodium
