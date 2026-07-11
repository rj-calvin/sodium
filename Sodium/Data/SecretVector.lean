import Sodium.Data.ByteVector

universe u

opaque SecurePointed : NonemptyType

namespace Sodium

structure SecretVector (n : USize) where
  private mk ::
  private ref : SecurePointed.type
  usize : USize
  usize_rfl : usize = n

namespace SecretVector

variable {n : USize}

noncomputable instance : Nonempty (SecretVector n) :=
  ⟨{ ref := Classical.choice SecurePointed.property, usize := n, usize_rfl := rfl }⟩

@[extern "lean_sodium_malloc"]
opaque randomBytes (n : USize) : IO (SecretVector n)

@[extern "lean_sodium_malloc_deterministic"]
opaque seededBytes (n : USize) (seed : @& ByteVector 32) : IO (SecretVector n)

@[extern "lean_sodium_secure_obj_is_zero"]
opaque isZero (obj : @& SecretVector n) : Bool

@[extern "lean_sodium_secure_obj_compare"]
opaque compare (obj1 obj2 : @& SecretVector n) : Ordering

instance : Ord (SecretVector n) := ⟨compare⟩
instance : BEq (SecretVector n) := ⟨(compare · · == .eq)⟩
instance : LT (SecretVector n) := ⟨(compare · · == .lt)⟩

end SecretVector

structure RandomBytes where
  private mk ::
  private ref : SecurePointed.type
  uoff : USize
  usize : USize

namespace RandomBytes

noncomputable instance : Nonempty RandomBytes :=
  ⟨{ ref := Classical.choice SecurePointed.property, uoff := 0, usize := 0 }⟩

@[extern "lean_sodium_randombytes_buf"]
opaque randomBytes (n : USize) : IO RandomBytes

@[extern "lean_sodium_randombytes_buf_deterministic"]
opaque seededBytes (n : USize) (seed : @& ByteVector 32) : IO RandomBytes

@[extern "lean_sodium_randombytes_buf_refresh"]
opaque refresh (bytes : RandomBytes) : BaseIO RandomBytes

@[extern "lean_sodium_randombytes_buf_refresh_deterministic"]
opaque seededRefresh (bytes : RandomBytes) (seed : @& ByteVector 32) : BaseIO RandomBytes

@[extern "lean_sodium_randombytes_buf_extract_slice"]
opaque extractSlice (bytes : RandomBytes) (n : USize) : BaseIO (ByteArray × RandomBytes)

end RandomBytes

end Sodium
