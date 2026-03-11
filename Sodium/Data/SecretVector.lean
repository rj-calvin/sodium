import Sodium.Init
import Sodium.Data.ByteVector

universe u

opaque SecurePointed : NonemptyType

namespace Sodium

structure SecretVector {σ} (_ : Sodium σ) (n : USize) where
  private mk ::
  private ref : SecurePointed.type
  usize : USize
  usize_rfl : usize = n

namespace SecretVector

variable {σ} {τ : @& Sodium σ}

noncomputable instance {n} : Nonempty (τ.SecretVector n) :=
  ⟨{ ref := Classical.choice SecurePointed.property, usize := n, usize_rfl := rfl }⟩

@[extern "lean_sodium_malloc"]
opaque randomBytes (n : USize) : IO (τ.SecretVector n)

@[extern "lean_sodium_malloc_deterministic"]
opaque seededBytes (n : USize) (seed : @& ByteVector 32) : IO (τ.SecretVector n)

@[extern "lean_sodium_secure_obj_is_zero"]
opaque isZero {n} (obj : @& τ.SecretVector n) : Bool

@[extern "lean_sodium_secure_obj_compare"]
opaque compare {n} (obj1 obj2 : @& τ.SecretVector n) : Ordering

instance {n} : Ord (τ.SecretVector n) := ⟨compare⟩
instance {n} : BEq (τ.SecretVector n) := ⟨(compare · · == .eq)⟩
instance {n} : LT (τ.SecretVector n) := ⟨(compare · · == .lt)⟩

end SecretVector

structure Entropy {σ} (_ : Sodium σ) where
  private mk ::
  private ref : SecurePointed.type
  uoff : USize
  usize : USize

namespace Entropy

variable {σ} {τ : @& Sodium σ}

noncomputable instance : Nonempty τ.Entropy :=
  ⟨{ ref := Classical.choice SecurePointed.property, uoff := 0, usize := 0 }⟩

@[extern "lean_sodium_randombytes_buf"]
opaque randomBytes (n : USize) : IO τ.Entropy

@[extern "lean_sodium_randombytes_buf_deterministic"]
opaque seededBytes (n : USize) (seed : @& ByteVector 32) : IO τ.Entropy

@[extern "lean_sodium_randombytes_buf_refresh"]
opaque refresh (bytes : τ.Entropy) : BaseIO τ.Entropy

@[extern "lean_sodium_randombytes_buf_refresh_deterministic"]
opaque seededRefresh (bytes : τ.Entropy) (seed : @& ByteVector 32) : BaseIO τ.Entropy

@[extern "lean_sodium_randombytes_buf_extract_slice"]
opaque extractSlice (bytes : τ.Entropy) (n : USize) : BaseIO (ByteArray × τ.Entropy)

end Entropy

end Sodium
