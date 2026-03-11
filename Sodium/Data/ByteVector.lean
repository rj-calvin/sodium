structure ByteVector (n : Nat) where
  toByteArray : ByteArray
  size_toByteArray : toByteArray.size = n
  deriving DecidableEq

attribute [simp, grind =] ByteVector.size_toByteArray

variable {n m : Nat}

namespace ByteVector

abbrev size (_ : ByteVector n) : Nat := n

@[inline, expose] def replicate (n) (v : UInt8) : ByteVector n :=
  ⟨⟨Array.replicate n v⟩, by simp only [ByteArray.size, Array.size_replicate]⟩

instance : Inhabited (ByteVector n) where
  default := replicate n default

def empty : ByteVector 0 := ⟨ByteArray.empty, rfl⟩

instance : EmptyCollection (ByteVector 0) where
  emptyCollection := ⟨ByteArray.empty, rfl⟩

protected abbrev hash (a : ByteVector n) : UInt64 := a.toByteArray.hash

instance : Hashable (ByteVector n) where
  hash := ByteVector.hash

@[extern "lean_sodium_bytes_compare"]
opaque compare (x y : @& ByteVector n) : Ordering

instance : Ord (ByteVector n) := ⟨compare⟩
instance : BEq (ByteVector n) := ⟨(compare · · == .eq)⟩
instance : LT (ByteVector n) := ⟨(compare · · == .lt)⟩

@[extern "lean_sodium_bytes_dec_eq"]
def decEq (x y : @& ByteVector n) : Decidable (Eq x y) :=
  match x, y with
  | ⟨⟨⟨x⟩⟩, _⟩, ⟨⟨⟨y⟩⟩, _⟩ =>
    dite (x = y)
      (fun h => match x, y, h with | _, _, Eq.refl _ => isTrue rfl)
      (fun h => isFalse (fun h' => h (congrArg (fun z => Array.toList z.toByteArray.data) h')))

@[extern "lean_sodium_bytes_dec_lt"]
def decLt (x y : @& ByteVector n) : Decidable (LT.lt x y) :=
  dite (compare x y == .lt) isTrue isFalse

instance : DecidableEq (ByteVector n) := decEq
instance : DecidableLT (ByteVector n) := decLt
instance {n m : Nat} {h : n = m} : HEq (ByteVector n) (ByteVector m) := by subst h; rfl

def toArray (bs : ByteVector n) : Array UInt8 := bs.toByteArray.data
def toList (bs : ByteVector n) : List UInt8 := bs.toByteArray.toList

@[inline] def findIdx? (x : ByteVector n) (p : UInt8 → Bool) (start := 0) : Option Nat :=
  x.toByteArray.findIdx? p start

@[inline] protected def cast (h : n = m := by native_decide) (x : ByteVector n) : ByteVector m :=
  ⟨x.toByteArray, by rw [← h]; exact x.size_toByteArray⟩

@[inline] def cast? (x : ByteVector n) : Option (ByteVector m) :=
  if h : n = m then some ⟨x.toByteArray, by rw [← h]; exact x.size_toByteArray⟩
  else none

instance {n m : Nat} {h : n = m} : ∀ x : ByteVector n, HEq (x.cast h) x := fun _ => by subst h; rfl

@[inline] def findFinIdx? (a : ByteVector n) (p : UInt8 → Bool) (start := 0) : Option (Fin n) :=
  let b := a.toByteArray.findFinIdx? p start
  a.size_toByteArray ▸ b

abbrev toUInt64LE (bs : ByteVector 8) : UInt64 := bs.toByteArray.toUInt64LE!
abbrev toUInt64BE (bs : ByteVector 8) : UInt64 := bs.toByteArray.toUInt64BE!

end ByteVector

namespace ByteArray

abbrev toByteVector (bs : ByteArray) : ByteVector bs.size := .mk bs rfl

abbrev toByteVector? (bs : ByteArray) : Option (ByteVector n) :=
  if h : bs.size = n then some ⟨bs, h⟩
  else none

abbrev toVector! (bs : ByteArray) : ByteVector n :=
  bs.toByteVector?.get!

@[simp, grind =] theorem toByteVector_size : ∀ bs : ByteArray, bs.toByteVector.size = bs.size := by intro; rfl
@[simp] theorem toByteVector_inj : ∀ bs : ByteArray, bs.toByteVector.toByteArray = bs := by intro; rfl

end ByteArray

namespace ByteVector

variable {n : Nat}

@[simp] theorem toByteArray_inj : ∀ bs : ByteVector n, bs.toByteArray.toByteVector = bs.cast (by exact Eq.symm bs.size_toByteArray) :=
  by intro; rfl

end ByteVector
