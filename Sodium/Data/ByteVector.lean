import Sodium.Data.ByteArray
import Sodium.Data.Encodable.Basic

open Lean Alloy.C

alloy c include <lean/lean.h> <sodium.h> <string.h>

structure ByteVector (n : Nat) where
  toArray : ByteArray
  size_toArray : toArray.size = n

attribute [simp, grind] ByteVector.size_toArray

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

def push : ByteVector n → UInt8 → ByteVector (n + 1)
  | ⟨bs, h⟩, b => ⟨bs.push b, by simpa [ByteArray.size_push]⟩

def usize (_ : ByteVector n) : USize := n

alloy c extern "lean_sodium_increment_vec"
def succ (buf : @& ByteVector n) : ByteVector n :=
  size_t len = lean_sarray_size(buf);
  uint8_t* buf_ptr = lean_sarray_cptr(buf);
  lean_object* out = lean_alloc_sarray(sizeof(uint8_t), len, len);
  uint8_t* out_ptr = lean_sarray_cptr(out);
  memcpy(out_ptr, buf_ptr, len);
  sodium_increment(out_ptr, len);
  return out;

def isZero (x : ByteVector n) : Bool := x.toArray.isZero

-- def uget : (a : ByteVector n) → (i : USize) → (h : i < n := by get_elem_tactic) → UInt8
--   | ⟨bs, hb⟩, i, h => bs[i]'(by
--     rw [USize.toFin_val]
--     refine (USize.lt_ofNat_iff ?_).mp ?_
--     · exact ByteArray.size_lt_USize_size bs
--     · rw [← Nat.toUSize_eq, ← ByteArray.usize, hb]
--       exact h)

def get! : (ByteVector n) → Nat → UInt8
  | ⟨bs, _⟩, i => bs[i]!

def get : (a : ByteVector n) → (i : Nat) → (h : i < n := by get_elem_tactic) → UInt8
  | ⟨bs, hb⟩, i, h => bs[i]'(by
    refine Nat.lt_of_le_of_ne ?_ ?_
    . subst hb
      simp_all only [gt_iff_lt]
      exact Nat.le_of_succ_le h
    . subst hb
      simp_all only [gt_iff_lt]
      intro a
      subst a
      simp_all only [Nat.lt_irrefl]
  )

instance : GetElem (ByteVector n) Nat UInt8 fun _ i => i < n where
  getElem xs i _ := xs.get i

-- instance : GetElem (ByteVector n) USize UInt8 fun _ i => i.toFin < n where
--   getElem xs i h := xs.uget i (by sorry)

def set! : (ByteVector n) → Nat → UInt8 → ByteVector n
  | ⟨bs, hb⟩, i, b => ⟨bs.set! i b, by simp [ByteArray.set!, ByteArray.size]; rw [← hb]; rfl⟩

def set : (a : ByteVector n) → (i : Nat) → UInt8 → (h : i < n := by get_elem_tactic) → ByteVector n
  | ⟨bs, hb⟩, i, b, h => ⟨bs.set i b (by subst hb; simp_all only [gt_iff_lt]), by simp [ByteArray.set, ByteArray.size]; rw [← hb]; rfl⟩

-- def uset : (a : ByteVector n) → (i : USize) → UInt8 → (h : i < n := by get_elem_tactic) → ByteVector n
--   | ⟨bs, hb⟩, i, v, h => ⟨bs.uset i v (by sorry), by simp [ByteArray.uset, ByteArray.size]; rw [← hb]; rfl⟩

protected abbrev hash (a : ByteVector n) : UInt64 := a.toArray.hash

instance : Hashable (ByteVector n) where
  hash := ByteVector.hash

-- def extract (a : ByteVector n) (b e : Nat) : ByteVector (min n e - b) where
--   toArray := a.toArray.copySlice b .empty 0 (e - b)
--   usize_toArray := by
--     simp [ByteArray.copySlice, ByteArray.usize, ByteArray.size]
--     sorry

protected def append {n m : Nat} (a : ByteVector n) (b : ByteVector m) : ByteVector (n + m) where
  toArray := b.toArray.copySlice 0 a.toArray n m false
  size_toArray := by
    simp [ByteArray.copySlice, ByteArray.size]
    rw [← ByteArray.size, ← ByteArray.size]
    rw [a.size_toArray, b.size_toArray]
    simp only [Nat.min_self]
    omega

instance {n m : Nat} : HAppend (ByteVector n) (ByteVector m) (ByteVector (n + m)) :=
  ⟨ByteVector.append⟩

def toList (bs : ByteVector n) : List UInt8 := bs.toArray.toList

@[inline] def findIdx? (x : ByteVector n) (p : UInt8 → Bool) (start := 0) : Option Nat :=
  x.toArray.findIdx? p start

@[inline] protected def cast (h : n = m := by native_decide) (x : ByteVector n) : ByteVector m :=
  ⟨x.toArray, by rw [← h]; exact x.size_toArray⟩

@[inline] def cast? (x : ByteVector n) : Option (ByteVector m) :=
  if h : n = m then
    some ⟨x.toArray, by rw [← h]; exact x.size_toArray⟩
  else
    none

@[inline] def findFinIdx? (a : ByteVector n) (p : UInt8 → Bool) (start := 0) : Option (Fin n) :=
  let b := a.toArray.findFinIdx? p start
  a.size_toArray ▸ b

abbrev toBase64 (bs : ByteVector n) : String := bs.toArray.toBase64

def ofBase64? (s : String) : Option (ByteVector n) := do
  let data ← ByteArray.ofBase64? s
  if h : data.size = n then some ⟨data, h⟩
  else none

abbrev toUInt64LE (bs : ByteVector 8) : UInt64 := bs.toArray.toUInt64LE!
abbrev toUInt64BE (bs : ByteVector 8) : UInt64 := bs.toArray.toUInt64BE!

instance : ToJson (ByteVector n) := ⟨toJson ∘ ByteVector.toArray⟩

instance : FromJson (ByteVector n) where
  fromJson? json := do
    let bs ← fromJson? (α := ByteArray) json
    if h : bs.size = n then return ⟨bs, h⟩
    else throw s!"expected exactly {n} bytes"

instance : BEq (ByteVector n) where
  beq x y := compare x.toArray y.toArray == .eq

instance : Ord (ByteVector n) := ⟨fun x y => compare x.toArray y.toArray⟩

end ByteVector

namespace ByteArray

abbrev toVector (bs : ByteArray) : ByteVector bs.size := .mk bs rfl

abbrev toVector? (bs : ByteArray) : Option (ByteVector n) :=
  if h : bs.size = n then some ⟨bs, h⟩
  else none

abbrev toVector! (bs : ByteArray) : ByteVector n :=
  bs.toVector?.get!

@[simp]
theorem toVector_size : ∀ bs : ByteArray, bs.toVector.size = bs.size := by intro; rfl

@[simp]
theorem toVector_inj : ∀ bs : ByteArray, bs.toVector.toArray = bs := by intro; rfl

end ByteArray

namespace ByteVector

variable {n : Nat}

@[simp]
theorem toArray_inj : ∀ bs : ByteVector n, bs.toArray.toVector = bs.cast (by exact Eq.symm bs.size_toArray) := by intro; rfl

instance : DecidableEq (ByteVector n) := fun a b =>
  match decEq a.toArray b.toArray with
  | isTrue h => isTrue (by cases a; cases b; simp_all only)
  | isFalse h => isFalse (fun eq => by cases eq; exact h rfl)

instance : Encodable (ByteVector n) :=
  Encodable.ofLeftInj (·.toArray) (·.toVector.cast?) (fun x => by
    simp only [toArray_inj]
    unfold cast?
    simp only [size_toArray, ↓reduceDIte, Option.some.injEq]
    rfl
  )

end ByteVector
