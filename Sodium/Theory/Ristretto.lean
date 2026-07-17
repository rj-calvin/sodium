import Sodium.Theory.Basic
import Sodium.Data.Ristretto255

namespace Sodium.Theory.Ristretto

def order : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

theorem order_pos : 0 < order := by decide

theorem order_lt_mask : order < 2 ^ 255 := by decide

theorem order_lt_word : order < 256 ^ 32 := by decide

def encList : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, x => UInt8.ofNat (x % 256) :: encList k (x / 256)

theorem length_encList (k x : Nat) : (encList k x).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [encList, ih]

def decList : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decList bs

theorem decList_encList (k x : Nat) : decList (encList k x) = x % 256 ^ k := by
  induction k generalizing x with
  | zero => simp [encList, decList, Nat.mod_one]
  | succ k ih =>
    rw [Nat.pow_succ', Nat.mod_mul]
    simp [encList, decList, ih]

def enc (k x : Nat) : ByteVector k :=
  ⟨⟨(encList k x).toArray⟩, by simp [ByteArray.size, length_encList]⟩

def dec {k : Nat} (v : ByteVector k) : Nat := decList v.toByteArray.data.toList

@[simp] theorem dec_enc (k x : Nat) : dec (enc k x) = x % 256 ^ k := by
  simp [dec, enc, decList_encList]

def mask {k : Nat} (v : ByteVector k) : Nat := dec v % 2 ^ 255

section Impl

variable (n p q : @& ByteVector 32) (u : @& ByteVector 64)

@[implemented_by Ristretto255.mulBase]
def mulBase := if mask n % order = 0 then none else some (enc 32 (mask n % order))

@[implemented_by Ristretto255.mul]
def mul :=
  if dec p < order then
    if mask n * dec p % order = 0 then none else some (enc 32 (mask n * dec p % order))
  else none

@[implemented_by Ristretto255.add]
def add :=
  if dec p < order ∧ dec q < order then some (enc 32 ((dec p + dec q) % order)) else none

@[implemented_by Ristretto255.sub]
def sub :=
  if dec p < order ∧ dec q < order then
    some (enc 32 ((dec p + (order - dec q)) % order))
  else none

@[implemented_by Ristretto255.fromHash]
def fromUniform := enc 32 (dec u % order)

@[implemented_by Ristretto255.isValidPoint]
def validPoint := decide (dec p < order)

def scalarReduced := decide (dec n < order)

@[implemented_by Ristretto255.scalarReduce]
def scalarReduce := enc 32 (dec u % order)

@[implemented_by Ristretto255.scalarAdd]
def scalarAdd := enc 32 ((dec p + dec q) % 256 ^ 32 % order)

@[implemented_by Ristretto255.scalarMul]
def scalarMul := enc 32 (dec p * dec q % order)

@[implemented_by Ristretto255.scalarNeg]
def scalarNeg := enc 32 ((order - dec p % order) % order)

end Impl

def spec : PrimeOrderGroup where
  name := `ristretto255.model
  scalarBytes := 32
  pointBytes := 32
  uniformBytes := 64
  nonReducedBytes := 64
  mulBase
  mul
  add
  sub
  fromUniform
  validPoint
  scalarReduced
  scalarReduce
  scalarAdd
  scalarMul
  scalarNeg

theorem dec_enc_lt {x : Nat} (h : x < order) : dec (enc 32 x) = x := by
  rw [dec_enc]
  exact Nat.mod_eq_of_lt (Nat.lt_trans h order_lt_word)

theorem mask_reduced {v : ByteVector 32} (h : dec v < order) : mask v = dec v :=
  Nat.mod_eq_of_lt (Nat.lt_trans h order_lt_mask)

theorem mask_enc_mod (x : Nat) : mask (enc 32 (x % order)) = x % order := by
  rw [mask, dec_enc_lt (Nat.mod_lt _ order_pos)]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ order_pos) order_lt_mask)

theorem add_lt_word {x y : Nat} (hx : x < order) (hy : y < order) : x + y < 256 ^ 32 := by
  have h : order + order < 256 ^ 32 := by decide
  omega

theorem mod_mul_mod_left (a b n : Nat) : a % n * b % n = a * b % n := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem mod_mul_mod_right (a b n : Nat) : a * (b % n) % n = a * b % n := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem scalarReduced_enc_mod (x : Nat) : spec.scalarReduced (enc 32 (x % order)) = true := by
  simp only [spec, scalarReduced]
  rw [dec_enc_lt (Nat.mod_lt _ order_pos)]
  exact decide_eq_true (Nat.mod_lt _ order_pos)

theorem mulBase_eq_some {n p : ByteVector 32} (h : spec.mulBase n = some p) :
    mask n % order ≠ 0 ∧ p = enc 32 (mask n % order) := by
  simp only [spec, mulBase] at h
  by_cases h0 : mask n % order = 0
  · rw [if_pos h0] at h
    exact absurd h (by simp)
  · rw [if_neg h0] at h
    exact ⟨h0, (Option.some.inj h).symm⟩

theorem mul_eq_some {n p q : ByteVector 32} (h : spec.mul n p = some q) :
    dec p < order ∧ mask n * dec p % order ≠ 0 ∧ q = enc 32 (mask n * dec p % order) := by
  simp only [spec, mul] at h
  by_cases hp : dec p < order
  · rw [if_pos hp] at h
    by_cases h0 : mask n * dec p % order = 0
    · rw [if_pos h0] at h
      exact absurd h (by simp)
    · rw [if_neg h0] at h
      exact ⟨hp, h0, (Option.some.inj h).symm⟩
  · rw [if_neg hp] at h
    exact absurd h (by simp)

theorem spec_lawful (hp : ∀ x y, order ∣ x * y → order ∣ x ∨ order ∣ y) : spec.Lawful where
  mul_comm a b pa pb hpa hpb := by
    obtain ⟨ha, rfl⟩ := mulBase_eq_some hpa
    obtain ⟨hb, rfl⟩ := mulBase_eq_some hpb
    simp only [spec, mul]
    rw [dec_enc_lt (Nat.mod_lt _ order_pos), dec_enc_lt (Nat.mod_lt _ order_pos),
      if_pos (Nat.mod_lt _ order_pos), if_pos (Nat.mod_lt _ order_pos),
      mod_mul_mod_right, mod_mul_mod_right, Nat.mul_comm (mask a) (mask b)]
  mul_isSome a b pa pb hpa hpb := by
    obtain ⟨ha, rfl⟩ := mulBase_eq_some hpa
    obtain ⟨hb, rfl⟩ := mulBase_eq_some hpb
    simp only [spec, mul]
    rw [dec_enc_lt (Nat.mod_lt _ order_pos), if_pos (Nat.mod_lt _ order_pos), mod_mul_mod_right]
    have hne : mask a * mask b % order ≠ 0 := fun h =>
      (hp _ _ (Nat.dvd_of_mod_eq_zero h)).elim
        (fun d => ha (Nat.mod_eq_zero_of_dvd d))
        (fun d => hb (Nat.mod_eq_zero_of_dvd d))
    rw [if_neg hne]
    rfl
  scalarMul_comm a b := by
    simp only [spec, scalarMul]
    rw [Nat.mul_comm (dec a) (dec b)]
  add_comm p q := by
    simp only [spec, add]
    by_cases h1 : dec p < order <;> by_cases h2 : dec q < order <;>
      simp [h1, h2, Nat.add_comm]
  validPoint_fromUniform u := scalarReduced_enc_mod (dec u)
  scalarReduced_scalarReduce s := scalarReduced_enc_mod (dec s)
  scalarReduced_scalarAdd a b _ _ := scalarReduced_enc_mod ((dec a + dec b) % 256 ^ 32)
  scalarReduced_scalarMul a b _ _ := scalarReduced_enc_mod (dec a * dec b)
  mul_scalarAdd a b p x y z hra hrb hx hy hz := by
    simp only [spec] at hra hrb
    have ha := of_decide_eq_true hra
    have hb := of_decide_eq_true hrb
    obtain ⟨-, -, rfl⟩ := mul_eq_some hx
    obtain ⟨-, -, rfl⟩ := mul_eq_some hy
    obtain ⟨-, -, rfl⟩ := mul_eq_some hz
    simp only [spec, add, scalarAdd]
    rw [dec_enc_lt (Nat.mod_lt _ order_pos), dec_enc_lt (Nat.mod_lt _ order_pos),
      if_pos ⟨Nat.mod_lt _ order_pos, Nat.mod_lt _ order_pos⟩, mask_enc_mod,
      mask_reduced ha, mask_reduced hb, Nat.mod_eq_of_lt (add_lt_word ha hb),
      mod_mul_mod_left, ← Nat.add_mod, ← Nat.add_mul]
  mulBase_scalarMul c x px hrc hrx hpx := by
    simp only [spec] at hrc hrx
    have hc := of_decide_eq_true hrc
    have hx := of_decide_eq_true hrx
    obtain ⟨-, rfl⟩ := mulBase_eq_some hpx
    simp only [spec, mulBase, scalarMul, mul]
    rw [mask_enc_mod, Nat.mod_mod, mask_reduced hx, Nat.mod_eq_of_lt hx, dec_enc_lt hx,
      if_pos hx, mask_reduced hc]
  add_mulBase a b pa pb pc hra hrb hpa hpb hpc := by
    simp only [spec] at hra hrb
    have ha := of_decide_eq_true hra
    have hb := of_decide_eq_true hrb
    obtain ⟨-, rfl⟩ := mulBase_eq_some hpa
    obtain ⟨-, rfl⟩ := mulBase_eq_some hpb
    obtain ⟨-, rfl⟩ := mulBase_eq_some hpc
    simp only [spec, add, scalarAdd]
    rw [mask_reduced ha, mask_reduced hb, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      dec_enc_lt ha, dec_enc_lt hb, if_pos ⟨ha, hb⟩, mask_enc_mod, Nat.mod_mod,
      Nat.mod_eq_of_lt (add_lt_word ha hb)]

end Sodium.Theory.Ristretto
