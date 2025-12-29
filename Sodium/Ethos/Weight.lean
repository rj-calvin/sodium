import Aesop
import Sodium.Data.Encodable.Basic

namespace Ethos

export Aesop (ScopeName)

deriving instance DecidableEq for ScopeName

attribute [aesop unsafe 50% cases constructors] ScopeName

/-- An abstract, universe-polymorphic quantization of units. -/
def Weight := Σ' n, ULift (Fin n)

def Weight.mk (n₁ : Nat) (n₂ : Nat) (h : n₁ < n₂) : Weight :=
  ⟨n₂, ⟨n₁, h⟩⟩

notation "Δ(" n₁ " | " n₂ ")" => Weight.mk n₁ n₂ (by omega)

instance : Zero Weight := ⟨Δ(0 | 1)⟩
instance : Inhabited Weight := ⟨0⟩

instance : Hashable Weight where
  hash x := mixHash 3 (mixHash (hash x.1) (hash x.2.down))

namespace Weight

def den (x : Weight) : Nat := x.1
def num (x : Weight) : Fin x.den := ULift.down x.2

@[simp]
theorem mk_num_den : ∀ x : Weight, Δ(x.num | x.den) = x := by intro; rfl

@[simp]
theorem den_nezero : ∀ x : Weight, x.den ≠ 0 := by
  intro x
  obtain ⟨_, ⟨_, h⟩⟩ := x
  exact Nat.ne_zero_of_lt h

@[simp]
theorem num_lt_den : ∀ x : Weight, x.num < x.den := by
  intro x
  obtain ⟨_, ⟨_, h⟩⟩ := x
  exact h

instance : ∀ x : Weight, NeZero x.den := fun x => ⟨den_nezero x⟩

@[simp]
theorem num_zero : ∀ x : Weight, x.den = 1 → x.num = 0 := by omega

@[ext, simp]
theorem ext : ∀ x y : Weight, x.den = y.den → (∀ (h : x.den = y.den), h ▸ x.num = y.num) → x = y := by
  intros x y h_den h_num
  obtain ⟨x_den, ⟨x_num, hx⟩⟩ := x
  obtain ⟨y_den, ⟨y_num, hy⟩⟩ := y
  subst h_den
  simp only [den, num, Fin.mk.injEq, forall_const] at h_num hy
  subst h_num
  rfl

@[coe]
def toFloat (x : Weight) : Float := x.num.toNat.toFloat / x.den.toFloat

abbrev Positive (x : Weight) : Prop := x.num ≠ 0

instance : Coe Weight Float := ⟨toFloat⟩
instance : ToString Weight := ⟨(·.toFloat.toString)⟩

instance : Repr Weight where
  reprPrec x
  | _ => f!"Δ({x.num}|{x.den})"

instance (x : Weight) : x.Positive → NeZero x.num := fun h => { out := h }

instance : Ord Weight where
  compare x y := compare (x.num * y.den) (y.num * x.den)

instance : LT Weight where
  lt x y := compare x y = .lt

instance : DecidableLT Weight := by
  intro ⟨x_den, ⟨x_num, _⟩⟩ ⟨y_den, ⟨y_num, _⟩⟩
  by_cases h : compare (x_num * y_den) (y_num * x_den) = .lt
  . exact isTrue h
  . exact isFalse h

@[simp]
theorem mk_num_pos : ∀ n m, NeZero n → (h : n < m) → Δ(n | m).num ≠ 0 := by
  intro _ _ h _
  unfold mk
  simp only [ne_eq, num, Fin.mk_eq_zero]
  exact h.out

def Shape := { x : Nat × Nat // x.2 ≠ 0 }

def Shape.push (x : Weight) : Shape := ⟨(x.num, x.den), den_nezero x⟩

def Shape.part (x : Weight) (h : x.num ≠ 0) : Shape := by
  refine ⟨⟨x.den, x.num⟩, ?_⟩
  simpa only [ne_eq, Fin.val_eq_zero_iff]

def Shape.pull (x : Shape) : Weight :=
  let ⟨⟨n₁, n₂⟩, _⟩ := x
  if _ : n₁ < n₂ then Δ(n₁ | n₂)
  else Δ(n₂ | n₁.succ)

@[simp]
theorem Shape.push_pull_eq : ∀ x : Weight, Shape.pull (Shape.push x) = ⟨x.den, ⟨x.num⟩⟩ := by
  intro x
  unfold push pull
  simp only [Fin.is_lt, reduceDIte, mk_num_den]
  rfl

@[simp]
theorem Shape.part_pull_succ : ∀ x, (h : x.num ≠ 0) → Shape.pull (Shape.part x h) = ⟨x.den.succ, x.num, by omega⟩ := by
  intro x h
  unfold part pull
  simp_all only [Nat.succ_eq_add_one]
  simp_all only [ne_eq]
  split
  omega
  rfl

instance : Encodable Weight :=
  have : Encodable Shape := by unfold Shape; infer_instance
  Encodable.ofEquiv _ {
    push := Shape.push
    pull := Shape.pull
    push_pull_eq := by intro x; simp only [Shape.push_pull_eq]; rfl
  }

protected def spin (x : Weight) (scope : ScopeName) : Weight :=
  Shape.pull <| if h : scope = .global ∧ x.num ≠ 0 then Shape.part x h.2 else Shape.push x

@[simp]
theorem weight_spin_zero : ∀ x : Weight, (h : x.num = 0) → x.spin .local = x.spin .global := by
  intro x h
  unfold Weight.spin
  simp_all only [reduceCtorEq, ne_eq, false_and, ↓reduceDIte, true_and, dite_not]

protected def quantize (x : Weight.{u}) (scope : ScopeName) : Nat :=
  let x : Weight.{u} := x.spin scope
  x.den - x.num

@[simp]
theorem quantize_nezero : ∀ (x : Weight) (s : ScopeName), x.quantize s ≠ 0 := by
  intros
  unfold Weight.quantize Weight.spin
  simp only [ne_eq]
  omega

@[simp]
theorem quantize_local_eq : ∀ x : Weight, x.quantize .local = x.den - x.num := by
  intro x
  unfold Weight.quantize Weight.spin
  have h_den : (Shape.push x).pull.den = x.den := by simp only [Shape.push_pull_eq]; congr
  have h_num : (Shape.push x).pull.num = @Fin.val x.den x.num := by
    unfold Shape.push Shape.pull
    split
    rename_i heq
    simp_all only [ne_eq, Shape.push_pull_eq, Subtype.mk.injEq, Prod.mk.injEq, Nat.succ_eq_add_one]
    simp_all only [ne_eq]
    obtain ⟨left, right⟩ := heq
    subst left right
    simp_all only [den_nezero, not_false_eq_true, Fin.is_lt]
    have : @Fin.val (if x_1 : @Fin.val x.den x.num < x.den then mk (@Fin.val x.den x.num) x.den x_1 else mk x.den (@Fin.val x.den x.num + 1) (by omega)).den (if x_1 : @Fin.val x.den x.num < x.den then mk (@Fin.val x.den x.num) x.den x_1 else mk x.den (@Fin.val x.den x.num + 1) (by omega)).num = @Fin.val (mk (@Fin.val x.den x.num) x.den (by omega)).den (mk (@Fin.val x.den x.num) x.den (by omega)).num := by
      congr <;> split
      . simp only
      . omega
      . rfl
      . have : @Fin.val x.den x.num < x.den := by simp only [Fin.is_lt]
        contradiction
    exact this
  simp_all only [Shape.push_pull_eq, reduceCtorEq, ne_eq, false_and, ↓reduceDIte, ↓dreduceDIte]

@[simp]
theorem quantize_global_reduced_eq : ∀ x : Weight, x.num = 0 → x.quantize .global = x.den := by
  intro x h
  unfold Weight.quantize Weight.spin
  have h_den : (Shape.push x).pull.den = x.den := by simp only [Shape.push_pull_eq]; congr
  have h_num : (Shape.push x).pull.num = @Fin.val x.den 0 := by
    unfold Shape.push Shape.pull
    simp_all only [Shape.push_pull_eq, ne_eq, Nat.succ_eq_add_one, Fin.val_zero,
      Fin.val_eq_zero_iff]
    have : (if x_1 : @Fin.val x.den x.num < x.den then mk (@Fin.val x.den x.num) x.den x_1 else mk x.den (@Fin.val x.den x.num + 1) (by omega)) = mk (@Fin.val x.den x.num) x.den (by omega) := by
      simp_all only [Fin.val_zero, Nat.zero_add]
      split
      next _ => simp_all only
      next h' =>
        have : 0 < x.den := by exact Nat.pos_of_neZero x.den
        contradiction
    rw [this]
    simp_all only [Fin.val_zero, Nat.zero_add]
    exact h
  simp_all only [ne_eq, not_true_eq_false, and_false, ↓reduceDIte, Shape.push_pull_eq]
  have : (if _ : Aesop.ScopeName.global = Aesop.ScopeName.global ∧ x.num ≠ 0 then Shape.part x (by omega) else Shape.push x) = Shape.push x := by
    simp_all only [ne_eq, not_true_eq_false, and_false, ↓reduceDIte]
  rw [this]
  simp_all only [ne_eq, not_true_eq_false, and_false, ↓reduceDIte, Fin.val_zero, Nat.sub_zero]

@[simp]
theorem quantize_global_partial_eq : ∀ x : Weight, x.num ≠ 0 → x.quantize .global = x.den.succ - x.num := by
  intro x h
  unfold Weight.quantize Weight.spin
  have h_den : (Shape.part x h).pull.den = x.den.succ := by simp only [Shape.part_pull_succ]; rfl
  have h_num : (Shape.part x h).pull.num = @Fin.val x.den x.num := by
    unfold Shape.part Shape.pull
    split
    rename_i heq
    simp_all only [Shape.part_pull_succ, ne_eq, Subtype.mk.injEq, Prod.mk.injEq]
    obtain ⟨left, right⟩ := heq
    subst left right
    have h_bound : ¬x.den < @Fin.val x.den x.num := by simp only [Nat.not_lt, Fin.is_le']
    have : @Fin.val (if x_1 : x.den < @Fin.val x.den x.num then mk x.den (@Fin.val x.den x.num) x_1 else mk (@Fin.val x.den x.num) x.den.succ (by omega)).den (if x_1 : x.den < @Fin.val x.den x.num then mk x.den (@Fin.val x.den x.num) x_1 else mk (@Fin.val x.den x.num) x.den.succ (by omega)).num = @Fin.val x.den.succ (x.num.castLT (by omega)) := by
      congr
      . split
        . contradiction
        . rfl
      . rw [dif_neg h_bound]
        rfl
    exact this
  have : (if _ : Aesop.ScopeName.global = Aesop.ScopeName.global ∧ x.num ≠ 0 then Shape.part x (by omega) else Shape.push x) = Shape.part x (by omega) := by
    simp only [ne_eq, true_and, dite_eq_ite, ite_not, ite_eq_right_iff]
    exact fun a => False.elim (h a)
  rw [this]
  simp_all only [Shape.part_pull_succ, Nat.succ_eq_add_one, ne_eq, not_false_eq_true, and_self, ↓reduceDIte]
  omega

def liftRelative.{v, u} : ∀ x : Weight, {y : Weight // Weight.quantize.{u} x .global = Weight.quantize.{v} y .local} := fun x => by
  if x.num = 0 then
    refine ⟨⟨x.den, ⟨0⟩⟩, ?_⟩
    simp_all only [quantize_global_reduced_eq, quantize_local_eq]
    rfl
  else
    refine ⟨⟨x.den + 1, ⟨x.num.castLT (by omega)⟩⟩, ?_⟩
    simp_all only [ne_eq, not_false_eq_true, quantize_global_partial_eq, Nat.succ_eq_add_one, quantize_local_eq]
    rfl

@[simp] theorem quantize_lift_relative_nonempty.{v, u} :
    ∀ x : Weight, Nonempty {y : Weight // Weight.quantize.{u} x .global = Weight.quantize.{v} y .local} :=
  (Nonempty.intro ·.liftRelative)

/-- Given any global weight `x` in universe `u`, there exists a local weight `y` in universe `v` of equal measure. -/
theorem quantize_relativity.{v, u} : ∀ x : Weight, ∃ y : Weight, Weight.quantize.{u} x .global = Weight.quantize.{v} y .local := by
  intro x
  obtain ⟨y, hy⟩ := liftRelative.{v, u} x
  exact ⟨y, hy⟩

end Ethos.Weight
