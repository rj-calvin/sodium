import Aesop
import Sodium.Data.Encodable.Basic

universe u

namespace Ethos

export Aesop (ScopeName)

deriving instance DecidableEq for ScopeName

attribute [aesop unsafe 50% cases constructors] ScopeName

/--
An abstract, universe-polymorphic quantization of units.
-/
def Weight := Σ' n, ULift (Fin n)

def Weight.mk (n₁ : Nat) (n₂ : Nat) (h : n₁ < n₂) : Weight.{0} :=
  ⟨n₂, ⟨n₁, h⟩⟩

notation "Δ(" n₁ " | " n₂ ")" => Weight.mk n₁ n₂ (by omega)

instance : Zero Weight := ⟨Δ(0 | 1)⟩
instance : Inhabited Weight := ⟨0⟩

instance : Hashable Weight where
  hash x := mixHash 3 (mixHash (hash x.1) (hash x.2.down))

namespace Weight

def den (x : Weight) : Nat := x.1
def num (x : Weight) : Fin x.den := x.2.down

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
theorem ext : ∀ x y : Weight, (x.den = y.den) → (∀ (h : x.den = y.den), h ▸ x.num = y.num) → x = y := by
  intros x y h_den h_num
  obtain ⟨x_den, ⟨x_num, hx⟩⟩ := x
  obtain ⟨y_den, ⟨y_num, hy⟩⟩ := y
  subst h_den
  simp only [den, num, Fin.mk.injEq, forall_const] at h_num hy
  subst h_num
  rfl

@[coe]
def toFloat (x : Weight) : Float := x.num.toNat.toFloat / x.den.toFloat

instance : Coe Weight Float := ⟨toFloat⟩
instance : ToString Weight := ⟨(·.toFloat.toString)⟩

instance : Repr Weight where
  reprPrec x
  | _ => f!"Δ({x.num}|{x.den})"

abbrev Positive (x : Weight) : Prop := x.num ≠ 0

instance (x : Weight) : x.Positive → NeZero x.num := fun h => { out := h }

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
theorem Shape.push_pull_eq : ∀ x, Shape.pull (Shape.push x) = x := by
  intro x
  unfold push pull
  simp only [Fin.is_lt, reduceDIte, mk_num_den]

instance : Encodable Weight :=
  have : Encodable Shape := by unfold Shape; infer_instance
  Encodable.ofEquiv _ {
    push := Shape.push
    pull := Shape.pull
    push_pull_eq := by simp
  }

protected def spin (x : Weight) (scope : ScopeName) : Weight :=
  Shape.pull <| if h : scope = .global ∧ x.num ≠ 0 then Shape.part x h.2 else Shape.push x

protected def quantize (x : Weight) (scope : ScopeName) : Nat :=
  let x := x.spin scope
  x.den - x.num

@[simp]
theorem quantize_nezero : ∀ (x : Weight) (s : ScopeName), x.quantize s ≠ 0 := by
  intros
  unfold Weight.quantize Weight.spin
  simp only [ne_eq]
  omega

end Ethos.Weight
