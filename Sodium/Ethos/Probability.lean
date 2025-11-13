import Sodium.Data.Encodable.Basic

universe u

namespace Ethos

def Probability := Σ' n, ULift (Fin n)

instance : Inhabited Probability where
  default := ⟨1, ⟨0⟩⟩

def Probability.mk (n₁ : Nat) (n₂ : Nat) (h : n₁ < n₂) : Probability :=
  ⟨n₂, ⟨n₁, h⟩⟩

instance : Hashable Probability where
  hash x := mixHash 3 (mixHash (hash x.1) (hash x.2.down))

notation "Δ(" n₁ " | " n₂ ")" => Probability.mk n₁ n₂ (by omega)

namespace Probability

def den (x : Probability) : Nat := x.1
def num (x : Probability) : Fin x.den := x.2.down

@[simp]
theorem den_nezero : ∀ x : Probability, x.den ≠ 0 := by
  intro x
  obtain ⟨_, ⟨_, h⟩⟩ := x
  exact Nat.ne_zero_of_lt h

@[simp]
theorem num_lt_den : ∀ x : Probability, x.num < x.den := by
  intro x
  obtain ⟨_, ⟨_, h⟩⟩ := x
  exact h

instance : ∀ x : Probability, NeZero x.den := fun x => ⟨den_nezero x⟩

@[simp]
theorem num_zero : ∀ x : Probability, x.den = 1 → x.num = 0 := by omega

@[ext, simp]
theorem ext : ∀ x y : Probability, (x.den = y.den) → (∀ (h : x.den = y.den), h ▸ x.num = y.num) → x = y := by
  intros x y h_den h_num
  obtain ⟨x_den, ⟨x_num, hx⟩⟩ := x
  obtain ⟨y_den, ⟨y_num, hy⟩⟩ := y
  subst h_den
  simp [den, num] at h_num hy
  have : x_num = y_num := h_num
  subst this
  rfl

@[simp]
theorem mk_num_den : ∀ x : Probability, Δ(x.num | x.den) = x := by
  intro _
  rfl

@[coe]
def toFloat (x : Probability) : Float := x.num.toNat.toFloat / x.den.toFloat

instance : Coe Probability Float := ⟨toFloat⟩

class Positive (x : Probability) : Prop where
  num_nezero : x.num ≠ 0

def Shape := { s : Nat × Nat // s.2 ≠ 0 }

def Shape.push (x : Probability) : Shape := ⟨(x.num, x.den), by exact den_nezero x⟩

def Shape.pull (x : Shape) : Probability :=
  let ⟨⟨n₁, n₂⟩, _⟩ := x
  if _ : n₁ < n₂ then Δ(n₁ | n₂)
  else Δ(n₂ | n₁.succ)

theorem Shape.push_pull_eq : ∀ x, Shape.pull (Shape.push x) = x := by
  unfold Shape.push Shape.pull
  intro x
  simp only [Fin.is_lt, reduceDIte, mk_num_den]

instance : Encodable Probability :=
  have : Encodable Shape := by unfold Shape; infer_instance
  Encodable.ofEquiv _ {
    push := Shape.push
    pull := Shape.pull
    push_pull_eq := Shape.push_pull_eq
  }

#eval show IO Unit from do
  let x : Probability.{0} := Δ(3 | 11)
  let y? : Option Probability.{0} := Shape.pull (Shape.push x)
  let z? : Option Probability.{0} := y?.bind fun y => Shape.pull (Shape.push y)
  let w? : Option Probability.{0} := z?.bind fun z => Shape.pull (Shape.push z)
  println! x.toFloat
  println! y?.map toFloat
  println! z?.map toFloat
  println! w?.map toFloat

end Ethos.Probability
