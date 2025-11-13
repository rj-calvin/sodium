import Sodium.Data.Encodable.Basic

universe u v

namespace Ethos

def Probability := Σ' n, ULift (Fin n)

instance : BEq Probability where
  beq x y := x.1 = y.1 ∧ x.2.down.toNat = y.2.down.toNat

instance : Inhabited Probability where
  default := ⟨1, ⟨0⟩⟩

instance : Hashable Probability where
  hash x := mixHash 3 (mixHash (hash x.1) (hash x.2.down))

namespace Probability

protected abbrev Id := Fin

def toFloat (ι : Probability) : Float := ι.2.down.toNat.toFloat / ι.1.toFloat

def Shape := Nat × Nat

-- def Shape.push (x : Probability) : Shape := (x.1, x.2.down) -- whoops!
def Shape.push (x : Probability) : Shape := (x.2.down, x.1)
def Shape.part (x : Probability) : Shape := (x.1, x.2.down)

def Shape.pull (x : Shape) : Option Probability := by
  cases h₁ : x.1 with
  | zero => exact none
  | succ n₁ =>
    cases h₂ : x.2 with
    | zero => exact some default
    | succ n₂ =>
      if h : n₁ < n₂ then
        exact some ⟨x.2, ⟨⟨x.1, by omega⟩⟩⟩
      else
        exact some ⟨x.1.succ, ⟨⟨x.2, by omega⟩⟩⟩

theorem Shape.push_pull_eq? : ∀ x, Shape.pull (Shape.push x) = some x := by
  unfold Shape.push Shape.pull
  intro x
  sorry

theorem Shape.part_pull_mono? : ∀ x y, Shape.pull (Shape.part x) = some y → y.toFloat < x.toFloat := by
  unfold Shape.part Shape.pull
  intros x y
  sorry

instance : Encodable Probability :=
  have : Encodable Shape := by unfold Shape; infer_instance
  Encodable.ofLeftInj Shape.push Shape.pull Shape.push_pull_eq?

#eval show IO Unit from do
  let x : Probability.{0} := ⟨11, ⟨3⟩⟩
  println! x.toFloat
  let y? : Option Probability.{0} := Shape.pull (Shape.push x)
  let z? : Option Probability.{0} := y?.bind fun y => Shape.pull (Shape.push y)
  println! y?.map toFloat
  println! z?.map toFloat
  let a? : Option Probability.{0} := z?.bind fun y => Shape.pull (Shape.push y)
  println! a?.map toFloat

#eval show IO Unit from do
  let x : Probability.{0} := ⟨11, ⟨3⟩⟩
  println! x.toFloat
  let y? : Option Probability.{0} := Shape.pull (Shape.part x)
  let z? : Option Probability.{0} := y?.bind fun y => Shape.pull (Shape.part y)
  println! y?.map toFloat
  println! z?.map toFloat
  let w? : Option Probability.{0} := z?.bind fun z => Shape.pull (Shape.part z)
  println! w?.map toFloat

end Ethos.Probability
