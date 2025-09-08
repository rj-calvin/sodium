import Sodium.Data.Encodable.Pi

universe u v w

inductive WType {α : Type u} (β : α → Type v)
  | mk (a : α) (f : β a → WType β) : WType β

instance : Inhabited (WType fun _ : Unit => Empty) := ⟨WType.mk () Empty.elim⟩

namespace WType

variable {α : Type u} {β : α → Type v}

def toSigma : WType β → Σ a : α, β a → WType β
  | ⟨a, f⟩ => ⟨a, f⟩

def ofSigma : (Σ a : α, β a → WType β) → WType β
  | ⟨a, f⟩ => ⟨a, f⟩

@[simp]
theorem ofSigma_toSigma : ∀ w : WType β, ofSigma (toSigma w) = w
  | ⟨_, _⟩ => rfl

@[simp]
theorem toSigma_ofSigma : ∀ s : Σ a : α, β a → WType β, toSigma (ofSigma s) = s
  | ⟨_, _⟩ => rfl

def elim (γ : Type w) (fγ : (Σ a, β a → γ) → γ) : WType β → γ
  | ⟨a, f⟩ => fγ ⟨a, fun b => elim γ fγ (f b)⟩

variable {ι : α → Nat}

def depth : WType (fun a => Fin (ι a)) → Nat
  | ⟨a, f⟩ =>
    let n := ι a
    if h : n ≠ 0 then
      have : NeZero n := ⟨by exact h⟩
      let ns := List.range n |>.map (Fin.ofNat n)
      1 + ns.foldl (init := 0) fun acc i => max acc (depth (f i))
    else 1

theorem depth_pos (w : WType fun a => Fin (ι a)) : 0 < w.depth := by
  obtain ⟨a, f⟩ := w
  unfold depth
  simp only [ne_eq, dite_not]
  split
  . trivial
  . omega

theorem depth_lt_depth_mk (a : α) (f : Fin (ι a) → WType fun i => Fin (ι i)) (i : Fin (ι a)) : depth (f i) < depth ⟨a, f⟩ := by
  sorry

end WType

abbrev WFin {α : Type u} (ι : α → Nat) (n : Nat) :=
  { w : WType fun a => Fin (ι a) // w.depth ≤ n }

namespace WFin

end WFin
