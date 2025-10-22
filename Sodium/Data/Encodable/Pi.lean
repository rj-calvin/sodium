import Sodium.Data.Encodable.Basic

universe u

namespace Vector

variable {n : Nat} {α : Type u}

instance encodable [Encodable α] : Encodable (Vector α n) where
  encode x := encode x.toArray
  decode? json := do
    let x ← decode? (α := Array α) json
    if h : x.size = n then some ⟨x, h⟩
    else none
  encodek _ := by
    simp only [Encodable.encodek, Option.bind_eq_bind, Option.bind_some, size_toArray,
      ↓reduceDIte, mk_toArray]

theorem get_eq_get_toList (v : Vector α n) (i : Fin n) :
    v.get i = v.toList.get (Fin.cast (by exact Eq.symm length_toList) i) :=
  rfl

@[simp]
theorem get_ofFn {n} (f : Fin n → α) (i) : (ofFn f).get i = f i := by
  simp [get_eq_get_toList]

@[simp]
theorem ofFn_get (v : Vector α n) : ofFn v.get = v := by
  rcases v with ⟨l, rfl⟩
  simp_all only [eq_mk, toArray_ofFn]
  ext i hi₁ hi₂ : 1
  · simp_all only [Array.size_ofFn]
  · simp_all only [Array.getElem_ofFn]
    rfl

end Vector

namespace Encodable

variable {α : Type u}

instance finArrow {n : Nat} [Encodable α] : Encodable (Fin n → α) :=
  ofEquiv _ {
    push := Vector.ofFn
    pull := Vector.get
    push_pull_eq i := by funext j; exact Vector.get_ofFn i j
  }

instance finPi (n : Nat) (π : Fin n → Type u) [∀ i, Encodable (π i)] : Encodable (∀ i, π i) :=
  ofEquiv {f : Fin n → Σ i, π i // ∀ i, (f i).1 = i} {
    push f := ⟨fun i => ⟨i, f i⟩, fun _ => rfl⟩
    pull f i := by rw [← f.2 i]; exact (f.1 i).2
    push_pull_eq _ := by simp only [eq_mpr_eq_cast, cast_eq]
  }

end Encodable
