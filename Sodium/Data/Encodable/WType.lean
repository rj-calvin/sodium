import Batteries.Tactic.Congr
import Sodium.Data.Encodable.Pi
import Sodium.Data.Empty

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

theorem Sigma.mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
  Sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ b₁ ≍ b₂ := by simp only [Sigma.mk.injEq]

def elim (γ : Type w) (fγ : (Σ a, β a → γ) → γ) : WType β → γ
  | ⟨a, f⟩ => fγ ⟨a, fun b => elim γ fγ (f b)⟩

theorem elim_inj (γ : Type w) (fγ : (Σ a, β a → γ) → γ) (hfγ : ∀ ⦃a b⦄, fγ a = fγ b → a = b) :
    ∀ ⦃a b⦄, elim γ fγ a = elim γ fγ b → a = b
  | ⟨a₁, f₁⟩, ⟨a₂, f₂⟩, h => by
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp (hfγ h)
    congr with x
    simp only [heq_eq_eq] at h
    exact elim_inj γ fγ hfγ (congrFun h x)

instance [hα : IsEmpty α] : IsEmpty (WType β) :=
  ⟨fun w => WType.recOn w (IsEmpty.elim hα)⟩

variable {ι : α → Nat}

def depth : WType (fun a => Fin (ι a)) → Nat
  | ⟨a, f⟩ =>
    let n := ι a
    if h : n = 0 then 1
    else
      let ns := List.range n |>.map (@Fin.ofNat n ⟨h⟩)
      1 + ns.foldl (init := 0) fun acc i => max acc (depth (f i))

theorem depth_pos (w : WType fun a => Fin (ι a)) : 0 < w.depth := by
  obtain ⟨a, f⟩ := w
  unfold depth
  simp only
  split
  . trivial
  . omega

private theorem fin_nonzero {n : Nat} (i : Fin n) : n ≠ 0 := by
  intro h
  rw [h] at i
  exact Fin.elim0 i

private theorem foldl_max_mono {l : List α} (f : α → Nat) (a b : Nat) (h : a ≤ b) :
    l.foldl (fun acc y => max acc (f y)) a ≤ l.foldl (fun acc y => max acc (f y)) b := by
  induction l generalizing a b with
  | nil => simp only [List.foldl_nil]; exact h
  | cons hd _ ih =>
    simp only [List.foldl_cons]
    apply ih
    cases Nat.le_total a (max b (f hd)) <;> omega

private theorem foldl_max_self {l : List α} (f : α → Nat) (a : Nat) :
    a ≤ l.foldl (fun acc y => max acc (f y)) a := by
  induction l generalizing a with
  | nil => simp only [List.foldl_nil]; exact Nat.le_refl a
  | cons head tail ih =>
    simp only [List.foldl_cons]
    have step : a ≤ max a (f head) := Nat.le_max_left a (f head)
    exact Nat.le_trans step (ih (max a (f head)))

private theorem foldl_max_le {l : List α} {x : α} (h : x ∈ l) (f : α → Nat) :
    f x ≤ l.foldl (fun acc y => max acc (f y)) 0 := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    simp only [List.foldl_cons, Nat.zero_le, Nat.max_eq_right, ge_iff_le]
    cases List.mem_cons.mp h with
    | inl h_eq =>
      subst h_eq
      exact Nat.le_trans (Nat.le_refl _) (foldl_max_self f (f x))
    | inr h_mem =>
      have ih : f x ≤ tail.foldl (fun acc y => max acc (f y)) 0 := ih h_mem
      have mono := foldl_max_mono (l := tail) f 0 (f head) (Nat.zero_le _)
      exact Nat.le_trans ih mono

private theorem foldl_max_bound_acc {l : List α} {bound : Nat} (f : α → Nat) (acc : Nat)
    (h_acc : acc ≤ bound) (h : ∀ x ∈ l, f x ≤ bound) :
    l.foldl (fun acc y => max acc (f y)) acc ≤ bound := by
  induction l generalizing acc with
  | nil => exact h_acc
  | cons hd tl ih =>
    simp_all only [List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp, List.foldl_cons]
    obtain ⟨left, right⟩ := h
    apply ih
    exact Nat.max_le_of_le_of_le h_acc left

private theorem foldl_max_bound {l : List α} {bound : Nat} (f : α → Nat)
    (h : ∀ x ∈ l, f x ≤ bound) :
    l.foldl (fun acc y => max acc (f y)) 0 ≤ bound := by
  induction l with
  | nil => simp only [List.foldl_nil]; exact Nat.zero_le _
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h_hd : f hd ≤ bound := h hd (by exact List.mem_cons_self)
    have h_tl : ∀ x ∈ tl, f x ≤ bound := fun x hx => h x (List.mem_cons_of_mem hd hx)
    have h₀ := ih h_tl
    simp_all only [List.mem_cons, or_true, implies_true, imp_self, forall_eq_or_imp, and_self, Nat.zero_le,
      Nat.max_eq_right, ge_iff_le]
    exact foldl_max_bound_acc f (f hd) h_hd h_tl

@[simp]
theorem depth_eq_one_of_zero (a : α) (f : Fin (ι a) → WType fun i => Fin (ι i)) (h : ι a = 0) :
    depth ⟨a, f⟩ = 1 := by
  unfold depth
  simp only
  rw [dif_pos h]

theorem depth_lt_depth_mk (a : α) (f : Fin (ι a) → WType fun i => Fin (ι i)) (i : Fin (ι a)) : depth (f i) < depth ⟨a, f⟩ := by
  unfold depth
  haveI : NeZero (ι a) := ⟨fin_nonzero i⟩
  simp only
  have h_mem : i ∈ (List.range (ι a)).map (Fin.ofNat (ι a)) := by
    rw [List.mem_map]
    exact ⟨i.val, List.mem_range.mpr i.isLt, Fin.ofNat_val_eq_self i⟩
  have h_le := foldl_max_le h_mem fun j => (f j).depth
  split
  rename_i x a f heq
  simp_all only
  have h_pos := Nat.lt_of_lt_of_le (depth_pos (mk a f)) h_le
  split <;> split <;> simp_all
  rename_i h₀ _
  haveI : NeZero (ι a) := ⟨h₀⟩
  have : (mk a f).depth = 1 + List.foldl (fun acc i => max acc (f i).depth) 0 ((List.range (ι a)).map (Fin.ofNat (ι a))) := by
    unfold depth
    simp only
    split
    . contradiction
    . simp only [Nat.add_left_cancel_iff]
      congr
      funext
      conv =>
        lhs
        arg 2
        unfold depth
  omega

end WType

abbrev WFin {α : Type u} (ι : α → Nat) (n : Nat) :=
  { w : WType fun a => Fin (ι a) // w.depth ≤ n }

namespace WFin

variable {n : Nat} {α : Type u} {ι : α → Nat}

def encodable_zero : Encodable (WFin ι 0) :=
  haveI : Encodable Empty := Empty.encodable
  let f : WFin ι 0 → Empty := fun ⟨_, h⟩ => False.elim <| Nat.not_lt_of_ge h (WType.depth_pos _)
  let finv : Empty → WFin ι 0 := by intro x; cases x
  have : ∀ x, finv (f x) = x := fun ⟨_, h⟩ => False.elim <| Nat.not_lt_of_ge h (WType.depth_pos _)
  Encodable.ofEquiv f finv this

def down (n : Nat) : WFin ι (n + 1) → Σ a, Fin (ι a) → WFin ι n
  | ⟨w, h⟩ => by
    obtain ⟨a, f⟩ := w
    have : ∀ i, (f i).depth ≤ n := fun i =>
      Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (WType.depth_lt_depth_mk a f i) h)
    exact ⟨a, fun i => ⟨f i, this i⟩⟩

def up (n : Nat) : (Σ a, Fin (ι a) → WFin ι n) → WFin ι (n + 1)
  | ⟨a, f⟩ =>
    let f' := fun i => (f i).val
    let hf' := fun i => (f i).property
    have : WType.depth ⟨a, f'⟩ ≤ n + 1 := by
      unfold WType.depth
      simp only
      split
      . exact Nat.le_add_left 1 n
      . rename_i h
        haveI : NeZero (ι a) := ⟨h⟩
        subst f'
        simp only
        rw [Nat.add_comm, Nat.add_le_add_iff_right]
        apply WType.foldl_max_bound
        intro i hi
        simp only [List.mem_map, List.mem_range] at hi
        obtain ⟨j, _, rfl⟩ := hi
        exact hf' (Fin.ofNat (ι a) j)
    ⟨⟨a, f'⟩, this⟩

variable [Encodable α]

def encodable_succ (n : Nat) (_ : Encodable (WFin ι n)) : Encodable (WFin ι (n + 1)) :=
  Encodable.ofEquiv (down n) (up n) (by intro ⟨⟨_, _⟩, _⟩; rfl)

instance _root_.WType.instEncodable : Encodable (WType fun i => Fin (ι i)) := by
  haveI h : ∀ n, Encodable (WFin ι n) := fun n => Nat.rec encodable_zero encodable_succ n
  let f : WType (fun i => Fin (ι i)) → Σ n, WFin ι n := fun w => ⟨w.depth, ⟨w, by exact Nat.le_refl _⟩⟩
  let finv : (Σ n, WFin ι n) → WType fun i => Fin (ι i) := fun p => p.2.1
  have : ∀ w, finv (f w) = w := fun _ => rfl
  exact Encodable.ofEquiv f finv this

end WFin
