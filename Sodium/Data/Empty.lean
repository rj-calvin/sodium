universe u v w

variable {α : Sort u} {β : Sort v} {γ : Sort w}

class IsEmpty (α : Sort u) : Prop where
  protected false : α → False

instance : IsEmpty False := ⟨id⟩

instance Empty.instIsEmpty : IsEmpty Empty := ⟨Empty.elim⟩
instance PEmpty.instIsEmpty : IsEmpty PEmpty := ⟨PEmpty.elim⟩
instance Fin.instIsEmpty : IsEmpty (Fin 0) := ⟨Fin.elim0⟩

protected theorem Function.isEmpty [IsEmpty β] (f : α → β) : IsEmpty α :=
  ⟨fun x => IsEmpty.false (f x)⟩

protected theorem Function.isEmptyOfSurjective [IsEmpty α] {f : α → β} (hf : ∀ b, ∃ a, f a = b) : IsEmpty β :=
  ⟨fun y => let ⟨x, _⟩ := hf y; IsEmpty.false x⟩

instance {p : α → Sort w} [∀ x, IsEmpty (p x)] [h : Nonempty α] : IsEmpty (∀ x, p x) :=
  h.elim fun x => Function.isEmpty fun y => y x

instance PProd.instIsEmpty_left [IsEmpty α] : IsEmpty (PProd α β) :=
  Function.isEmpty PProd.fst

instance PProd.instIsEmpty_right [IsEmpty β] : IsEmpty (PProd α β) :=
  Function.isEmpty PProd.snd

instance Prod.instIsEmpty_left {α β} [IsEmpty α] : IsEmpty (α × β) :=
  Function.isEmpty Prod.fst

instance Prod.instIsEmpty_right {α β} [IsEmpty β] : IsEmpty (α × β) :=
  Function.isEmpty Prod.snd

instance Quot.instIsEmpty [IsEmpty α] {r : α → α → Prop} : IsEmpty (Quot r) :=
  Function.isEmptyOfSurjective Quot.exists_rep

instance Quotient.instIsEmpty [IsEmpty α] {s : Setoid α} : IsEmpty (Quotient s) :=
  Quot.instIsEmpty

instance PSum.instIsEmpty [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕' β) :=
  ⟨fun x => PSum.rec IsEmpty.false IsEmpty.false x⟩

instance Sum.instIsEmpty {α β} [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕ β) :=
  ⟨fun x => Sum.rec IsEmpty.false IsEmpty.false x⟩

instance Subtype.instIsEmpty [IsEmpty α] (p : α → Prop) : IsEmpty (Subtype p) :=
  ⟨fun x => IsEmpty.false x.1⟩

theorem Subtype.isEmpty_of_false {p : α → Prop} (hp : ∀ a, ¬p a) : IsEmpty (Subtype p) :=
  ⟨fun x => hp _ x.2⟩

instance Subtype.isEmpty_false : IsEmpty { _a : α // False } :=
  Subtype.isEmpty_of_false fun _ => id

instance Sigma.isEmpty_left {α} [IsEmpty α] {σ : α → Type w} : IsEmpty (Sigma σ) :=
  Function.isEmpty Sigma.fst

@[elab_as_elim]
def isEmptyElim [IsEmpty α] {p : α → Sort w} (a : α) : p a :=
  (IsEmpty.false a).elim

theorem isEmpty_iff : IsEmpty α ↔ α → False :=
  ⟨@IsEmpty.false α, IsEmpty.mk⟩

namespace IsEmpty

open Function

@[elab_as_elim]
protected def elim {α : Sort u} (_ : IsEmpty α) {p : α → Sort w} (a : α) : p a :=
  isEmptyElim a

protected def elim' {β : Sort v} (h : IsEmpty α) (a : α) : β :=
  (h.false a).elim

protected theorem prop_iff {p : Prop} : IsEmpty p ↔ ¬p :=
  isEmpty_iff

variable [IsEmpty α]

@[simp]
theorem forall_iff {p : α → Prop} : (∀ a, p a) ↔ True :=
  iff_true_intro isEmptyElim

@[simp]
theorem exists_iff {p : α → Prop} : (∃ a, p a) ↔ False :=
  iff_false_intro fun ⟨x, _⟩ ↦ IsEmpty.false x

instance (priority := 100) : Subsingleton α :=
  ⟨isEmptyElim⟩

end IsEmpty

private theorem not_iff_comm {a b} : (¬a ↔ b) ↔ (¬b ↔ a) := open scoped Classical in Decidable.not_iff_comm
private theorem not_iff_not {a b} : (¬a ↔ ¬b) ↔ (a ↔ b) := open scoped Classical in Decidable.not_iff_not
private theorem not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b := open scoped Classical in Decidable.not_and_iff_not_or_not

@[simp]
theorem not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α :=
  ⟨fun h ↦ ⟨fun x ↦ h ⟨x⟩⟩, fun h1 h2 ↦ h2.elim h1.elim⟩

@[simp]
theorem not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α :=
  not_iff_comm.mp not_nonempty_iff

@[simp]
theorem isEmpty_Prop {p : Prop} : IsEmpty p ↔ ¬p := by
  simp only [← not_nonempty_iff, nonempty_prop]

private theorem nonempty_pi {ι} {α : ι → Sort w} : Nonempty (∀ i, α i) ↔ ∀ i, Nonempty (α i) :=
  ⟨fun ⟨f⟩ a => ⟨f a⟩, @Pi.instNonempty _ _⟩

@[simp]
theorem isEmpty_pi {π : α → Sort w} : IsEmpty (∀ a, π a) ↔ ∃ a, IsEmpty (π a) := by
  simp only [← not_nonempty_iff, nonempty_pi, Classical.not_forall]

private theorem exists_true_iff_nonempty {α : Sort u} : (∃ _ : α, True) ↔ Nonempty α :=
  Iff.intro (fun ⟨a, _⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨a, trivial⟩

theorem isEmpty_fun : IsEmpty (α → β) ↔ Nonempty α ∧ IsEmpty β := by
  rw [isEmpty_pi, ← exists_true_iff_nonempty, ← exists_and_right, true_and]

@[simp]
theorem nonempty_fun : Nonempty (α → β) ↔ IsEmpty α ∨ Nonempty β :=
  not_iff_not.mp <| by rw [not_or, not_nonempty_iff, not_nonempty_iff, isEmpty_fun, not_isEmpty_iff]

private theorem nonempty_sigma {α : Type u} {γ : α → Type w} : Nonempty (Σ a : α, γ a) ↔ ∃ a : α, Nonempty (γ a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩

@[simp]
theorem isEmpty_sigma {α} {E : α → Type w} : IsEmpty (Sigma E) ↔ ∀ a, IsEmpty (E a) := by
  simp only [← not_nonempty_iff, nonempty_sigma, not_exists]

private theorem nonempty_psigma {α : Sort u} {γ : α → Sort w} : Nonempty (PSigma γ) ↔ ∃ a : α, Nonempty (γ a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩

@[simp]
theorem isEmpty_psigma {α} {E : α → Sort w} : IsEmpty (PSigma E) ↔ ∀ a, IsEmpty (E a) := by
  simp only [← not_nonempty_iff, nonempty_psigma, not_exists]

private theorem Classical.nonempty_subtype {α : Sort u} {p : α → Prop} : Nonempty (Subtype p) ↔ ∃ a : α, p a :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, c⟩) fun ⟨a, c⟩ => ⟨⟨a, c⟩⟩

theorem isEmpty_subtype (p : α → Prop) : IsEmpty (Subtype p) ↔ ∀ x, ¬p x := by
  simp only [← not_nonempty_iff, Classical.nonempty_subtype, not_exists]

private theorem nonempty_prod {α β} : Nonempty (α × β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩

@[simp]
theorem isEmpty_prod {α : Type u} {β : Type v} : IsEmpty (α × β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_prod, not_and_or]

private theorem nonempty_pprod {α β} : Nonempty (PProd α β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩

@[simp]
theorem isEmpty_pprod : IsEmpty (PProd α β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_pprod, not_and_or]

private theorem nonempty_sum {α β} : Nonempty (α ⊕ β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | .inl a => Or.inl ⟨a⟩
      | .inr b => Or.inr ⟨b⟩)
    fun h =>
      match h with
      | .inl ⟨a⟩ => ⟨Sum.inl a⟩
      | .inr ⟨b⟩ => ⟨Sum.inr b⟩

@[simp]
theorem isEmpty_sum {α β} : IsEmpty (α ⊕ β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_sum, not_or]

private theorem nonempty_psum {α β} : Nonempty (α ⊕' β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | .inl a => Or.inl ⟨a⟩
      | .inr b => Or.inr ⟨b⟩)
    fun h =>
      match h with
      | .inl ⟨a⟩ => ⟨PSum.inl a⟩
      | .inr ⟨b⟩ => ⟨PSum.inr b⟩

@[simp]
theorem isEmpty_psum {α β} : IsEmpty (α ⊕' β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_psum, not_or]

private theorem nonempty_ulift {α} : Nonempty (ULift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩

@[simp]
theorem isEmpty_ulift {α} : IsEmpty (ULift α) ↔ IsEmpty α := by
  simp only [← not_nonempty_iff, nonempty_ulift]

private theorem nonempty_plift {α} : Nonempty (PLift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩

@[simp]
theorem isEmpty_plift {α} : IsEmpty (PLift α) ↔ IsEmpty α := by
  simp only [← not_nonempty_iff, nonempty_plift]

theorem wellFounded_of_isEmpty {α} [IsEmpty α] (r : α → α → Prop) : WellFounded r :=
  ⟨isEmptyElim⟩
