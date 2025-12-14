import Sodium.Data.Encodable.WType

universe u v w uα uβ uγ uδ

structure PFunctor where
  A : Type u
  B : A → Type v

namespace PFunctor

variable {α : Type u} {β : Type v} {γ : Type w}

@[coe] def new (P : PFunctor.{uα,uβ}) (α : Type u) : Type (max u uα uβ) :=
  Σ x : P.A, P.B x → α

protected abbrev Id (P : PFunctor.{uα, uβ}) : Type (max uα uβ) :=
  Σ x : P.A, P.B x

instance : CoeFun PFunctor.{uα,uβ} (fun _ => Type u → Type (max u uα uβ)) := ⟨new⟩

instance : Inhabited PFunctor.{uα,uβ} := ⟨⟨default, default⟩⟩

variable (P : PFunctor.{uα,uβ})

instance [Inhabited P.A] [Inhabited α] : Inhabited (P α) := ⟨⟨default, default⟩⟩
instance [Inhabited P.A] [Inhabited (P.B default)] : Inhabited P.Id := ⟨⟨default, default⟩⟩

instance [Encodable P.A] [∀ a, Encodable (P.B a)] : Encodable P.Id := by unfold PFunctor.Id; infer_instance

def map (f : α → β) : P α → P β := fun ⟨a, g⟩ => ⟨a, f ∘ g⟩

instance : Functor P.new where map := P.map

@[simp] theorem map_eq_map {α β : Type u} (f : α → β) (x : P α) : f <$> x = P.map f x := rfl
@[simp] theorem map_eq (f : α → β) (a : P.A) (g : P.B a → α) : P.map f ⟨a, g⟩ = ⟨a, f ∘ g⟩ := rfl
@[simp] theorem id_map : ∀ x : P α, P.map id x = x := fun ⟨_, _⟩ => rfl
@[simp] theorem map_map (f : α → β) (g : β → γ) : ∀ x : P α, P.map g (P.map f x) = P.map (g ∘ f) x := fun ⟨_, _⟩ => rfl

instance : LawfulFunctor P.new where
  map_const := rfl
  id_map x := P.id_map x
  comp_map f g x := P.map_map f g x |>.symm

abbrev W : Type (max uα uβ) := @WType P.A P.B

variable {P}

def W.head : P.W → P.A
  | ⟨a, _⟩ => a

def W.children : ∀ x : P.W, P.B (W.head x) → P.W
  | ⟨_, f⟩ => f

def W.next : P.W → P P.W
  | ⟨a, f⟩ => ⟨a, f⟩

def W.mk : P P.W → P.W
  | ⟨a, f⟩ => ⟨a, f⟩

@[simp] theorem W.next_mk (p : P P.W) : W.next (W.mk p) = p := by cases p; rfl
@[simp] theorem W.mk_next (p : P.W) : W.mk (W.next p) = p := by cases p; rfl

def new.iget [DecidableEq P.A] [Inhabited α] (x : P α) (i : P.Id) : α :=
  if h : i.1 = x.1 then x.2 (cast (congrArg _ h) i.2) else default

@[simp] theorem fst_map (x : P α) (f : α → β) : (P.map f x).1 = x.1 := by cases x; rfl

@[simp] theorem iget_map [DecidableEq P.A] [Inhabited α] [Inhabited β] (x : P α)
    (f : α → β) (i : P.Id) (h : i.1 = x.1) : (P.map f x).iget i = f (x.iget i) := by
  simp only [new.iget, fst_map, *]
  cases x
  rfl

@[reducible]
def comp (P₂ : PFunctor.{uγ,uδ}) (P₁ : PFunctor.{uα,uβ}) : PFunctor.{max uα uγ uδ, max uβ uδ} where
  A := Σ a₂ : P₂.A, P₂.B a₂ → P₁.A
  B | ⟨a, k⟩ => Σ u : P₂.B a, P₁.B (k u)

def comp.mk (P₂ : PFunctor.{uγ,uδ}) (P₁ : PFunctor.{uα,uβ}) {α : Type u} (x : P₂ (P₁ α)) : comp P₂ P₁ α :=
  ⟨⟨x.1, Sigma.fst ∘ x.2⟩, fun ⟨a, k⟩ => (x.2 a).2 k⟩

def comp.get {P₂ : PFunctor.{uγ,uδ}} {P₁ : PFunctor.{uα,uβ}} {α : Type u} (x : comp P₂ P₁ α) : P₂ (P₁ α) :=
  ⟨x.1.1, fun a₂ => ⟨x.1.2 a₂, fun a₁ => x.2 ⟨a₂, a₁⟩⟩⟩

notation a " ⊚ " b => comp a b
notation "mk% " P₂ ", " P₁ ", " x => comp.mk P₂ P₁ x
notation "get% " x => comp.get x

protected def W.cases {X : P.W → Sort w} (f : ∀ x : P P.W, X (W.mk x)) (p : P.W) : X p :=
  suffices X (W.mk (W.next p)) by
    rw [← W.mk_next p]
    exact this
  f _

@[simp] theorem W.cases_mk {X : P.W → Sort w} (p : P P.W) (f : ∀ x : P P.W, X (W.mk x)) : W.cases f (W.mk p) = f p := by
  simp only [W.mk, W.cases, W.next]
  cases p; simp only [eq_mpr_eq_cast, cast_eq]

end PFunctor
