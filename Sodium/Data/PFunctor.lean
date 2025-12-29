import Batteries.Logic
import Batteries.Tactic.Trans
import Sodium.Inhabit
import Sodium.Data.Encodable.WType

universe u v w uα uβ uγ uδ

/-- A universe-polymorphic function. -/
structure PFunctor where
  A : Type u
  B : A → Type v

namespace PFunctor

variable {α : Type u} {β : Type v} {γ : Type w}

@[coe] def new (P : PFunctor.{uα,uβ}) (α : Type u) : Type (max u uα uβ) :=
  Σ x : P.A, P.B x → α

protected abbrev Id (P : PFunctor.{uα, uβ}) : Type (max uα uβ) :=
  Σ x : P.A, P.B x

protected abbrev Path (P : PFunctor.{uα, uβ}) := List P.Id

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

inductive Cofix (P : PFunctor.{uα, uβ}) : Nat → Type (max uα uβ)
| roll : Cofix P 0
| intro {n} : ∀ a, (P.B a → Cofix P n) → Cofix P n.succ

namespace Cofix

protected def default [Inhabited P.A] : ∀ n, Cofix P n
| 0 => roll
| .succ n => intro default fun _ => Cofix.default n

instance [Inhabited P.A] {n} : Inhabited (Cofix P n) := ⟨Cofix.default n⟩
instance subsingleton : Subsingleton (Cofix P 0) := ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

inductive Agree : ∀ {n}, Cofix P n → Cofix P n.succ → Prop
| fold (x : Cofix P 0) (y : Cofix P 1) : Agree x y
| intro {n} {a} (x : P.B a → Cofix P n) (y : P.B a → Cofix P n.succ) : (∀ i : P.B a, Agree (x i) (y i)) → Agree (.intro a x) (.intro a y)

@[simp] theorem agree_fold_idx {x : Cofix P 0} {y : Cofix P 1} : Agree x y := by constructor

def Agree.head : ∀ {n}, Cofix P (Nat.succ n) → P.A
| _, .intro i _ => i

def Agree.children : ∀ {n} (x : Cofix P (Nat.succ n)), P.B (Agree.head x) → Cofix P n
| _, .intro _ f => f

theorem agree_intro
    {n} (x : Cofix P <| Nat.succ n) (y : Cofix P <| Nat.succ n + 1)
    {i j} (h : i ≍ j) (agree : Agree x y)
    : Agree (Agree.children x i) (Agree.children y j) := by
  obtain - | ⟨_, _, ha⟩ := agree
  cases h
  apply ha

def cut : ∀ {n}, Cofix P n.succ → Cofix P n
| 0, .intro _ _ => .roll
| .succ _, .intro i f => .intro i <| cut ∘ f

def search {X} (f : X → P X) : X → ∀ n, Cofix P n
| _, 0 => roll
| j, .succ _ => intro (f j).1 fun i => search f ((f j).2 i) _

theorem cut_eq_of_agree {n} (x : Cofix P n) (y : Cofix P n.succ) (h : Agree x y) : cut y = x := by
  induction n with
  | zero =>
    cases x
    cases y
    rfl
  | succ n ih =>
    cases h with | intro f y h' =>
      simp only [cut, Function.comp_def]
      congr with y
      exact ih _ _ (h' y)

theorem search_agreement {X} (f : X → P X) (i : X) (n : Nat) : Agree (search f i n) (search f i n.succ) := by
  induction n generalizing i with
  | zero => constructor
  | succ n ih => exact .intro _ _ fun _ => ih _

def Consensus (x : ∀ n, Cofix P n) := ∀ n, Agree (x n) (x n.succ)

theorem agree_with_consensus (n m : Nat) (x : ∀ n, Cofix P n) (h : Consensus x) : Agree.head (x n.succ) = Agree.head (x m.succ) := by
  suffices ∀ n, Agree.head (x <| Nat.succ n) = Agree.head (x 1) by simp [this]
  clear n m
  intro n
  rcases hx : x n.succ with - | ⟨_, f⟩
  cases h₁ : x 1
  dsimp only [Agree.head]
  induction n with
  | zero =>
    rw [h₁] at hx
    cases hx
    rfl
  | succ n ih =>
    have := h n.succ
    cases h₂ : x n.succ
    rw [hx, h₂] at this
    apply ih (cut ∘ f)
    rw [h₂]
    obtain - | ⟨_, _, ha⟩ := this
    congr
    funext j
    dsimp only [Function.comp_apply]
    rw [cut_eq_of_agree]
    apply ha

end Cofix

/-- An approximation of a universe-polymorphic function. -/
structure PFin (P : PFunctor.{uα, uβ}) where
  approx : ∀ n, Cofix P n
  consistent : Cofix.Consensus approx

/-- The universal monad. -/
def M (P : PFunctor.{uα, uβ}) := PFin P

theorem M.default_consistent [Inhabited P.A] : ∀ n, Cofix.Agree (default : Cofix P n) default
| 0 => Cofix.Agree.fold _ _
| .succ n => Cofix.Agree.intro _ _ fun _ => M.default_consistent n

instance M.inhabited [Inhabited P.A] : Inhabited (M P) where
  default := {
    approx := default
    consistent := @M.default_consistent _ _
  }

instance PFin.inhabited [Inhabited P.A] : Inhabited P.PFin := show Inhabited P.M by infer_instance

namespace M

theorem ext (x y : P.M) (h : ∀ n, x.approx n = y.approx n) : x = y := by
  cases x
  cases y
  congr with n
  apply h

def corec {X} (f : X → P X) (init : X) : P.M where
  approx := Cofix.search f init
  consistent := Cofix.search_agreement _ _

def head (x : P.M) := Cofix.Agree.head (x.approx 1)

def children (x : P.M) (i : P.B (head x)) : P.M := by
  have := fun n => @Cofix.agree_with_consensus _ n 0 x.approx x.consistent
  refine {approx := ?_, consistent := ?_}
  exact fun n => Cofix.Agree.children (x.approx _) (cast (congrArg _ <| by simp only [head, this]) i)
  intro n
  have p := x.consistent n.succ
  apply Cofix.agree_intro _ _ _ p
  trans i
  apply cast_heq
  symm
  apply cast_heq

def ichildren [Inhabited P.M] [DecidableEq P.A] (i : P.Id) (x : P.M) : P.M :=
  if h : i.1 = head x then children x (cast (congrArg _ <| by simp only [head, h]) i.2)
  else default

theorem agree_with_approx (n m : Nat) (x : P.M) : Cofix.Agree.head (x.approx n.succ) = Cofix.Agree.head (x.approx m.succ) :=
  Cofix.agree_with_consensus n m _ x.consistent

theorem head_reduce_left : ∀ (x : P.M) (n : Nat), head x = Cofix.Agree.head (x.approx n.succ)
| ⟨_, h⟩, _ => Cofix.agree_with_consensus _ _ _ h

theorem head_reduce_right : ∀ (x : P.M) (n : Nat), Cofix.Agree.head (x.approx n.succ) = head x
| ⟨_, h⟩, _ => Cofix.agree_with_consensus _ _ _ h

theorem cut_approx (x : P.M) (n : Nat) : Cofix.cut (x.approx n.succ) = x.approx n :=
  Cofix.cut_eq_of_agree _ _ (x.consistent _)

def dest : P.M → P P.M
| x => ⟨head x, fun i => children x i⟩

protected def Cofix.mk (x : P P.M) : ∀ n, Cofix P n
| 0 => Cofix.roll
| .succ n => Cofix.intro x.1 fun i => (x.2 i).approx n

theorem mk_consensus (x : P P.M) : Cofix.Consensus (Cofix.mk x)
| 0 => by constructor
| .succ n => by
  constructor
  intro i
  apply (x.2 i).consistent

protected def mk (x : P P.M) : P.M where
  approx := Cofix.mk x
  consistent := mk_consensus x

inductive Agree : Nat → P.M → P.M → Prop
| sync (x y : P.M) : Agree 0 x y
| intro {n : Nat} {a} (x y : P.B a → P.M) {α β}
  : α = M.mk ⟨a, x⟩ → β = M.mk ⟨a, y⟩ → (∀ i, Agree n (x i) (y i)) → Agree n.succ α β

@[simp] theorem dest_mk (x : P P.M) : dest (M.mk x) = x := rfl

@[simp] theorem mk_dest (x : P.M) : M.mk (dest x) = x := by
  apply ext
  intro n
  dsimp only [M.mk]
  induction n with
  | zero => apply @Subsingleton.elim _ Cofix.subsingleton
  | succ n => ?_
  dsimp only [Cofix.mk, dest, head]
  rcases h : x.approx n.succ with - | ⟨hd, ch⟩
  have h' : hd = Cofix.Agree.head (x.approx 1) := by
    rw [← Cofix.agree_with_consensus n, h, Cofix.Agree.head]
    apply x.consistent
  revert ch
  rw [h']
  intro ch h
  congr
  ext a
  dsimp only [children]
  generalize c : cast _ a = b
  rw [cast_eq_iff_heq] at c
  revert b
  rw [h]
  intro _ c
  cases c
  rfl

theorem mk_inj {x y : P P.M} (h : M.mk x = M.mk y) : x = y := by rw [← dest_mk x, h, dest_mk]

def deconstruct {N : P.M → Sort _} (f : ∀ x : P P.M, N (M.mk x)) (x : P.M) : N x :=
  suffices N (M.mk (dest x)) by
    rw [← mk_dest x]
    exact this
  f _

protected abbrev cases {N : P.M → Sort _} (x : P.M) (f : ∀ x : P P.M, N (M.mk x)) : N x :=
  deconstruct f x

protected abbrev «match» {N : P.M → Sort _} (x : P.M) (f : ∀ a b, N (M.mk ⟨a, b⟩)) : N x :=
  M.cases x fun ⟨a, c⟩ => f a c

theorem construct (a : P.A) (f : P.B a → P.M) (i : Nat)
: (M.mk ⟨a, f⟩).approx i.succ = Cofix.intro a fun j => (f j).approx i := rfl

@[simp] theorem agree_with_cofix {n : Nat} (x : P.M) : Agree n x x := by
  induction n generalizing x with | zero => ?_ | succ _ ih => ?_ <;>
  induction x using M.match <;> constructor <;> try rfl
  intro
  apply ih

theorem cofix_iff_agree {n : Nat} (x y : P.M) : Cofix.Agree (x.approx n) (y.approx n.succ) ↔ Agree n x y := by
  constructor <;> intro h
  . induction n generalizing x y with
    | zero => constructor
    | succ _ ih =>
      induction x using M.match
      induction y using M.match
      simp only [construct] at h
      obtain - | ⟨_, _, ha⟩ := h
      constructor <;> try rfl
      intro i
      apply ih
      apply ha
  . induction n generalizing x y with
    | zero => constructor
    | succ _ ih =>
      obtain - | @⟨_, a, α, β⟩ := h
      induction x using M.match with | _ a₁ f₁
      induction y using M.match with | _ a₂ f₂
      simp only [construct]
      have ha₁ := mk_inj ‹M.mk ⟨a₁, f₁⟩ = M.mk ⟨a, α⟩›
      cases ha₁
      replace ha₂ := mk_inj ‹M.mk ⟨a₂, f₂⟩ = M.mk ⟨a, β⟩›
      cases ha₂
      constructor
      intro i
      apply ih
      simp [*]

@[simp] theorem deconstruct_mk {N : P.M → Sort _} (x : P P.M) (f : ∀ x : P P.M, N (M.mk x))
: M.deconstruct f (M.mk x) = f x := rfl

@[simp] theorem cases_mk {N : P.M → Sort _} (x : P P.M) (f : ∀ x : P P.M, N (M.mk x))
: M.cases (M.mk x) f = f x := deconstruct_mk x f

@[simp] theorem construct_mk {N : P.M → Sort _} {a} (x : P.B a → P.M)
  (f : ∀ (a) (f : P.B a → P.M), N (M.mk ⟨a, f⟩))
: M.match (M.mk ⟨a, x⟩) f = f a x := @deconstruct_mk P N ⟨a, x⟩ fun ⟨a, y⟩ => f a y

end M

inductive Net : List P.Id → P.M → Prop
| nil (x : P.M) : Net [] x
| cons (xs : List P.Id) (x : P.M) {a} (f : P.B a → P.M) (i : P.B a) : x = M.mk ⟨a, f⟩ → Net xs (f i) → Net (⟨a, i⟩ :: xs) x

theorem net_ext {xs : List P.Id} {a α} {f : P.B a → P.M} {i : P.B α} : Net (⟨α, i⟩ :: xs) (M.mk ⟨a, f⟩) → a = α := by
  generalize h : M.mk ⟨a, f⟩ = x
  rintro (_ | ⟨_, _, _, _, rfl, _⟩)
  cases M.mk_inj h
  rfl

theorem net_idx {xs : List P.Id} {a} {f : P.B a → P.M} {i : P.B a} : Net (⟨a, i⟩ :: xs) (M.mk ⟨a, f⟩) → Net xs (f i) := by
  generalize h : M.mk ⟨a, f⟩ = x
  rintro (_ | ⟨_, _, _, _, rfl, hp⟩)
  cases M.mk_inj h
  exact hp

def navigate [DecidableEq P.A] [Inhabited P.M] : List P.Id → P.M → P.M
| [], x => x
| ⟨a, i⟩ :: ps, x =>
  M.match (N := fun _ => P.M) x fun α f =>
    if h : a = α then navigate ps (f <| cast (by rw [h]) i)
    else default (α := P.M)

def route [DecidableEq P.A] [Inhabited P.M] (ps : List P.Id) : P.M → P.A :=
  fun x : P.M => M.head (navigate ps x)

theorem route_default_idx [DecidableEq P.A] [Inhabited P.M] (ps : List P.Id) (x : P.M) (h : ¬Net ps x) : route ps x = M.head default := by
  induction ps generalizing x with
  | nil =>
    exfalso
    apply h
    constructor
  | cons hd tl ih =>
    obtain ⟨a, i⟩ := hd
    induction x using M.match with | _ α f
    simp only [route, navigate] at ih ⊢
    by_cases h₀ : a = α
    . subst α
      simp only [dif_pos, M.construct_mk]
      rw [ih]
      intro h₁
      apply h
      constructor <;> try rfl
      apply h₁
    . simp [*]

@[simp] theorem head_mk (x : P P.M) : M.head (M.mk x) = x.1 :=
  Eq.symm <| calc
    x.1 = (M.dest (M.mk x)).1 := by rw [M.dest_mk]
    _ = M.head (M.mk x) := rfl

theorem children_mk {a} (x : P.B a → P.M) (i : P.B (M.head (M.mk ⟨a, x⟩))) : M.children (M.mk ⟨a, x⟩) i = x (cast (by rw [head_mk]) i) := by
  apply M.ext
  intro n
  rfl

@[simp] theorem ichildren_mk [DecidableEq P.A] [Inhabited P.M] (x : P P.M) (i : P.Id) : M.ichildren i (M.mk x) = x.iget i := by
  dsimp only [navigate, PFunctor.new.iget]
  congr with h

@[simp] theorem navigate_mk [DecidableEq P.A] [Inhabited P.M]
    (ps : List P.Id) {a} (f : P.B a → P.M) {i : P.B a} : navigate (⟨_, i⟩ :: ps) (M.mk ⟨a, f⟩) = navigate ps (f i) := by
  simp only [navigate, dif_pos, navigate, M.construct_mk]
  rfl

@[simp] theorem route_nil_idx [DecidableEq P.A] [Inhabited P.M] {a} (f : P.B a → P.M) : route .nil (M.mk ⟨a, f⟩) = a := rfl

@[simp] theorem route_cons_idx [DecidableEq P.A] [Inhabited P.M] (ps : List P.Id) {a} (f : P.B a → P.M) {i}
: route (⟨a, i⟩ :: ps) (M.mk ⟨a, f⟩) = route ps (f i) := by simp only [route, navigate_mk]

theorem corec {X} (f : X → P X) (x : X) : M.corec f x = M.mk (P.map (M.corec f) (f x)) := by
  dsimp only [M.corec, M.mk]
  congr with n
  rcases n with - | n
  . dsimp only [Cofix.search, M.Cofix.mk]
  . dsimp only [Cofix.search, M.Cofix.mk]
    cases f x
    dsimp only [PFunctor.map]
    congr

protected def lrec {α : Type _} (F : ∀ X, (α → X) → α → P X) : α → P.M := M.corec (F _ id)

protected def rrec {α : Type u} (F : ∀ {X : Type (max u uα uβ)}, (α → X) → α → P.M ⊕ P X) (x : α) : P.M :=
  let k := fun _ k (a : P.M ⊕ α) =>
    let y := match a with
    | .inl x => Sum.inl x
    | .inr x => F (k ∘ Sum.inr) x
    match y with
    | .inr y => y
    | .inl y => P.map (k ∘ Sum.inl) (M.dest y)
  PFunctor.lrec k (@Sum.inr P.M _ x)

theorem ext_aux [Inhabited P.M] [DecidableEq P.A] {n : Nat} (x y z : P.M)
  (hx : M.Agree n z x) (hy : M.Agree n z y)
  (hrec : ∀ ps : List P.Id, n = ps.length → route ps x = route ps y)
: x.approx n.succ = y.approx n.succ := by
  induction n generalizing x y z with
  | zero =>
    specialize hrec [] rfl
    induction x using M.match
    induction y using M.match
    simp only [route_nil_idx] at hrec
    subst hrec
    simp only [M.construct, heq_iff_eq, Cofix.intro.injEq, eq_iff_true_of_subsingleton, and_self]
  | succ n ih =>
    cases hx
    cases hy
    induction x using M.match
    induction y using M.match
    subst z
    iterate 3 (have := M.mk_inj ‹_›; cases this)
    rename_i ih a f₃ f₂ ha₂ _ _ h₂ _ _ f₁ h₁ ha₁ clr
    simp only [M.construct]
    have := M.mk_inj h₁
    cases this
    clear h₁
    have := M.mk_inj h₂
    cases this
    clear h₂
    congr
    ext i
    apply ih
    . solve_by_elim
    . solve_by_elim
    intro ps h
    specialize hrec (⟨_, i⟩ :: ps) (congrArg _ h)
    simp only [route_cons_idx] at hrec
    exact hrec

@[ext] theorem ext [Inhabited P.M] [DecidableEq P.A] (x y : P.M) (h : ∀ ps : List P.Id, route ps x = route ps y) : x = y := by
  apply M.ext
  intro i
  induction i with
  | zero => apply Subsingleton.elim
  | succ i ih =>
    apply ext_aux x y x
    . rw [← M.cofix_iff_agree]
      apply x.consistent
    . rw [← M.cofix_iff_agree, ih]
      apply y.consistent
    intro ps hi
    dsimp only [route] at h
    cases hi
    apply h ps

structure Connect (R : P.M → P.M → Prop) : Prop where
  send : ∀ {a α} {f₀ f₁}, R (M.mk ⟨a, f₀⟩) (M.mk ⟨α, f₁⟩) → a = α
  recv : ∀ {a} {f₀ f₁ : P.B a → P.M}, R (M.mk ⟨a, f₀⟩) (M.mk ⟨a, f₁⟩) → ∀ i : P.B a, R (f₀ i) (f₁ i)

theorem simulate [Inhabited P.M] [DecidableEq P.A] {R : P.M → P.M → Prop} (conn : Connect R) (s₁ s₂) (ps : List P.Id)
: R s₁ s₂ → Net ps s₁ ∨ Net ps s₂ → route ps s₁ = route ps s₂
∧ ∃ (a : _) (f₀ f₁ : P.B a → P.M), navigate ps s₁ = M.mk ⟨a, f₀⟩ ∧ navigate ps s₂ = M.mk ⟨a, f₁⟩
∧ ∀ i : P.B a, R (f₀ i) (f₁ i) := by
  intro h₀ hh
  induction s₁ using M.match with | _ a₀ f₀
  induction s₂ using M.match with | _ a₁ f₁
  obtain rfl : a₀ = a₁ := conn.send h₀
  induction ps generalizing a₀ f₀ f₁ with
  | nil =>
    exists rfl, a₀, f₀, f₁, rfl, rfl
    apply conn.recv h₀
  | cons i ps ih => ?_
  obtain ⟨a₂, i⟩ := i
  obtain rfl : a₀ = a₂ := by rcases hh with hh | hh <;> cases net_ext hh <;> rfl
  dsimp only [route] at ih ⊢
  have h₁ := conn.recv h₀ i
  induction h₂ : f₀ i using M.match with | _ b₀ g₀
  induction h₃ : f₁ i using M.match with | _ b₁ g₁
  simp only [h₂, h₃, navigate_mk] at ih ⊢
  rw [h₂, h₃] at h₁
  obtain rfl : b₀ = b₁ := conn.send h₁
  apply ih _ _ _ h₁
  rw [← h₂, ← h₃]
  apply Or.imp net_idx net_idx hh

theorem inhabit [Nonempty P.M] (R : P.M → P.M → Prop) (conn : Connect R) : ∀ s₁ s₂, R s₁ s₂ → s₁ = s₂ := by
  inhabit M P
  classical
  intro s₁ s₂ hR
  apply ext
  intro ps
  by_cases h : Net ps s₁ ∨ Net ps s₂
  . have := simulate conn _ _ ps hR h
    exact this.left
  . rw [not_or] at h
    obtain ⟨h₀, h₁⟩ := h
    simp only [route_default_idx, *, not_false_iff]

theorem link_dest (f : α → P α) (x : α) : M.dest (M.corec f x) = P.map (M.corec f) (f x) := by rw [corec, M.dest_mk]

theorem link (R : P.M → P.M → Prop) (h : ∀ x y, R x y → ∃ a f₀ f₁, M.dest x = ⟨a, f₀⟩ ∧ M.dest y = ⟨a, f₁⟩ ∧ ∀ i, R (f₀ i) (f₁ i))
: ∀ x y, R x y → x = y := by
  intro x y hR
  have := Inhabited.mk x.head
  apply inhabit R _ _ _ hR
  clear hR x y
  constructor
  . intro a α f₀ f₁ ih
    rcases h _ _ ih with ⟨b, g₀, g₁, h₀, h₁, h₂⟩
    clear h
    replace h₀ := congrArg Sigma.fst h₀
    replace h₁ := congrArg Sigma.fst h₁
    simp only [M.dest_mk] at h₀ h₁
    rw [h₀, h₁]
  . intro a f₀ f₁ ih
    rcases h _ _ ih with ⟨b, g₀, g₁, h₀, h₁, h₂⟩
    clear h
    simp only [M.dest_mk] at h₀ h₁
    cases h₀
    cases h₁
    apply h₂

theorem bisim {α : Type _} {Q : α → Prop} (u v : α → P.M)
  (h : ∀ x, Q x → ∃ a f₀ f₁, M.dest (u x) = ⟨a, f₀⟩ ∧ M.dest (v x) = ⟨a, f₁⟩ ∧ ∀ i, ∃ y, Q y ∧ f₀ i = u y ∧ f₁ i = v y)
: ∀ x, Q x → u x = v x := fun x hx =>
  let R := fun w z : P.M => ∃ y, Q y ∧ w = u y ∧ z = v y
  @link P R
    (fun _ _ ⟨y, hy, xeq, yeq⟩ => let ⟨a, f₀, f₁, hu, hv, hw⟩ := h y hy; ⟨a, f₀, f₁, xeq.symm ▸ hu, yeq.symm ▸ hv, hw⟩)
    _ _ ⟨x, hx, rfl, rfl⟩

end PFunctor
