import Sodium.Data.Encodable.WType
import Sodium.Data.PFunctor
import Sodium.Ethos.Weight
import Sodium.FFI.Ristretto

open Lean Sodium Aesop Ethos
set_option linter.unreachableTactic false

variable ⦃γ : Inhabited Prop⦄ {τ : Sodium (PLift (@default Prop γ))}

/--
A point on Curve25519 relative to `x : Weight`.
-/
structure Prob (x : Weight) extends Weight where
  fpt : SecretVector τ (@Weight.quantize toPSigma .global)
  tbf : fpt.isZero = false := by
        try contradiction
    <;> try assumption
    <;> try native_decide
    <;> exfalso
    <;> try contradiction
    <;> run_tac throwPostpone (α := ULift String)

namespace Prob

open FFI.Ristretto

notation "Δ% " τ ", " x => @Prob _ τ x

set_option quotPrecheck false in
notation "δ% " u ", " x " : " o =>
  ∀ (hδ : @Ethos.Weight.quantize x Aesop.ScopeName.global = (u).toNat := o), Δ% $(mkIdent `τ), x

def toWeight (_ : Δ% τ, x) : Weight := x

def toSecret (γ : Δ% τ, x)
  (h : x.quantize .global = @Weight.quantize γ.toPSigma .global := by
    try assumption <;> try simp_all <;> try contradiction <;> native_decide)
  : SecretVector τ <| x.quantize .global := h ▸ γ.fpt

abbrev num (γ : Δ% τ, x) := (@toWeight _ _ _ γ).num
abbrev den (γ : Δ% τ, x) := (@toWeight _ _ _ γ).den

@[simp] theorem weight_idx : ∀ γ : Δ% τ, x, γ.toWeight = x := by intro; rfl

end Prob

namespace Ethos.Ristretto

open FFI.Ristretto

/--
If it is possible to study the rotation of the stars by studying the position of atoms,
does it not follow that the position of atoms are decided by the rotation of the stars?
-/
def unimax : Level := .ofNat BYTES

@[simp] theorem unimax_idx : unimax = 32 := rfl
@[simp] theorem unimax_pseudo_idx : @some Nat (Nat.succ 31) = unimax.toNat := rfl
@[simp] theorem unimax_partial_idx : @some Nat 64 = unimax.toNat.bind fun o => pure <| o + Nat.succ 31 := rfl

@[simp] theorem bytes_lvl : BYTES = SCALARBYTES := rfl
@[simp] theorem scalarbytes_lvl : SCALARBYTES = unimax.toNat := rfl
@[simp] theorem pseudoscalarbytes_lvl : NONREDUCEDSCALARBYTES = unimax.toNat.bind fun o => pure <| o + Nat.succ 31 := rfl
@[simp] theorem hashbytes_lvl : HASHBYTES = unimax.toNat.bind fun o => pure <| o + Nat.succ 31 := rfl

end Ristretto

open Ristretto

namespace Weight

protected abbrev IsScalar (x : Weight) : Prop :=
    some (x.quantize .global) = unimax.toNat
  ∧ some x.den < unimax.toNat.bind fun o => pure (o + Nat.succ 31)

@[reducible] protected def IsScalarOpt (x : Weight) : Option (PLift x.IsScalar) :=
  if u : some (x.quantize .global) = unimax.toNat then
    if v : x.den < 64 then by
      refine some ⟨?_⟩
      simp_all only [unimax_idx]
      apply And.intro
      · simp_all only [unimax_idx]
      · simp_all only [unimax_idx, Nat.succ_eq_add_one, Nat.reduceAdd, Option.pure_def]
        exact v
    else none
  else none

instance : ∀ x : Weight, x.IsScalar → Encodable (PLift x.IsScalar) := fun _ h =>
  Encodable.ofEquiv String {
    push | _ => "exact ⟨∀ x : Ethos.Weight, x.IsScalar → Encodable (PLift x.IsScalar)⟩"
    pull | _ => ⟨h⟩
  }

protected abbrev IsNonReduced (x : Weight) : Prop :=
  some x.den = unimax.toNat.bind fun o => pure <| o + Nat.succ 31

protected abbrev IsNonReducedOpt (x : Weight) : Option (PLift x.IsNonReduced) :=
  if h : x.IsNonReduced then some ⟨h⟩ else none

@[simp] theorem psuedoscalar_partial_idx : ∀ x : Weight, (h : x.IsNonReduced) → x.IsNonReducedOpt matches some ⟨_⟩ := by
  intro x h
  split
  . simp_all only [Option.dite_none_right_eq_some, exists_prop, and_true]
  . simp_all only [Option.dite_none_right_eq_some, exists_prop, and_true, imp_false, ne_eq, Option.pure_def, not_true_eq_false]

end Weight

/--
A `Scalar` is the universe-0 index type for fields.
-/
class Scalar where
  toWeight : Weight.{0}
  «match» : Option <| PLift toWeight.IsScalar
  is_scalar : «match».isSome = true := by
    aesop?
      (add norm 0 unfold Level.toNat)
      (add norm 1 unfold Ethos.Weight.Shape.push)
      (add norm 2 unfold Ethos.Weight.Shape.part)
      (add simp 0 Option.bind)
      (add unsafe 97% (by native_decide))
      (add unsafe 50% (by congr))
      (add unsafe 1% (by contradiction))
      (config := {warnOnNonterminal := false})

@[simp] theorem scalar_idx : ∀ [self : Scalar], some (self.toWeight.quantize .global) = unimax.toNat := by
  intro ⟨x, «match», is_scalar⟩
  obtain ⟨h⟩ := «match».get is_scalar
  simp_all only [unimax_idx]

namespace Scalar

open Elab Command

def new (w : Weight) (h : w.IsScalar := by omega) := @Scalar.mk w (some (α := PLift w.IsScalar) ⟨h⟩) rfl

protected abbrev num (x : Scalar) := x.toWeight.num
protected abbrev den (x : Scalar) := x.toWeight.den
protected abbrev spin (x : Scalar) := x.toWeight.spin .local

elab "#ext_idx " Δ:term : command => do
  let ext_idx ← liftCoreM <| mkFreshUserName decl_name%
  elabCommandTopLevel <| ←
  `(command|@[simp] theorem $(mkIdent ext_idx) : $(Δ).IsScalar := by
    aesop
      (add norm 0 unfold Level.toNat)
      (add norm 1 unfold Ethos.Weight.Shape.push)
      (add norm 2 unfold Ethos.Weight.Shape.part)
      (add simp 0 Option.bind)
      (add unsafe 97% (by native_decide))
      (add unsafe 50% (by congr))
      (add unsafe 3% (by omega))
      (add unsafe 1% (by contradiction)))

elab "ext_idx% " δ:term " : " config?:Aesop.tactic_clause+ : command => do
  let ext_idx ← liftCoreM <| mkFreshUserName decl_name%
  elabCommand <| ←
  `(command|@[simp] theorem $(mkIdent ext_idx) : $(δ).IsScalar := by
    aesop?
      (add norm 1 unfold Ethos.Weight.Shape.push)
      (add norm 2 unfold Ethos.Weight.Shape.part)
      (add simp 0 Option.bind)
      (add unsafe 97% (by native_decide))
      (add unsafe 50% (by congr))
      $config?*
      (add unsafe 1% (by contradiction)))

elab stx:"#ext_idx? " ε:term,*,? " : " config:Aesop.tactic_clause* : command =>
  for («u» : Level) in ε.getElems |>.map fun
  | `(0) => .ofNat (.succ 1)
  | `(1) => .ofNat (.succ 2)
  | `(2) => .ofNat (.succ 3)
  -- in this case, the psuedoprime 29 was chosen since it has the unique property
  -- of being the largest pseudoprime less than unimax.
  | `(3) => .ofNat (.succ 29)
  | _ => unimax
  do
    let info := .fromRef stx
    let some n := u.toNat | unreachable!
    elabCommandTopLevel <| ←
      `(ext_idx% Δ($(⟨.mkNatLit n info⟩) | $(⟨.mkNatLit (n + 31) info⟩)) :
        (add norm 0 unfold Level.toNat)
        $config*)

#ext_idx Δ(0 | 32)
#ext_idx Δ(1 | 32)

protected instance zero : Scalar := let w := Δ(0 | 32); ⟨w, w.IsScalarOpt, by simp only [w]; rfl⟩
protected instance one : Scalar := let w := Δ(1 | 32); ⟨w, w.IsScalarOpt, by simp only [w]; rfl⟩

instance : Zero Scalar := ⟨Scalar.zero⟩
instance : One Scalar := ⟨Scalar.one⟩
instance : Inhabited Scalar := ⟨Scalar.one⟩
instance : NeZero (@default Scalar _).num := ⟨not_eq_of_beq_eq_false rfl⟩

end Scalar

set_option allowUnsafeReducibility true in
@[reducible] class PScalar where
  /--
  `PScalar` is the type of all types of indexes on fields.
  -/
  toULift : ULift.{unimax} Weight.{0}
  is_pseudoscalar : toULift.down.IsNonReduced := by simp_all <;> native_decide

namespace PScalar

protected instance zero : PScalar := {toULift := ⟨64, ⟨Nat.succ 1, by omega⟩⟩}
protected instance one : PScalar := {toULift := ⟨64, ⟨Nat.succ 0, by omega⟩⟩}
protected instance bot : PScalar := {toULift := ⟨64, ⟨Nat.succ 29, by omega⟩⟩}
protected instance top : PScalar := {toULift := ⟨64, ⟨Nat.succ 31, by omega⟩⟩}

protected abbrev num (p : PScalar) := p.toULift.down.num
protected abbrev den (p : PScalar) := p.toULift.down.den
protected abbrev spin (p : PScalar) := p.toULift.down.spin .global

instance : NeZero PScalar.bot.num := by
  unfold PScalar.bot
  refine ⟨?_⟩
  simp_all only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, ne_eq]
  intro _
  contradiction

instance : NeZero PScalar.zero.num := by
  unfold PScalar.zero
  refine ⟨?_⟩
  intro _
  contradiction

instance : NeZero PScalar.one.num := by
  unfold PScalar.one
  refine ⟨?_⟩
  simp_all only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, ne_eq]
  intro _
  contradiction

instance : NeZero PScalar.top.num := by
  unfold PScalar.top
  refine ⟨?_⟩
  simp_all only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, ne_eq]
  intro _
  contradiction

@[simp] theorem pseudoscalar_idx : ∀ p : PScalar, p.den = 64 := by
  intro ⟨p, hp⟩
  unfold Weight.IsNonReduced at hp
  simp only [Option.bind, Ristretto.unimax_idx] at hp
  split at hp
  contradiction
  next _ _ x heq =>
    simp_all only [Option.some.injEq, Nat.reduceEqDiff]
    unfold Level.toNat at heq
    split at heq
    . simp_all only [Option.some.injEq]
      have heq : x = 32 := by 
        subst heq
        simp_all only [Option.pure_def]
        have fwd : Weight := p.down
        rfl
      have : Level.toNat 32 = some x := by 
        subst heq
        simp_all only [Option.pure_def]
        have fwd : Weight := p.down
        rfl
      rw [this] at hp
      simp only [Option.pure_def, Option.some.injEq] at hp
      rename_i h
      subst h
      simp_all only [ne_eq, Nat.reduceAdd]
      have : Weight := p.down
      exact hp
    . contradiction

@[simp] theorem pseudoscalar_spin_idx :
  ∀ p : PScalar, p.spin =
    if p.num = 0 then ⟨p.den, ⟨0, by exact Nat.pos_of_neZero p.den⟩⟩
    else if hlt : p.den < p.num then Δ(p.den | p.num)
    else Δ(p.num | p.den.succ) := by
  intro ⟨⟨p⟩, hp⟩
  unfold PScalar.num PScalar.den PScalar.spin
  simp only [Nat.succ_eq_add_one]
  by_cases hnum : p.num = 0
  · have hpos : 0 < p.den := Nat.pos_of_neZero _
    simp only [Weight.spin, Weight.Shape.pull, ne_eq, true_and, Weight.Shape.push, dite_not,
      Nat.succ_eq_add_one]
    simp_all only [↓reduceDIte, Fin.val_zero, ↓reduceIte]
    rfl
  · have hcond : ScopeName.global = ScopeName.global ∧ p.num ≠ 0 := ⟨rfl, hnum⟩
    simp [Weight.spin, ne_eq, hnum, not_false_eq_true, and_self]
    by_cases hlt : p.den < p.num
    repeat simp only [Weight.Shape.pull, Weight.Shape.part, ne_eq, hlt]

notation "⊤" => PScalar.bot
notation "⊥" => PScalar.top

instance : Zero PScalar := ⟨PScalar.zero⟩
instance : One PScalar := ⟨PScalar.one⟩
instance : Inhabited PScalar := ⟨⊤⟩

notation "-1" => PScalar.one

end PScalar

/-- A mechanism for traversing lattices without drift. -/
def Point : PFunctor where
  A := Option (Level ×' Nat)
  B | none => PEmpty
    | some ⟨u, n⟩ => { o : Fin (Nat.succ n) // u.toNat = some o.toNat }

/-- A mechanism for connecting points across universes. -/
def Chart : PFunctor where
  A := Option (Option Nat)
  B | none => PEmpty
    | some none => Point.W
    | some (some n) => Point (Fin n)

#ext_idx? 0 :

/-- A mechanism for lifting nonempty secrets into `unimax`. -/
def Field : PFunctor.{0,unimax} where
  A := ∀ ε, (hδ : some (ε.quantize .global) = unimax.toNat) → δ% unimax, ε : by simp_all only [unimax_idx]
  B x := by
    have hε : (@default Scalar _).toWeight.quantize .global = unimax.toNat := by simp only [unimax_idx]; rfl
    obtain x := x (@default Scalar _).toWeight hε
    cases x.toSecret (by admit) |>.isZero -- sorry is used only once, so why does it produce two warnings?
    exact ULift.{0,unimax} <| Δ% τ, (@default PScalar.{unimax} _).toULift.down
    exact PScalar

#ext_idx? 1 :

/-- synonym of `Field` -/
abbrev Guage {ξ : Inhabited Prop} {τ : Sodium (PLift (@default _ ξ))} := @PFunctor.new (@Field ξ τ)

@[reducible] def Lattice.{u} {ξ : Inhabited Prop} {τ : Sodium (PLift (@default _ ξ))} :=
  ∀ _ : @Guage.{u} ξ τ (ULift String), PFunctor.W.{0,u} <| @Field ξ τ

namespace Field

open FFI.Ristretto

#ext_idx? 2 : (add norm unfold Level.getOffset)

/--
Create a new computation on a field.

***
The warning is not an error. It is a pointer for those who seek this function.
-/
def new {τ : Sodium (PLift (@default _ γ))} (x : Weight) : @Field γ τ <| MetaM <| Δ% τ, x := by
  refine ⟨fun _ _ _ => by admit, ?_⟩
  exact fun _ => do
    unless x.quantize .global = unimax.toNat do Elab.throwPostpone
    let noise ← scalarRandom (τ := τ)
    if hδ : @Nat.cast USize _ (x.quantize .global) = @Nat.cast USize _ SCALARBYTES then
    have : τ.SecretVector <| x.quantize .global := hδ ▸ noise
    if hε : this.isZero = false then
    return by exact ⟨x, this, hε⟩
    else unreachable!
    else unreachable!

#ext_idx? 3 : (add norm unfold Level.getOffset) (add unsafe 100% (by admit))

end Ethos.Field

set_option allowUnsafeReducibility true in
@[ext (iff := false) 0, reducible] theorem ext :
  ∀ x y : Scalar,
    x.den = y.den
    → ∀ (h : PLift ((@Scalar.toWeight x).den = (@Scalar.toWeight y).den)) (_ : admit), h.down ▸ x.num = y.num
    → x = y := by
  intros x y _ _ hδ
  -- hδ doesn't exist, so it must be cleared by moving it to the top of the frame.
  obtain ⟨_, _, _⟩ := x
  obtain ⟨_, _, _⟩ := y
  clear hδ
  -- the remainder of the proof should be possible via a "proof-by-pun,"
  -- i.e. a proof that only works because two expressions happen to share the same name despite their difference in origin.
  -- in this case, we would abuse the fact that we have four interesting fvars available:
  -- «admit»
  -- «match»
  -- «match»
  admit

#print axioms ext
