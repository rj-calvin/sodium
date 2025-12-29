import Sodium.Data.Encodable.WType
import Sodium.Data.PFunctor
import Sodium.Ethos.Weight
import Sodium.FFI.Ristretto
import Sodium.FFI.GenericHash

open Lean Elab Term Sodium Aesop Ethos

variable ⦃γ : Inhabited Prop⦄ {τ : Sodium (PLift (@default Prop γ))}

/-- A point on Curve25519 relative to `x : Weight`. -/
structure Prob (x : Weight) extends Weight where
  fpt : SecretVector τ (@Weight.quantize toPSigma .global)
  fpt_shape : x.quantize .global = @Weight.quantize toPSigma .global

namespace Prob
set_option quotPrecheck false

notation "Δ% " τ ", " x => @Prob _ τ x

notation "δ% " u " : " o =>
  ∀ (hδ : ∃ y, @Ethos.Weight.quantize y Aesop.ScopeName.local = (u).toNat := o), Δ% $(mkIdent `τ), hδ.choose

def toWeight (_ : Δ% τ, x) : Weight := x
def toSecret (γ : Δ% τ, x) : SecretVector τ <| x.quantize .global := γ.fpt_shape ▸ γ.fpt

abbrev num (p : Δ% τ, x) := (toWeight p).num
abbrev den (p : Δ% τ, x) := (toWeight p).den

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
@[simp] theorem unimax_match_idx : unimax.toNat.isSome = true := by unfold Level.toNat; rfl

@[simp] theorem unimax_nat_idx : ∀ x, some x = unimax.toNat → x = 32 := by
  intro x a
  cases a
  rfl

theorem bytes_lvl : BYTES = SCALARBYTES := rfl
theorem scalarbytes_lvl : SCALARBYTES = unimax.toNat := rfl
theorem pseudoscalarbytes_lvl : NONREDUCEDSCALARBYTES = unimax.toNat.bind fun o => pure <| o + Nat.succ 31 := rfl
theorem hashbytes_lvl : HASHBYTES = unimax.toNat.bind fun o => pure <| o + Nat.succ 31 := rfl

abbrev Reduced := ByteVector BYTES

def Reduced.toNat : Reduced → Nat
| x =>
  let (_, out) := x.toList.foldl (init := (1, 0))
    fun | (pow, acc), b => (pow * 256, acc + b.toNat * pow)
  out

instance : DecidableEq {x : Reduced // isValidPoint x} := by infer_instance
instance : DecidableEq (Option Reduced) := by infer_instance

instance : Repr (Option {x : Reduced // isValidPoint x}) where
  reprPrec x _ :=
    match x with
    | some ⟨x, _⟩ => repr (some x.toNat)
    | _ => repr (none (α := PUnit))

abbrev NonReduced := ByteVector NONREDUCEDSCALARBYTES

open FFI.GenericHash in
def NonReduced.ofEncodable {α} [Encodable α] (a : α) (name? : Option Name := none) : NonReduced :=
  let bytes := (encode a).compress.toUTF8
  let salt :=
    match name? with
    | some x => hashCustom SALTBYTES (by unfold SALTBYTES BYTES_MIN BYTES_MAX; omega) (toString x).toUTF8 default default
    | _ => default
  hashCustom NONREDUCEDSCALARBYTES (by unfold NONREDUCEDSCALARBYTES BYTES_MIN BYTES_MAX; omega) bytes salt default

def NonReduced.ofNat (n : Nat) : NonReduced :=
  let (_, out) := (List.range NONREDUCEDSCALARBYTES).foldl (init := (n, default))
    fun | (m, bs), i => (m / 256, bs.set! i <| UInt8.ofNat (m % 256))
  out

instance {n} : OfNat NonReduced n where
  ofNat := NonReduced.ofNat n

instance {n} : OfNat (Option Reduced) n where
  ofNat := pointHash (NonReduced.ofNat n)

instance : Coe NonReduced (Option Reduced) := ⟨pointHash⟩
instance : Add (Option Reduced) where add | some a, some b => pointAdd a b | _, _ => none
instance : Sub (Option Reduced) where sub | some a, some b => pointSub a b | _, _ => none

@[simp] theorem reduced_add_idx : ∀ a b : Reduced, some a + some b = pointAdd a b := by intros; rfl
@[simp] theorem reduced_sub_idx : ∀ a b : Reduced, some a - some b = pointSub a b := by intros; rfl

end Ristretto

open Ristretto

abbrev Ristretto := Option {x : Reduced // FFI.Ristretto.isValidPoint x}

namespace Weight

abbrev IsScalar (x : Weight) : Prop :=
  some (x.quantize .global) = unimax.toNat ∧ some x.den < unimax.toNat.bind fun o => pure <| o + Nat.succ 31

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

/-- A `Scalar` is the index type for fields. -/
class Scalar where
  toWeight : Weight.{0}
  «match» : Option <| PLift toWeight.IsScalar := toWeight.IsScalarOpt
  is_scalar : «match».isSome = true := by unfold Weight.IsScalarOpt; try simp_all; first | assumption | native_decide

namespace Scalar

@[simp] theorem scalar_idx : ∀ [self : Scalar], some (self.toWeight.quantize .global) = unimax.toNat := by
  intro ⟨x, «match», is_scalar⟩
  obtain ⟨h⟩ := «match».get is_scalar
  simp_all only [unimax_idx]

open FFI.Ristretto in
@[simp] theorem scalar_nat_idx : ∀ [self : Scalar], self.toWeight.quantize .global = SCALARBYTES := by
  intro
  simp only [scalar_idx, unimax_idx, unimax_nat_idx, unimax_pseudo_idx]
  rfl

instance scalar_ext : ∀ x y : Weight, (h : x = y) → (hx : PLift x.IsScalar) → (hy : PLift y.IsScalar) → HEq hx hy :=
  fun _ _ _ hx hy => by
    obtain ⟨hx⟩ := hx
    obtain ⟨hy⟩ := hy
    congr
    exact proof_irrel_heq hx hy

def new (w : Weight) (h : w.IsScalar) :=
  @Scalar.mk w (some (α := PLift w.IsScalar) ⟨h⟩) rfl

protected abbrev num (x : Scalar) := x.toWeight.num
protected abbrev den (x : Scalar) := x.toWeight.den
protected abbrev spin (x : Scalar) := x.toWeight.spin .local

protected instance zero : Scalar := let w := Δ(0 | 32); ⟨w, w.IsScalarOpt, by simp only [w]; rfl⟩
protected instance one : Scalar := let w := Δ(1 | 32); ⟨w, w.IsScalarOpt, by simp only [w]; rfl⟩

instance : Zero Scalar := ⟨Scalar.zero⟩
instance : One Scalar := ⟨Scalar.one⟩
instance : Inhabited Scalar := ⟨Scalar.one⟩
instance : NeZero (@default Scalar _).num := ⟨not_eq_of_beq_eq_false rfl⟩

@[simp] theorem scalar_weight_ext : ∀ x y : Scalar, (h : x = y) → x.toWeight = y.toWeight := by
  intro x y h
  obtain ⟨x, mx, hx⟩ := x
  obtain ⟨y, my, hy⟩ := y
  simp_all only
  cases h
  rfl

@[simp] theorem one_ne_zero : (1 : Scalar) ≠ (0 : Scalar) := by
  refine Ne.intro ?_
  intro h
  cases Scalar.scalar_weight_ext 1 0 h

end Scalar

/-- `PScalar` is the universe-polymorphic index type for fields. -/
class PScalar where
  toULift : ULift Weight.{0}
  is_pseudoscalar : toULift.down.IsNonReduced := by try simp_all; first | assumption | native_decide

namespace PScalar

protected instance bot : PScalar := {toULift := ⟨64, ⟨0, by omega⟩⟩}
protected instance one : PScalar := {toULift := ⟨64, ⟨Nat.succ 0, by omega⟩⟩}
protected instance two : PScalar := {toULift := ⟨64, ⟨Nat.succ 1, by omega⟩⟩}
protected instance top : PScalar := {toULift := ⟨64, ⟨Nat.succ 31, by omega⟩⟩}

protected abbrev num (p : PScalar) := p.toULift.down.num
protected abbrev den (p : PScalar) := p.toULift.down.den
protected abbrev spin (p : PScalar) := p.toULift.down.spin .global

instance : NeZero PScalar.one.num := by
  unfold PScalar.one
  refine ⟨?_⟩
  intro _
  contradiction

instance : NeZero PScalar.two.num := by
  unfold PScalar.two
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
    simp only [Weight.spin, Weight.Shape.pull, ne_eq, true_and, Weight.Shape.push, dite_not, Nat.succ_eq_add_one]
    simp_all only [↓reduceDIte, Fin.val_zero, ↓reduceIte]
    rfl
  · simp only [Weight.spin, ne_eq, hnum, not_false_eq_true, and_self, ↓reduceDIte, Weight.Shape.part_pull_succ, ↓reduceIte]
    by_cases hlt : p.den < p.num
    . simp only [Weight.Shape.pull, Weight.Shape.part, ne_eq, hlt]
      omega
    . simp_all only [not_false_eq_true, ne_eq, true_and, Nat.not_lt, Fin.is_le']
      split
      . omega
      . rfl

notation "⊤" => PScalar.top
notation "⊥" => PScalar.bot
notation "-1" => PScalar.two

instance : One PScalar := ⟨PScalar.one⟩
instance : Inhabited PScalar := ⟨⊤⟩

end PScalar

/-- A universe-polymorphic string. -/
abbrev PString := ULift Syntax

namespace PString

def pseudostring_transport_idx : ∀ _ : PString, Syntax := by intro p; exact p.down

protected def mk (s : String) (info : SourceInfo := default) : PString := Id.run do
  let mut stx : Array Syntax := #[]
  for c in s.toList do stx := stx.push <| ulift c
  return ⟨.node info ``Lean.Parser.Tactic.tacticSeq stx⟩
where ulift (c : Char) : Syntax.Tactic :=
  ⟨Syntax.node .none ``Lean.Parser.Tactic.exact #[
    Syntax.atom .none "exact",
    Syntax.node .none ``Lean.Parser.Term.anonymousCtor #[
      Syntax.atom .none "⟨",
      Syntax.node .none `term #[Syntax.mkCharLit c],
      Syntax.atom .none "⟩"
    ]
  ]⟩

protected def «elab» (p : PString) : TermElabM String := do
  let mut s := ""
  for c in p.down.getArgs do
    let type := mkApp (mkConst ``ULift [levelZero, levelZero]) (mkConst ``Char)
    let δ ← Meta.mkFreshExprMVar type
    runTacticMAsTermElabM δ.mvarId! do Tactic.evalTactic c
    let δ ← instantiateMVars δ
    let x ← unsafe Meta.evalExpr (ULift Char) type δ
    s := s ++ ⟨[x.down]⟩
  return s

end PString

/-- A mechanism for lifting nonempty secrets from universe `u` into universe `v`. -/
def Field : PFunctor.{u, v} where
  A := ∀ ε : ULift.{u, 0} Weight, (hε : some (ε.down.quantize .global) = unimax.toNat) → δ% unimax :
    ε.down.quantize_relativity.imp fun _ hδ => by rwa [hδ] at hε
  B x := by
    obtain x : Prob.{u} _ := x ⟨(@default Scalar _).toWeight⟩ rfl
    cases x.toSecret.isZero
    . exact ULift.{v} <| Δ% τ, x.toWeight
    . exact PString.{v}

namespace Field

open Command

set_option linter.unreachableTactic false

elab "#ext_idx? " idx:ident δ:term " : " config:Aesop.tactic_clause+ : command => do
  elabCommand <| ← `(command|theorem $idx : $δ := by
    aesop?
      (add norm 0 unfold Level.toNat)
      (add unsafe 0% (pattern := False) (by contradiction))
      $config*)

/--
info: Try this:
  apply And.intro
  · unfold Lean.Level.toNat
    simp_all only [unimax_pseudo_idx, unimax_idx]
    rfl
  · unfold Lean.Level.toNat
    simp_all only [unimax_pseudo_idx, unimax_idx, Nat.succ_eq_add_one, Nat.reduceAdd, unimax_nat_idx, Option.pure_def]
    split
    next x heq =>
      simp_all only [unimax_pseudo_idx, unimax_idx, Option.bind_some, Option.some_lt_some]
      (native_decide)
    next x
      x_1 =>
      simp_all only [imp_false, unimax_pseudo_idx, unimax_idx, Option.bind_none, Option.not_lt_none]
      (contradiction)
-/
#guard_msgs in
#ext_idx? ext_idx_bot Δ(0 | 32).IsScalar : (add unsafe (by native_decide))

/--
info: Try this:
  apply And.intro
  · unfold Lean.Level.toNat
    simp_all only [unimax_pseudo_idx, unimax_idx, Fin.isValue, ne_eq, Weight.mk_num_pos, not_false_eq_true,
      Weight.quantize_global_partial_eq, Nat.succ_eq_add_one]
    rfl
  · unfold Lean.Level.toNat
    simp_all only [unimax_pseudo_idx, unimax_idx, Nat.succ_eq_add_one, Nat.reduceAdd, unimax_nat_idx, Option.pure_def]
    split
    next x heq =>
      simp_all only [unimax_pseudo_idx, unimax_idx, Option.bind_some, Option.some_lt_some]
      (native_decide)
    next x
      x_1 =>
      simp_all only [imp_false, unimax_pseudo_idx, unimax_idx, Option.bind_none, Option.not_lt_none]
      (contradiction)
-/
#guard_msgs in
#ext_idx? ext_idx_top Δ(1 | 32).IsScalar : (add unsafe (by native_decide))

/--
info: Try this:
  apply And.intro
  · unfold Lean.Level.toNat
    simp_all only [Fin.isValue, ne_eq, Weight.mk_num_pos, not_false_eq_true, Weight.quantize_global_partial_eq,
      Nat.succ_eq_add_one, unimax_idx]
    rfl
  · unfold Lean.Level.toNat
    simp_all only [unimax_idx, Nat.succ_eq_add_one, Nat.reduceAdd, unimax_pseudo_idx, unimax_nat_idx, Option.pure_def]
    split
    next x heq =>
      simp_all only [unimax_pseudo_idx, unimax_idx, Option.bind_some, Option.some_lt_some]
      (admit)
    next x
      x_1 =>
      simp_all only [imp_false, unimax_pseudo_idx, unimax_idx, Option.bind_none, Option.not_lt_none]
      (contradiction)
-/
#guard_msgs(info, drop warning) in
#ext_idx? ext_idx_one Δ(2 | 33).IsScalar : (add unsafe (by contradiction)) (add unsafe (by admit))

/--
info: Try this:
  apply And.intro
  · unfold Lean.Level.toNat
    simp_all only [Fin.isValue, ne_eq, Weight.mk_num_pos, not_false_eq_true, Weight.quantize_global_partial_eq,
      Nat.succ_eq_add_one, unimax_idx]
    rfl
  · unfold Lean.Level.toNat
    simp_all only [unimax_idx, Nat.succ_eq_add_one, Nat.reduceAdd, unimax_pseudo_idx, unimax_nat_idx, Option.pure_def]
    split
    next x heq =>
      simp_all only [unimax_pseudo_idx, unimax_idx, Option.bind_some, Option.some_lt_some]
      (admit)
    next x
      x_1 =>
      simp_all only [imp_false, unimax_pseudo_idx, unimax_idx, Option.bind_none, Option.not_lt_none]
      (admit)
-/
#guard_msgs(info, drop warning) in
#ext_idx? ext_idx_two Δ(3 | 34).IsScalar : (add unsafe (by admit))

theorem ext_idx_three : Δ(32 | 63).IsScalar := by
  apply And.intro
  · unfold Lean.Level.toNat
    simp_all only [unimax_pseudo_idx, unimax_idx, Fin.isValue, ne_eq, Weight.mk_num_pos, not_false_eq_true,
      Weight.quantize_global_partial_eq, Nat.succ_eq_add_one]
    rfl
  · unfold Lean.Level.toNat
    simp_all only [unimax_pseudo_idx, unimax_idx, Nat.succ_eq_add_one, Nat.reduceAdd, unimax_nat_idx, Option.pure_def]
    split
    next x heq =>
      simp_all only [unimax_pseudo_idx, unimax_idx, Option.bind_some, Option.some_lt_some]
      (native_decide)
    next x x_1 =>
      simp_all only [imp_false, unimax_pseudo_idx, unimax_idx, Option.bind_none, Option.not_lt_none]
      (contradiction)

end Field

/-- synonym of `Field` -/
abbrev Guage {ξ : Inhabited Prop} {τ : Sodium (PLift (@default _ ξ))} := @PFunctor.new (@Field.{31, 0} _ τ)

/-- A fabric of fields relative to a choice of `Guage`. -/
@[reducible] def Lattice {ξ : Inhabited Prop} {τ : Sodium (PLift (@default _ ξ))} :=
  let Field : PFunctor.{0} := @Field _ τ; ∀ _ : @Guage _ τ PString, Field.W

class HLattice {ξ : Inhabited Prop} {τ : Sodium (PLift (@default _ ξ))} (_ : @Guage _ τ PString) where
  field : PFunctor.W <| @Field _ τ

namespace Lattice

variable {ξ : Inhabited Prop} {τ : Sodium (PLift (@default _ ξ))}

abbrev next (ι : Lattice) (γ : Guage (τ := τ) PString) := PFunctor.W.next (ι γ)
abbrev children (ι : Lattice) (γ : Guage (τ := τ) PString) := PFunctor.W.children (ι γ)

abbrev cases {X : (@Field _ _).W → Sort u}
    (ι : Lattice.{0, max u 31})
    (γ : Guage (τ := τ) PString)
    (f : (x : Field (@Field _ _).W) → X (PFunctor.W.mk x)) :=
  PFunctor.W.cases f (ι γ)

end Lattice

end Ethos

@[ext (iff := false)] theorem ext :
  ∀ x y : Scalar,
    x.den = y.den
    → ∀ (h : PLift ((@Scalar.toWeight x).den = (@Scalar.toWeight y).den)) (_ : admit), h.down ▸ x.num = y.num
    → x = y := by
  intros x y _ h hδ h'
  obtain h := h.down
  obtain ⟨x, mx, hx⟩ := x
  obtain ⟨y, my, hy⟩ := y
  clear hδ
  congr
  . ext; simp_all only; exact congrArg Fin.val h'
  . have : x = y := by ext; exact h; exact congrArg Fin.val h'
    match mx, my with
    | some _, some _ =>
      congr
      exact Scalar.scalar_ext x y this _ _
  . simp_all only [heq_eq_eq]

/-- info: 'ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ext

/-- info: 'Ethos.Field.ext_idx_bot' depends on axioms: [propext, Lean.ofReduceBool, Quot.sound] -/
#guard_msgs in
#print axioms Field.ext_idx_bot

/-- info: 'Ethos.Field.ext_idx_top' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound] -/
#guard_msgs in
#print axioms Field.ext_idx_top

/-- info: 'Ethos.Field.ext_idx_one' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Field.ext_idx_one

/-- info: 'Ethos.Field.ext_idx_two' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Field.ext_idx_two
