import Lean.Data.Lsp
import Sodium.Ethos.Weight
import Sodium.Server.Monad
import Sodium.Crypto.Stream

universe u

open Lean Sodium Crypto Meta

declare_aesop_rule_sets [«standard», «cautious»] (default := false)

namespace Aesop

export Ethos (Weight)

def Percent.ofWeight (p : Weight) : Percent := ⟨p⟩

instance _root_.Lean.Meta.TransparencyMode.encodable : Encodable TransparencyMode :=
  Encodable.ofEquiv (Fin 4) {
    push
      | .all => 0
      | .default => 1
      | .reducible => 2
      | .instances => 3
    pull
      | 0 => .all
      | 1 => .default
      | 2 => .reducible
      | 3 => .instances
  }

deriving instance DecidableEq for TransparencyMode

instance BuilderName.encodable : Encodable BuilderName :=
  Encodable.ofEquiv (Fin 8) {
    push
      | .apply => 0
      | .cases => 1
      | .constructors => 2
      | .destruct => 3
      | .forward => 4
      | .simp => 5
      | .tactic => 6
      | .unfold => 7
    pull
      | 0 => .apply
      | 1 => .cases
      | 2 => .constructors
      | 3 => .destruct
      | 4 => .forward
      | 5 => .simp
      | 6 => .tactic
      | 7 => .unfold
  }

deriving instance DecidableEq for BuilderName

instance PhaseName.encodable : Encodable PhaseName :=
  Encodable.ofEquiv (Fin 3) {
    push
      | .norm => 0
      | .safe => 1
      | .unsafe => 2
    pull
      | 0 => .norm
      | 1 => .safe
      | 2 => .unsafe
  }

deriving instance DecidableEq for PhaseName

inductive PhaseAngle where
  | up
  | down
  | left
  | right
  | top
  | bot
  deriving Inhabited, DecidableEq, BEq, Hashable

instance PhaseAngle.encodable : Encodable PhaseAngle :=
  Encodable.ofEquiv (Fin 6) {
    push
      | .up => 0
      | .down => 1
      | .left => 2
      | .right => 3
      | .top => 4
      | .bot => 5
    pull
      | 0 => .up
      | 1 => .down
      | 2 => .left
      | 3 => .right
      | 4 => .top
      | 5 => .bot
  }

instance ScopeName.encodable : Encodable ScopeName :=
  Encodable.ofEquiv (Fin 2) {
    push
      | .local => 0
      | .global => 1
    pull
      | 0 => .local
      | 1 => .global
  }

instance CtorNames.encodable : Encodable CtorNames :=
  Encodable.ofEquiv (Name × Array Name × Bool) {
    push | ⟨n, ns, h⟩ => ⟨n, ns, h⟩
    pull | ⟨n, ns, h⟩ => ⟨n, ns, h⟩
  }

instance RuleName.encodable : Encodable RuleName :=
  Encodable.ofEquiv (Name × BuilderName × PhaseName × ScopeName × UInt64) {
    push | ⟨n, bn, pn, sn, h⟩ => ⟨n, bn, pn, sn, h⟩
    pull | ⟨n, bn, pn, sn, h⟩ => ⟨n, bn, pn, sn, h⟩
  }

instance RuleTerm.encodable : Encodable RuleTerm :=
  Encodable.ofEquiv (Name ⊕ Term) {
    push
      | .const n => .inl n
      | .term t => .inr t
    pull
      | .inl n => .const n
      | .inr t => .term t
  }

end Aesop

namespace Ethos

export Aesop (
  PhaseName
  PhaseSpec
  PhaseAngle
  Percent
  Percent.ofWeight
  LocalRuleSet
  LocalRuleSetMember
  RuleName
  RuleTerm
  CtorNames
  BuilderName
)

/--
A proof-carrying object.
-/
structure Observable extends Weight where
  private mk ::
  phase : PhaseName := default
  carrier : Verified Syntax.Tactic

namespace Observable

protected def new {σ : Type u} {τ : Sodium σ} (stx : Syntax.Tactic) (scope : ScopeName := .local) : CryptoM τ Observable := by
  refine bind getRemainingHeartbeats fun before => ?_
  refine bind (sign stx) fun cert => ?_
  refine bind getRemainingHeartbeats fun after => ?_

  if h : after < before then
    exact pure ⟨Δ(after | before), if scope = .local then .safe else .unsafe, cert⟩
  else
    exact pure ⟨Δ(before | after.succ), default, cert⟩

protected def renew {σ : Type u} {τ : Sodium σ} (o : Observable) (scope : ScopeName := .global) : CryptoM τ Observable := by
  refine bind getRemainingHeartbeats fun before => ?_
  refine bind (sign o.carrier.val) fun cert => ?_
  refine bind getRemainingHeartbeats fun after => ?_

  if h : after < before then
    exact pure ⟨Δ(after | before), if scope = .local then .safe else .unsafe, cert⟩
  else
    exact pure ⟨Δ(before | after.succ), default, cert⟩

@[coe]
def toWeight (o : Observable) : Weight := o.toPSigma

instance : Coe Observable Weight := ⟨toWeight⟩

def pretty (o : Observable) : Format := o.carrier.val.raw.prettyPrint
def size (o : Observable) : Nat := (toString o.pretty).length

def phaseSpec (o : Observable) : PhaseSpec :=
  match o.phase with
  | .unsafe => .unsafe {successProbability := Percent.ofWeight o}
  | .safe => .safe {penalty := o.toWeight.quantize .local, safety := .safe}
  | .norm => .norm {penalty := o.toWeight.quantize .global}

def toRule (o : Observable) (name : Name) (scope : ScopeName) : LocalRuleSetMember :=
  .global <| .base <| o.phaseSpec.toRule name .tactic scope (.tacticStx o.carrier) .unindexed none

def toRuleSet (os : Array Observable) (name : Name) (scope : ScopeName) : LocalRuleSet :=
  os.mapIdx (·, ·) |>.foldl (init := ∅) fun set ⟨i, o⟩ => set.add <| o.toRule (.num name i) scope

abbrev den (o : Observable) := o.toWeight.den
abbrev num (o : Observable) := o.toWeight.num

@[simp]
theorem den_nezero (o : Observable) : o.den ≠ 0 := by
  simp only [ne_eq, Weight.den_nezero, not_false_eq_true]

@[simp]
theorem num_lt_den (o : Observable) : o.num < o.den := by exact Weight.num_lt_den _

instance : ∀ o : Observable, NeZero o.den := fun o => ⟨den_nezero o⟩

protected instance format : ToFormat Observable := ⟨pretty⟩

protected instance repr : Repr Observable where
  reprPrec o n :=
    have : o.num < o.den := by simp
    f!"{reprPrec Δ(o.num | o.den) n}"

abbrev Positive (o : Observable) := o.num ≠ 0

def Shape := Weight × PhaseName × Verified Syntax.Tactic

def Shape.push : Observable → Shape
  | ⟨p, x, s⟩ => ⟨p, x, s⟩

def Shape.pull : Shape → Observable
  | ⟨p, x, s⟩ => ⟨p, x, s⟩

def Shape.part (o : Observable) (scope : ScopeName) : Shape :=
  ⟨o.toWeight.spin scope, o.phase, o.carrier⟩

instance Shape.encodable : Encodable Shape := by unfold Shape; infer_instance

protected instance encodable : Encodable Observable :=
  Encodable.ofEquiv _ { push := Shape.push, pull := Shape.pull }

def rotate : PhaseAngle → Observable → Observable
  | .bot, o@{phase := .norm, ..} => {o with phase := .norm}
  | .bot, o@{phase := .unsafe, ..} => {o with phase := .unsafe}
  | .bot, o@{phase := .safe, ..} => {o with phase := .safe}
  | .up, o@{phase := .norm, ..} => {o with phase := .safe}
  | .up, o@{phase := .unsafe, ..} => {o with phase := .norm}
  | .up, o@{phase := .safe, ..} => {o with phase := .unsafe}
  | .down, o@{phase := .norm, ..} => {o with phase := .unsafe}
  | .down, o@{phase := .unsafe, ..} => {o with phase := .safe}
  | .down, o@{phase := .safe, ..} => {o with phase := .norm}
  | .left, o@{phase := .norm, ..} => {o with phase := .unsafe}
  | .left, o@{phase := .unsafe, ..} => {o with phase := .safe}
  | .left, o@{phase := .safe, ..} => {o with phase := .norm}
  | .right, o@{phase := .norm, ..} => {o with phase := .safe}
  | .right, o@{phase := .unsafe, ..} => {o with phase := .norm}
  | .right, o@{phase := .safe, ..} => {o with phase := .unsafe}
  | .top, o@{phase := .norm, ..} => {o with phase := .norm}
  | .top, o@{phase := .unsafe, ..} => {o with phase := .safe}
  | .top, o@{phase := .safe, ..} => {o with phase := .unsafe}

@[simp]
theorem rotate_bot : ∀ p : PhaseAngle, ∀ o : Observable, p = .bot → (o.rotate p).phase = o.phase := by
  intro p o _
  unfold rotate
  induction p <;> try contradiction
  cases h : o.phase <;> split <;> simp <;> contradiction

def emit (io : IO.FS.Stream) (o : Observable) (method : String := "$/tactic") : MetaM PUnit :=
  io.writeLspNotification {method, param := encode o}

end Observable

abbrev Suggestion := String × Float

def Observable.toSuggestion (o : Observable) : Suggestion :=
  (toString o.carrier.val.raw.prettyPrint, o.toWeight)

/--
A `Universal` is a mechanism for associating semantics to instances of `Observable`.
-/
def Universal : PFunctor where
  A := Prop
  B := fun h => (_ : h) → Observable

namespace Universal

/--
The default proposition that JSON encodings of `Observable` round-trip correctly.
-/
protected instance prompt : Inhabited Universal.A where
  default :=
      ∀ x : Weight, decode? (encode x) = some x
    ∧ ∀ y : PhaseName, decode? (encode y) = some y
    ∧ ∀ z : Verified Syntax.Tactic, decode? (encode z) = some z
    ∧ ∀ o : Observable, decode? (encode o) = some o

instance {α} [Inhabited α] : Inhabited (Universal α) where
  default := ⟨default, fun _ => default⟩

@[simp] theorem specific_idx : Universal.A.{0} = Prop := rfl

@[simp] theorem specific_default_idx : Universal.B default = (@default Universal.A.{0} Universal.prompt → Observable) := by
  unfold Universal
  simp only

theorem universal_idx : Universal.A = Prop := rfl

theorem universal_default_idx : Universal.B default = (@default Universal.A Universal.prompt → Observable) := by
  unfold Universal
  simp only [Encodable.encodek, implies_true, and_self]

/--
The level-matrix representing all inhabitation clauses of the `Universal` functor.
-/
@[reducible]
protected def Prompt (u : Level := levelZero) (v : Level := levelOne) : Expr :=
  mkApp (mkConst ``Inhabited) (mkApp (mkConst ``PFunctor.A [u, v]) (mkConst ``Universal [u]))

/--
`Forward` represents the fixpoint of `Universal.prompt`. It can be thought of as a postponed
inhabitation clause for `Verified Syntax.Tactic`.

Usually, this proposition emerges spontaneously when using `aesop`, thus making it a convenient
argument for declaring `forward` rules.
-/
@[reducible]
protected def Forward : Prop :=
  ∀ (_ : Verified Syntax.Tactic) (o : Observable.{u}), (Observable.Shape.push o).pull = o

/--
`Destruct` is the terminal type of `Universal.prompt`.

The choice of proposition is motivated by the form of `Universal.Forward`, making it easy to
terminate proof search through the use of an `apply` rule.
-/
@[reducible]
protected def Destruct := PLift (∀ (o : Observable.{u}), (Observable.Shape.push o).pull = o)

namespace Destruct

def Shape.push (_ : Universal.Destruct) : String :=
  "exact ⟨∀ (o : Sodium.Ethos.Observable.{0}), (Sodium.Ethos.Observable.Shape.push o).pull = o⟩"

def Shape.pull : String → Option Universal.Destruct
| "exact ⟨∀ (o : Sodium.Ethos.Observable.{0}), (Sodium.Ethos.Observable.Shape.push o).pull = o⟩" => some ⟨by intro; rfl⟩
| _ => none

instance encodable : Encodable Universal.Destruct.{0} :=
  Encodable.ofLeftInj Shape.push Shape.pull (by intro; rfl)

end Destruct

@[reducible]
protected def map {α β} := @PFunctor.map α β Universal

end Universal

def mkFreshDelta (u : Level := levelZero) (v : Level := levelZero) : MetaM Expr :=
  Meta.mkFreshExprMVar (Universal.Prompt u v)

protected def Observable.observe {α} (o : Observable) (u : Universal α) := u.2 fun _ => o

variable {σ : Type u} {τ : Sodium σ}

protected def Observable.pointer (scope : ScopeName) : CryptoM τ Observable := do
  Observable.new (← `(tactic|rfl)) scope

open PrettyPrinter in
protected def Observable.quantize (o : Observable) (p : PhaseAngle := .top) : CryptoM τ Observable :=
  Meta.withNewMCtxDepth do
    let json := encode (← o.renew)
    let term ← delab <| mkStrLit json.compress
    Observable.rotate p <$> Observable.new (← `(tactic|exact ⟨$term⟩))

protected def Universal.bind (u : Universal (CryptoM τ Observable)) (f : Observable → CryptoM τ Observable) : Universal (CryptoM τ Observable) := by
  refine Universal.map (bind · fun o => ?_) u
  exact do (← f o).observe u

open PrettyPrinter in
protected def Universal.print {α : Type} [Encodable α] (ma : Universal (MetaM α)) : Universal (CryptoM τ Observable) := by
  refine Universal.map (fun m => ?_) ma
  refine bind m fun a => ?_
  have e : Expr := mkStrLit (encode a).compress
  refine bind (delab e) fun x => ?_
  exact bind `(tactic|exact ⟨$x⟩) Observable.new

instance : Functor Universal where
  map := Universal.map

/--
A `Witness` is a universe-polymorphic computation over proof-carrying objects.

See `Sodium.Typo.Emulator` for example usage.
-/
@[reducible]
def Witness.{«x», «y»} {σ : Type «x»} (τ : Sodium σ) := Universal.{«y»} (CryptoM τ Observable)

namespace Witness

variable {τ : Sodium σ}

def mk (o : Observable) : Witness τ := ⟨default, fun _ => pure o⟩

def emit (io : IO.FS.Stream) (o : Observable) (method : String := "$/witness") (α : Witness τ) : CryptoM τ PUnit := do
  (← o.observe α).emit io method

end Witness

end Ethos
