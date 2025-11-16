import Aesop
import Sodium.Ethos.Probability
import Sodium.Server.Monad
import Sodium.Crypto.Stream

/-
Ethos is a mechanism for translating semantics between universes.
-/

universe u

open Lean Sodium Crypto Meta

namespace Aesop

export Ethos (Probability)

def Percent.ofProbability (p : Probability) : Percent := ⟨p⟩

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

export Aesop (PhaseName PhaseAngle Percent Percent.ofProbability)

/--
A proof-carrying object.
-/
structure Observable extends Probability where
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

@[simp]
def toProbability (o : Observable) : Probability := o.toPSigma

def toPercent (o : Observable) : Percent := Percent.ofProbability o.toProbability

def pretty (o : Observable) : Format := o.carrier.val.raw.prettyPrint
def size (o : Observable) : Nat := (toString o.pretty).length

abbrev den (o : Observable) := o.toProbability.den
abbrev num (o : Observable) := o.toProbability.num

@[simp]
theorem den_nezero (o : Observable) : o.den ≠ 0 := by
  simp only [ne_eq, Probability.den_nezero, not_false_eq_true]

@[simp]
theorem num_lt_den (o : Observable) : o.num < o.den := by exact Probability.num_lt_den _

instance : ∀ o : Observable, NeZero o.den := fun o => ⟨den_nezero o⟩

protected instance format : ToFormat Observable := ⟨pretty⟩

protected instance repr : Repr Observable where
  reprPrec o n :=
    have : o.num < o.den := by simp
    f!"{reprPrec.{0} Δ(o.num | o.den) n}"

abbrev Positive (o : Observable) := o.num ≠ 0

def Shape := Probability × PhaseName × Verified Syntax.Tactic

def Shape.push : Observable → Shape
  | ⟨p, x, s⟩ => ⟨p, x, s⟩

def Shape.pull : Shape → Observable
  | ⟨p, x, s⟩ => ⟨p, x, s⟩

def Shape.part (o : Observable) (scope : ScopeName) : Shape :=
  ⟨o.toProbability.spin scope, o.phase, o.carrier⟩

instance Shape.encodable : Encodable Shape := by unfold Shape; infer_instance

protected instance encodable : Encodable Observable :=
  Encodable.ofEquiv _ { push := Shape.push, pull := Shape.pull }

def rotate : PhaseAngle → Observable → Observable
  | .top, o@{phase := .norm, ..} => {o with phase := .norm}
  | .top, o@{phase := .unsafe, ..} => {o with phase := .unsafe}
  | .top, o@{phase := .safe, ..} => {o with phase := .safe}
  | .up, o@{phase := .norm, ..} => {o with phase := .safe}
  | .up, o@{phase := .unsafe, ..} => {o with phase := .norm}
  | .up, o@{phase := .safe, ..} => {o with phase := .unsafe}
  | .down, o@{phase := .norm, ..} => {o with phase := .safe}
  | .down, o@{phase := .unsafe, ..} => {o with phase := .norm}
  | .down, o@{phase := .safe, ..} => {o with phase := .unsafe}
  | .left, o@{phase := .norm, ..} => {o with phase := .unsafe}
  | .left, o@{phase := .unsafe, ..} => {o with phase := .safe}
  | .left, o@{phase := .safe, ..} => {o with phase := .norm}
  | .right, o@{phase := .norm, ..} => {o with phase := .unsafe}
  | .right, o@{phase := .unsafe, ..} => {o with phase := .safe}
  | .right, o@{phase := .safe, ..} => {o with phase := .norm}
  | .bot, o@{phase := .norm, ..} => {o with phase := .norm}
  | .bot, o@{phase := .unsafe, ..} => {o with phase := .unsafe}
  | .bot, o@{phase := .safe, ..} => {o with phase := .safe}

@[simp]
theorem rotate_top : ∀ p : PhaseAngle, ∀ o : Observable, p = .top → (o.rotate p).phase = o.phase := by
  intro p o _
  unfold rotate
  induction p <;> try contradiction
  cases h : o.phase <;> split <;> simp <;> contradiction

@[simp]
theorem rotate_bot : ∀ p : PhaseAngle, ∀ o : Observable, p = .bot → (o.rotate p).phase = o.phase := by
  intro p o _
  unfold rotate
  induction p <;> try contradiction
  cases h : o.phase <;> split <;> simp <;> contradiction

end Observable

abbrev Suggestion := Probability × String

def Observable.toSuggestion (o : Observable) : Suggestion :=
  (o.toProbability, toString o.carrier.val.raw.prettyPrint)

/--
Mechanism for associating semantics to instances of `Observable`.
-/
def Universal : PFunctor where
  A := Prop
  B := fun h => (_ : h) → Observable

instance : Coe Universal.A Prop := ⟨id⟩
instance : Coe Prop Universal.A := ⟨id⟩

protected instance Universal.prompt : Inhabited Universal.A where
  default :=
      ∀ x : Probability.{0}, decode? (encode x) = some x
    ∧ ∀ y : PhaseName, decode? (encode y) = some y
    ∧ ∀ z : Verified Syntax.Tactic, decode? (encode z) = some z
    ∧ ∀ o : Observable.{1}, decode? (encode o) = some o

instance {α} [Inhabited α] : Inhabited (Universal α) where
  default := ⟨default, fun _ => default⟩

protected def Universal.map {α β} := @PFunctor.map α β Universal

protected def Observable.observe {α} (o : Observable) (u : Universal α) := u.2 fun _ => o

variable {σ : Type u} {τ : Sodium σ}

protected def Observable.pointer (scope : ScopeName) : CryptoM τ Observable := do
  Observable.new (← `(tactic|rfl)) scope

open PrettyPrinter in
protected def Observable.quantize (o : Observable) (p : PhaseAngle := .up) : CryptoM τ Observable :=
  Meta.withNewMCtxDepth do
    let json := encode (← o.renew)
    Observable.rotate .left <$> Observable.rotate p <$> Observable.new (← `(tactic|exact ⟨$(← delab (mkStrLit json.compress))⟩))

open PrettyPrinter in
protected def Universal.print {α : Type} [Encodable α] (ε : Universal (MetaM α)) : Universal (CryptoM τ Observable) := by
  refine Universal.map (fun m => ?_) ε
  refine bind m fun a => ?_
  have e : Expr := mkStrLit (encode a).compress
  refine bind (delab e) fun x => ?_
  refine bind `(tactic|exact ⟨$x⟩) fun stx => ?_
  refine bind (Observable.new stx) fun o => ?_
  exact pure o

-- noncomputable def Universal.quantize? (α : Type) [Encodable α] (ε₀ : Universal Observable) : Universal (MetaM (Decrypt α)) := by
--   sorry

instance : Functor Universal where
  map := Universal.map

end Ethos

def Ethos := MVarId → Server (Array Ethos.Observable)

def EthosT {σ : Type u} (τ : Sodium σ) (m : {σ : Type u} → Sodium σ → Type → Type) (α : Type) := MVarId → ServerT τ m α

def EthosM {σ : Type u} (τ : Sodium σ) (α : Type) := MVarId → Ethos.Universal (ServerM τ α)

namespace Ethos

export Aesop (ScopeName)

variable {α β : Type} {σ : Type u} {τ : Sodium σ}

open Lean.Server.ServerTask in
protected def turn (ε : EthosM τ Observable) (scope : ScopeName := .global) : MVarId → Universal (CryptoM τ (ServerTask Observable)) := by
  intro δ
  refine Universal.map (fun k => ?_) (ε δ)
  exact δ.withContext do
    let o ← Observable.new (← `(tactic|aesop (add norm 0 unfold Ethos.Universal.prompt)
                                             (add norm 1 unfold Ethos.Universal.map)
                                             (add norm 2 unfold Ethos.Observable.encodable)
                                             (add safe 3 apply Ethos.Observable.renew)
                                             (add unsafe forward 34% Ethos.Observable.observe)))
    let keys ← mkStaleKeys
    match k {session := ← newSession? keys.pkey (client := scope = .local)} with
    | ⟨.ephemeral, k⟩ => return pure (← k ())
    | ⟨.addressed, k⟩ => do
      let o ← k (← encrypt o)
      return pure o
    | ⟨.anonymous, k⟩ => do
      let some o ← encryptAnon? keys.pkey o | default
      let o ← k o
      return pure o
    | ⟨.terminal, _⟩ => throwError m!"{(0 : Fin 1)}"
    | _ => return pure o

open Lean.Server.ServerTask in
protected def magic : MVarId → Universal (MetaM (ServerTask Observable)) := by
  intro δ
  refine ⟨default, fun k => ?_⟩
  refine δ.withContext do return pure (k ?_)
  unfold Ethos.Universal.prompt
  unfold Ethos.Observable.encodable
  simp only [Encodable.encodek, Encodable.ofEquiv, Option.map_some, Option.some.injEq, true_and, forall_const]
  intro _ o
  rfl

open Lean.Server.ServerTask in
protected def main (u : {σ : Type u} → (τ : Sodium σ) → EthosM τ Observable) : MVarId → MetaM (ServerTask Observable) := by
  intro δ
  refine δ.withContext <| CryptoM.toMetaM fun (τ : Sodium _) => ?_
  obtain ⟨_, k⟩ := Ethos.magic δ
  refine bind `(tactic|aesop (add norm 0 unfold Ethos.Universal.prompt)
                             (add norm 1 unfold Ethos.Universal.map)
                             (add safe 2 unfold Ethos.Observable.encodable)
                             (add unsafe 100% forward Ethos.Observable.observe))
    fun stx => ?_
  refine bind (Observable.new stx) fun o => ?_
  refine bind (k (fun _ => o)) fun o? => ?_
  have pull := o?.mapCostly fun o => o.observe <| Ethos.turn (scope := if o.phase = .safe then .local else .global) (u τ) δ
  exact pull.get

/--
The expression representing the proposition that all semantics can be encoded into Json.
-/
protected def Prompt : Expr := mkConst ``Ethos.Universal.prompt [levelZero]

def mkFreshDelta (name : Name := .anonymous) : MetaM Expr := Meta.mkFreshExprMVar (type? := Ethos.Prompt) .natural name

variable {σ : Type u}

#eval show MetaM Json from do
  let ε : {σ : Type} → (τ : Sodium.{0} σ) → EthosM τ Observable := fun _ _ => by
    refine ⟨default, fun k _ => ServerT.ephemeral ?_⟩
    let o := k (by aesop (add norm unfold Ethos.Universal.prompt))
    exact o.quantize

  let δ ← mkFreshDelta
  let o? ← Ethos.main (fun _ δ => ε _ δ) δ.mvarId!
  let o := o?.get

  return json% {
    "Δ" : $(toString (repr o)),
    "Δt" : $(toString (repr o.toProbability.quantize)),
    "ΔP" : $(o.toPercent.toFloat),
    phase : $(toString o.phase),
    format : $(toString o.pretty)
  }

#eval show MetaM Json from do
  let ε : {σ : Type} → (τ : Sodium.{0} σ) → EthosM τ Observable := fun _ δ => by
    refine ⟨default, fun k _ => ServerT.addressed ?_⟩
    exact fun msg => δ.withContext do
      let mo := k (by aesop (add norm unfold Ethos.Universal.prompt))
      println! f!"I can see a tactic worth {mo.toPercent}: {mo}"
      let .accepted o ← decrypt? (α := Observable) msg | default
      if mo.phase = o.phase then o.quantize
      else default

  let δ ← mkFreshDelta
  let o? ← Ethos.main (fun _ δ => ε _ δ) δ.mvarId!
  let o := o?.get

  return json% {
    "Δ" : $(toString (repr o)),
    "Δt" : $(toString (repr o.toProbability.quantize)),
    "ΔP" : $(o.toProbability.toFloat),
    phase : $(toString o.phase),
    format : $(toString o.pretty)
  }

end Ethos
