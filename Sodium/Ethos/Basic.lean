import Aesop
import Sodium.Ethos.Probability
import Sodium.Server.Monad

universe u

open Lean Sodium Crypto Meta

variable {σ : Type u}

namespace Aesop

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

inductive PhaseAngle where
  | up
  | down
  | left
  | right
  | top
  | bot

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

export Aesop (PhaseName PhaseAngle)

structure Observable extends Probability where
  phase : PhaseName
  carrier : Verified Syntax

namespace Observable

def format (o : Observable) : Format := o.carrier.val.prettyPrint
def size (o : Observable) : Nat := (toString o.format).length

protected def Id : PFunctor where
  A := Prop
  B := fun _ => Observable

instance : Coe Observable.Id.A Prop := ⟨id⟩

instance : Inhabited Observable.Id.A :=
  ⟨∀ x y, Probability.Shape.pull.{0} (Probability.Shape.part.{0} x) = some y → y.toFloat < x.toFloat⟩

instance : Coe (Observable.Id.B default) Observable := ⟨id⟩

@[always_inline]
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
  cases h : o.phase with
  | norm => split <;> simp <;> contradiction
  | safe => split <;> simp <;> contradiction
  | «unsafe» => split <;> simp <;> contradiction

@[simp]
theorem rotate_bot : ∀ p : PhaseAngle, ∀ o : Observable, p = .bot → (o.rotate p).phase = o.phase := by
  intro p o _
  unfold rotate
  induction p <;> try contradiction
  cases h : o.phase with
  | norm => split <;> simp <;> contradiction
  | safe => split <;> simp <;> contradiction
  | «unsafe» => split <;> simp <;> contradiction

theorem rotate_up? : ∀ p : PhaseAngle, ∃ o : Observable, p = .up → (o.rotate p).phase = .safe := by
  intro p
  unfold rotate
  sorry

end Ethos.Observable

def Ethos (τ : Sodium σ) (α : Type) :=
  MVarId → ServerM τ (Array (Syntax.Tactic × Ethos.Observable.Id α))

namespace Ethos

variable {τ : Sodium σ}

def map {α β} (f : α → β) (ε : Ethos τ α) : Ethos τ β :=
  fun δ => (ε δ {}).map (·.map fun ⟨t, o⟩ => ⟨t, ⟨default, fun k => f (o.snd k)⟩⟩)

def main {β} (session : Session τ Curve25519Blake2b) (α : Type) : (α → β) → Ethos τ α → Ethos τ β :=
  fun f ε δ => (ε δ {session}).map (·.map fun ⟨t, o⟩ => ⟨t, ⟨default, fun k => f (o.snd k)⟩⟩)

end Ethos
