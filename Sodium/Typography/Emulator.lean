import Sodium.Ethos.Basic

open Lean Elab Tactic Sodium Crypto Ethos

attribute [aesop norm 0 unfold (rule_sets := [«standard»])]
  Universal.prompt Universal.map

attribute [aesop unsafe 31% unfold (rule_sets := [«cautious»])]
  Observable.encodable

attribute [aesop safe 0 apply (rule_sets := [«cautious»])]
  Observable.observe

attribute [aesop safe [constructors (rule_sets := [«cautious»]), cases (rule_sets := [«standard»])]]
  MessageKind

namespace Typography

variable {σ}

@[reducible]
def Shape := Option (Option Char)

@[reducible]
def Escape : Shape := some (some '\x1b')

namespace Shape

notation "top%" => some none
notation "shape% " γ => some (some («α» := «Char») γ)

instance : Inhabited Shape := ⟨Escape⟩
instance : Encodable Shape := by unfold Shape; infer_instance

def quantize {τ : Sodium σ} (scope : ScopeName := .local) : Shape → CryptoM τ Observable
| shape% γ => do Observable.new <| ← `(tactic|exact ⟨$(Syntax.mkCharLit γ)⟩)
| top% => Observable.pointer (if scope = .local then .global else .local)
| _ => Observable.pointer scope

structure _root_.IO.RealWorld.Shape (τ : Sodium σ) where
  shape : Typography.Shape
  witness : Witness τ := ⟨default, fun _ => shape.quantize⟩

end Shape

@[reducible]
def Point := Option (Syntax.Tactic ⊕ Syntax)

@[reducible]
def Null : Point := some (.inr default)

namespace Point

notation "point% " γ => some (Sum.inl («α» := «Syntax».«Tactic») («β» := «Syntax») γ)
notation "bot%" => some (Sum.inr («α» := «Syntax».«Tactic») default)

instance : Inhabited Point := ⟨Null⟩
instance : Encodable Point := by unfold Point; infer_instance

def quantize {τ : Sodium σ} (scope : ScopeName := .global) : Point → CryptoM τ Observable
| point% γ => Observable.new γ scope
| bot% => Observable.pointer scope
| _ => Observable.pointer (if scope = .local then .global else .local)

structure _root_.IO.RealWorld.Point (τ : Sodium σ) where
  point : Typography.Point
  witness : Witness τ := ⟨default, fun _ => point.quantize⟩

end Point

/--
An `Emulator` simulates the operations of a `Typewriter`.

Here "simulates" means that it is defined using only the default syntax
categories (.e.g. the ones used to elaborate this file). This is relevant since
a `Typewriter` can only be meaningfully defined relative to the standard of the
user's keyboard. As a consequence, we're compelled to declare `Emulator`
_before_ we define the thing it exists to emulate.

In layman's terms, `Emulator` lets you build tools with typewriters without
needing to import the file that declares the letter `x` as a keyword.

See `Sodium.Typography.Frontend.Qwerty` for an example `Typewriter`.
-/
@[reducible]
def Emulator (σ : Type) : PFunctor where
  A := Σ' τ : Sodium σ, IO.RealWorld.Shape τ × IO.RealWorld.Point τ
  B | ⟨_, ⟨⟨none, _⟩, _⟩⟩ | ⟨_, ⟨_, ⟨none, _⟩⟩⟩ => PEmpty
    | ⟨_, ⟨⟨top%, _⟩, ⟨bot%, _⟩⟩⟩ => PUnit
    | ⟨_, ⟨⟨shape% _, _⟩, ⟨bot%, _⟩⟩⟩ => Tactic
    | _ => TermElabM Shape

namespace Emulator

section quotPrecheckFalse
set_option quotPrecheck false

notation "pos% " τ => ⟨τ, ⟨⟨none, _⟩, _⟩⟩
notation "neg% " τ => ⟨τ, ⟨_, ⟨none, _⟩⟩⟩

notation "stop% " τ =>
  ⟨τ, ⟨{«shape» := top% : «IO».«RealWorld».«Shape» τ}, {«point» := bot% : «IO».«RealWorld».«Point» τ}⟩⟩

notation "start% " τ ", " β =>
  ⟨τ, ⟨{«shape» := top% : «IO».«RealWorld».«Shape» τ}, {«point» := point% β : «IO».«RealWorld».«Point» τ}⟩⟩

notation "stage% " τ ", " α =>
  ⟨τ, ⟨{«shape» := shape% α : «IO».«RealWorld».«Shape» τ}, {«point» := bot% : «IO».«RealWorld».«Point» τ}⟩⟩

notation "commit% " τ ", " α ", " β =>
  ⟨τ, ⟨{«shape» := shape% α : «IO».«RealWorld».«Shape» τ}, {«point» := point% β : «IO».«RealWorld».«Point» τ}⟩⟩

end quotPrecheckFalse

@[aesop norm]
protected def map {α β} := @PFunctor.map α β (Emulator σ)

instance : Coe (Emulator σ).A (Σ' τ : Sodium σ, IO.RealWorld.Shape τ × IO.RealWorld.Point τ) := ⟨id⟩
instance : Coe (Σ' τ : Sodium σ, IO.RealWorld.Shape τ × IO.RealWorld.Point τ) (Emulator σ).A := ⟨id⟩

/--
Produce a stream of bytes on `log` using magic.
-/
def bridge
  (log : IO.FS.Stream)
  (config : TSyntaxArray `Aesop.tactic_clause := #[])
  (scope : ScopeName := .global)
  (u : Level := levelZero)
  (v : Level := levelOne)
  : MetaM (Emulator Syntax.Tactic (TermElabM Shape)) :=
do CryptoM.toMetaM fun τ : Sodium.{0} _ => do
  let γ ← `(tactic|aesop (rule_sets := [«standard»]) $config*)
  let o ← Observable.new γ scope
  let log ← (if scope = .global then IO.setStdout else IO.setStderr) log
  let ε : (Emulator.{0,0} _).A := start% τ, γ
  let δ : (Emulator.{0,0} _).B ε → Witness τ := fun α => by
    refine ⟨default, fun β => ?_⟩
    unfold Emulator at α
    unfold Universal at β
    subst ε
    simp only at α β
    exact try
      let ζ ← mkFreshDelta u v
      let ⟨x, _⟩ ← runTactic ζ.mvarId! γ
      let _ ← instantiateMVars ζ
      let (x, _) ← Aesop.runTacticMAsMetaM α x
      return β (by aesop (add norm unfold Universal.prompt))
    catch _ => o.renew scope
  (δ (pure (default : Shape))).emit log o
  return by
    refine Emulator.map o.observe ⟨ε, fun δ => ?_⟩
    refine ⟨default, fun _ => ?_⟩
    unfold Emulator at δ
    subst ε
    simp only at δ
    exact δ

end Emulator

end Typography
