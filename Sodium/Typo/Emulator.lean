import Sodium.Ethos.Probably

open Lean Elab Tactic Sodium Crypto Ethos

attribute [aesop norm unfold (rule_sets := [«standard»])]
  Universal.prompt

attribute [aesop [unsafe 29% constructors (rule_sets := [«standard»]), safe cases (rule_sets := [«cautious»])]]
  MessageKind

attribute [aesop safe cases (rule_sets := [«standard», «cautious»])]
  Decrypt

attribute [aesop norm unfold (rule_sets := [«cautious»])]
  Observable.encodable

attribute [aesop unsafe 31% apply (rule_sets := [«cautious»]) (pattern := CryptoM _ Observable)]
  Observable.observe

namespace Typo

@[reducible]
def Shape := Option (Option Char)

@[reducible]
def Escape : Shape := some (some '\x1b')

namespace Shape

notation "top%" => some none
notation "shape% " γ => some (some («α» := «Char») γ)

instance : Inhabited Shape := ⟨Escape⟩
instance : Encodable Shape := by unfold Shape; infer_instance
instance : DecidableEq Shape := by unfold Shape; infer_instance

def quantize {τ : Sodium σ} (scope : ScopeName := .local) : Shape → CryptoM τ Observable
| shape% γ => do Observable.new <| ← `(tactic|exact ⟨$(Syntax.mkCharLit γ)⟩)
| top% => Observable.pointer (if scope = .local then .global else .local)
| _ => Observable.pointer scope

variable [io : Ethos.World] in
structure _root_.IO.RealWorld.Shape where
  shape : Typo.Shape
  witness : Witness io.τ := ⟨@default _ Universal.prompt.{0}, fun _ => shape.quantize⟩

end Shape

@[reducible]
def Point := Option (Syntax.Tactic ⊕ Syntax)

@[reducible]
def Origin : Point := some (.inr default)

namespace Point

notation "point% " γ => some (Sum.inl («α» := «Syntax».«Tactic») («β» := «Syntax») γ)
notation "bot%" => some (Sum.inr («α» := «Syntax».«Tactic») default)

instance : Inhabited Point := ⟨Origin⟩
instance : Encodable Point := by unfold Point; infer_instance

variable [io : World] in
def quantize (scope : ScopeName := .global) : Point → CryptoM io.τ Observable
| point% γ => Observable.new γ scope
| bot% => Observable.pointer scope
| _ => Observable.pointer (if scope = .local then .global else .local)

variable [io : World] in
structure _root_.IO.RealWorld.Point where
  point : Typo.Point
  witness : Witness io.τ := ⟨@default _ Universal.prompt.{1}, fun _ => point.quantize⟩

end Point

/--
An `Emulator` simulates the operations of a `Typewriter`.

Here "simulates" means that it is defined using only the default syntax
categories (.e.g. the ones used to elaborate this declaration). This is relevant
since a `Typewriter` can only be meaningfully defined relative to the standard
of the user's keyboard. As a consequence, we're compelled to declare `Emulator`
_before_ we define the thing it exists to emulate.

In layman's terms, `Emulator` lets you build tools with typewriters without
needing to import the file that declares the letter `x` as a keyword.

See `Sodium.Typo.Frontend.Qwerty` for an example `Typewriter`.
-/
@[reducible]
def Emulator [io : World] : PFunctor where
  A := IO.RealWorld.Shape × IO.RealWorld.Point
  B | ⟨⟨none, _⟩, _⟩ | ⟨_, ⟨none, _⟩⟩ => PEmpty
    | ⟨⟨top%, _⟩, ⟨bot%, _⟩⟩ => PUnit
    | ⟨⟨shape% _, _⟩, ⟨bot%, _⟩⟩ => Tactic
    | _ => TermElabM Shape

namespace Emulator

section quotPrecheckFalse
set_option quotPrecheck false

notation "pos%" => ⟨⟨none, _⟩, _⟩
notation "neg%" => ⟨_, ⟨none, _⟩⟩

notation "stop% " =>
  ⟨{«shape» := top% : «IO».«RealWorld».«Shape»}, {«point» := bot% : «IO».«RealWorld».«Point»}⟩

notation "start% " β =>
  ⟨{«shape» := top% : «IO».«RealWorld».«Shape»}, {«point» := point% β : «IO».«RealWorld».«Point»}⟩

notation "stage% " α =>
  ⟨{«shape» := shape% α : «IO».«RealWorld».«Shape»}, {«point» := bot% : «IO».«RealWorld».«Point»}⟩

notation "commit% " α ", " β =>
  ⟨{«shape» := shape% α : «IO».«RealWorld».«Shape»}, {«point» := point% β : «IO».«RealWorld».«Point»}⟩

end quotPrecheckFalse

@[reducible]
protected def map [World] {α β} := @PFunctor.map α β Emulator

instance [World] : Functor Emulator where
  map := Emulator.map

@[simp] theorem emulator_idx [World] :
  Emulator.A = (IO.RealWorld.Shape × IO.RealWorld.Point) := rfl

@[simp] theorem emulator_stop_idx [World] : Emulator.B stop% = PUnit := rfl
@[simp] theorem emulator_start_idx [World] : ∀ β, Emulator.B (start% β) = TermElabM Shape := by intro; rfl
@[simp] theorem emulator_stage_idx [World] : ∀ α, Emulator.B (stage% α) = Tactic := by intro; rfl
@[simp] theorem emulator_commit_idx [World] : ∀ α β, Emulator.B (commit% α, β) = TermElabM Shape := by intros; rfl

/-- Produce a stream of bytes on `log` using magic. -/
def bridge
  (log : IO.FS.Stream)
  (v : Level := levelOne)
  (scope : ScopeName := .local)
  (config : TSyntaxArray `Aesop.tactic_clause := #[])
  [io : World]
: CryptoM io.τ (Emulator (TermElabM Shape)) := do
  let γ ← `(tactic|aesop (rule_sets := [«standard», «cautious», «external», «temporal»]) $config*)
  let o ← Observable.new γ scope
  let log ← (if scope = .global then IO.setStdout else IO.setStderr) log
  let ε : Emulator.A := start% γ
  let δ : Emulator.B ε → Witness io.τ := fun α => by
    refine ⟨@default _ Universal.prompt.{0}, fun β => ?_⟩
    subst ε
    simp only at α
    exact try
      let ζ ← mkFreshDelta Ristretto.unimax v
      let ⟨x, _⟩ ← runTactic ζ.mvarId! γ
      let _ ← instantiateMVars ζ
      let (x, _) ← Aesop.runTacticMAsMetaM α x
      return β (by aesop (add norm unfold Universal.prompt))
    catch _ => o.renew scope
  let δ := δ <| pure (default : Shape)
  δ.emit log o
  return by
    refine Emulator.map o.observe ⟨ε, fun δ => ?_⟩
    refine ⟨@default _ Universal.prompt.{0}, fun _ => ?_⟩
    subst ε
    simp only at δ
    exact δ

end Emulator

@[reducible]
def Destructor [io : World] := Emulator.W

namespace Destructor

variable [io : World]

abbrev mk := @PFunctor.W.mk Emulator
abbrev next := @PFunctor.W.next Emulator
abbrev head := @PFunctor.W.head Emulator
abbrev children := @PFunctor.W.children Emulator
abbrev cases := @PFunctor.W.cases Emulator

end Destructor

end Typo
