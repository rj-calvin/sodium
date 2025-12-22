import Sodium.Ethos.Probably

open Lean Elab Tactic Sodium Crypto Ethos

declare_aesop_rule_sets [«external»] (default := false)

attribute [aesop norm 0 unfold (rule_sets := [«standard»])]
  Universal.prompt

attribute [aesop [unsafe 29% constructors (rule_sets := [«standard»]), safe cases (rule_sets := [«cautious»])]]
  MessageKind

attribute [aesop safe 0 cases (rule_sets := [«standard», «cautious»])]
  Decrypt

attribute [aesop norm unfold (rule_sets := [«cautious»])]
  Observable.encodable

attribute [aesop unsafe 31% apply (rule_sets := [«cautious»]) (pattern := CryptoM _ Observable)]
  Observable.observe

namespace Typo

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
instance : DecidableEq Shape := by unfold Shape; infer_instance

def quantize {τ : Sodium σ} (scope : ScopeName := .local) : Shape → CryptoM τ Observable
| shape% γ => do Observable.new <| ← `(tactic|exact ⟨$(Syntax.mkCharLit γ)⟩)
| top% => Observable.pointer (if scope = .local then .global else .local)
| _ => Observable.pointer scope

structure _root_.IO.RealWorld.Shape (τ : Sodium σ) where
  shape : Typo.Shape
  witness : Witness τ := ⟨@default.{1} _ Universal.prompt.{0}, fun _ => shape.quantize⟩

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

def quantize {τ : Sodium σ} (scope : ScopeName := .global) : Point → CryptoM τ Observable
| point% γ => Observable.new γ scope
| bot% => Observable.pointer scope
| _ => Observable.pointer (if scope = .local then .global else .local)

structure _root_.IO.RealWorld.Point (τ : Sodium σ) where
  point : Typo.Point
  witness : Witness τ := ⟨@default.{1} _ Universal.prompt.{0}, fun _ => point.quantize⟩

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

@[reducible]
protected def map {α β} := @PFunctor.map α β (Emulator σ)

instance : Functor (Emulator σ) where
  map := Emulator.map

variable {τ : Sodium σ}

@[simp] theorem emulator_idx :
  (Emulator σ).A = Σ' τ : Sodium σ, IO.RealWorld.Shape τ × IO.RealWorld.Point τ := rfl

@[simp] theorem emulator_stop_idx : (Emulator σ).B (stop% τ) = PUnit := rfl
@[simp] theorem emulator_start_idx : ∀ β, (Emulator σ).B (start% τ, β) = TermElabM Shape := by intro; rfl
@[simp] theorem emulator_stage_idx : ∀ α, (Emulator σ).B (stage% τ, α) = Tactic := by intro; rfl
@[simp] theorem emulator_commit_idx : ∀ α β, (Emulator σ).B (commit% τ, α, β) = TermElabM Shape := by intros; rfl

/-- Produce a stream of bytes on `log` using magic. -/
def bridge
  (log : IO.FS.Stream)
  (config : TSyntaxArray `Aesop.tactic_clause := #[])
  (u : Level := levelZero)
  (v : Level := levelOne)
  (scope : ScopeName := .local)
  : MetaM (Emulator σ (TermElabM Shape)) :=
do CryptoM.toMetaM (ctx := .ofString "cautious") fun τ : Sodium _ => do
  let γ ← `(tactic|aesop (rule_sets := [«standard», «cautious»]) $config*)
  let o ← Observable.new γ scope
  let log ← (if scope = .global then IO.setStdout else IO.setStderr) log
  let ε : (Emulator σ).A := start% τ, γ
  let δ : (Emulator _).B ε → Witness τ := fun α => by
    refine ⟨@default.{1} _ Universal.prompt.{0}, fun β => ?_⟩
    subst ε
    simp only at α
    exact try
      let ζ ← mkFreshDelta u v
      let ⟨x, _⟩ ← runTactic ζ.mvarId! γ
      let _ ← instantiateMVars ζ
      let (x, _) ← Aesop.runTacticMAsMetaM α x
      return β (by aesop (add norm unfold Universal.prompt))
    catch _ => o.renew scope
  let δ := δ <| pure (default : Shape)
  δ.emit log o
  return by
    refine Emulator.map o.observe ⟨ε, fun δ => ?_⟩
    refine ⟨@default.{1} _ Universal.prompt.{0}, fun _ => ?_⟩
    subst ε
    simp only at δ
    exact δ

end Emulator

@[reducible]
def Destructor := PFunctor.W <| Emulator Universal.Destruct

namespace Destructor

abbrev mk := @PFunctor.W.mk (Emulator Universal.Destruct)
abbrev next := @PFunctor.W.next (Emulator Universal.Destruct)
abbrev head := @PFunctor.W.head (Emulator Universal.Destruct)
abbrev children := @PFunctor.W.children (Emulator Universal.Destruct)
abbrev cases := @PFunctor.W.cases (Emulator Universal.Destruct)

end Destructor

end Typo
