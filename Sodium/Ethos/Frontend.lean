import Sodium.Ethos.Basic

universe u

open Lean Sodium Aesop Meta Elab Term Tactic

namespace Ethos

declare_syntax_cat Ethos.message_kind (behavior := symbol)
syntax &"ephemeral" : Ethos.message_kind
syntax &"addressed" : Ethos.message_kind
syntax &"anonymous" : Ethos.message_kind
syntax &"partial" : Ethos.message_kind
syntax &"terminal" : Ethos.message_kind

declare_syntax_cat Ethos.prompt (behavior := symbol)
syntax " (" &"prompt" " := " term ")" : Ethos.prompt

def Prompt.elab (stx : Syntax) : ElabM Expr :=
  withRef stx do
    match stx with
    | `(prompt|(prompt := $t)) => elabTermEnsuringType t (mkSort 0)
    | _ => throwUnsupportedSyntax

open PrettyPrinter in
elab "ethos" m?:(Ethos.message_kind)? p:Ethos.prompt rules:Aesop.tactic_clause* body:term : tactic => do
  evalTactic <| ← `(tactic|try intro)
  let δ ← getMainGoal
  let x ← runTermElab <| withNewMCtxDepth <| ElabM.runForwardElab δ (Prompt.elab p)
  let x ← delab x
  let m ← m?.getDM `(Ethos.message_kind|ephemeral)
  match m with
  | `(Ethos.message_kind|ephemeral) => evalRefine <| ← `(tactic|refine ⟨$x, fun _ _ => ServerT.ephemeral ?_⟩)
  | `(Ethos.message_kind|addressed) => evalRefine <| ← `(tactic|refine ⟨$x, fun _ _ => ServerT.addressed ?_⟩)
  | `(Ethos.message_kind|anonymous) => evalRefine <| ← `(tactic|refine ⟨$x, fun _ _ => ServerT.anonymous ?_⟩)
  | _ => evalRefine <| ← `(tactic|refine ⟨$(⟨p.raw⟩), fun _ _ => ?_⟩)
  evalTactic <| ← `(tactic|expose_names)
  evalTactic <| ← `(tactic|have : Observable := $(mkIdent `x) (by aesop $rules*))
  evalTactic <| ← `(tactic|expose_names)
  evalTactic <| ← `(tactic|exact $body)

open Command in
elab "#ethos" " => " t:term : command => do
  elabCommand <| ← `(command|#eval show MetaM Json from Sodium.Crypto.CryptoM.toMetaM fun τ : Sodium.{0} _ => $t)

section Examples

open Crypto

variable {σ : Type} (τ : Sodium σ)

def EchoServer : EthosM τ Observable := by
  ethos addressed (prompt := default) (add norm unfold Ethos.Universal.prompt) fun msg => do
    unless this.phase = .safe do default
    let .accepted x ← decrypt? (α := Observable) msg | default
    println! format x
    x.quantize

#ethos => do
  let δ ← mkFreshDelta
  let o? ← Ethos.main EchoServer δ.mvarId!
  let o := o?.get

  return json% {
    Δ: $(repr o.toProbability |> toString),
    Δt: $(o.toProbability.quantize),
    Δp: $(o.toProbability.toFloat),
    phase: $(toString o.phase)
  }

def EchoServer.prompt : EthosM τ Observable := by
  ethos (prompt := default) (add norm unfold Ethos.Universal.prompt) do
    unless this.phase = .safe do default
    Observable.new <| ← `(tactic|
      ethos addressed (prompt := default) (add norm unfold Ethos.Universal.prompt) fun msg => do
        unless this.phase = .safe do default;
        let .accepted x ← decrypt? (α := Observable) msg | default;
        println! format x;
        x.quantize)

#ethos => do
  let δ ← mkFreshDelta
  let o? ← Ethos.main EchoServer.prompt δ.mvarId!
  let o := o?.get

  return json% {
    Δ: $(repr o.toProbability |> toString),
    Δt: $(o.toProbability.quantize),
    Δp: $(o.toProbability.toFloat),
    phase: $(toString o.phase),
    format: $(toString o.pretty)
  }

end Examples

end Ethos
