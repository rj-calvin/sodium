import Sodium.Ethos.Basic
import Sodium.Ethos.Possibly

open Lean Sodium Ethos Ristretto

declare_aesop_rule_sets [«temporal»] (default := false)

namespace Ethos

@[inherit_doc Ethos.Field] abbrev Universal.Field :=
  fun τ : Sodium (PLift (@default Prop Universal.prompt.{0})) =>
  Universal <| @Ethos.Field Universal.prompt.{0} τ (Point Syntax.Tactic)

@[inherit_doc Ethos.Lattice] abbrev Universal.Lattice :=
  fun τ : Sodium (PLift (@default Prop Universal.prompt.{0})) =>
  Universal <| @Ethos.Lattice Universal.prompt.{0} τ

/-- Round-trip `f` through `unimax`. -/
def Universal.lift (f : ∀ ε, (ψ : some (ε.quantize .global) = unimax.toNat) → δ% unimax, ε : ψ) : Universal.Field τ := by
  refine ⟨@default.{1} _ Universal.prompt.{0}, fun o => ?_⟩
  let o := o (by aesop (add norm unfold Universal.prompt))
  refine ⟨?_, fun w? => ?_⟩
  . exact fun ε hδ _ => f ε hδ hδ
  . unfold Universal.Field Ethos.Field at w?
    simp only [unimax_idx] at w? -- what to do with `Bool.rec`?
    match w? with | _ => exact ⟨some ⟨0, 1⟩, fun _ => o.carrier.val⟩

/--
info: 'Ethos.Universal.lift' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]
-/
#guard_msgs in
#print axioms Universal.lift

end Ethos
