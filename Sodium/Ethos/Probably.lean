import Sodium.Ethos.Basic
import Sodium.Ethos.Possibly

open Lean Sodium Ethos Ristretto

declare_aesop_rule_sets [«temporal»] (default := false)

namespace Ethos

@[inherit_doc Ethos.Field] abbrev Universal.Field :=
  fun τ : Sodium (PLift (@default _ Universal.prompt)) =>
  Universal <| @Ethos.Field.{1,0} Universal.prompt τ (Point Syntax.Tactic)

@[inherit_doc Ethos.Lattice] abbrev Universal.Lattice :=
  fun τ : Sodium (PLift (@default _ Universal.prompt)) =>
  Universal <| @Ethos.Lattice.{0} Universal.prompt τ

/-- Round-trip `f` through `unimax`. -/
def Universal.lift (f : ∀ ε, (ψ : some (ε.quantize .global) = unimax.toNat) → δ% unimax, ε : ψ) : Universal.Field τ := by
  refine ⟨@default _ Universal.prompt.{0}, fun o => ?_⟩
  let o := o (by aesop (add norm unfold Universal.prompt))
  refine ⟨?_, fun w? => ?_⟩
  . exact fun ε hδ _ => f ε hδ hδ
  . unfold Universal.Field Ethos.Field at w?
    simp only [unimax_idx] at w? -- what to do with `Bool.rec`?
    match w? with | _ => exact ⟨some ⟨0, 1⟩, fun _ => o.carrier.val⟩

/-- info: 'Ethos.Universal.lift' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound] -/
#guard_msgs in
#print axioms Universal.lift

/-- info: Try this: exact Field.ext_idx_top -/
#guard_msgs in
@[simp] theorem idx_top : Weight.IsScalar.{0} Δ(1 | 32) := by exact?

/-- info: Try this: exact Field.ext_idx_bot -/
#guard_msgs in
@[simp] theorem idx_bot : Weight.IsScalar.{0} Δ(0 | 32) := by exact?

/-- info: Try this: exact Field.ext_idx_one -/
#guard_msgs in
@[simp] theorem idx_one : Weight.IsScalar.{0} Δ(2 | 33) := by exact?

/-- info: Try this: exact Field.ext_idx_two -/
#guard_msgs in
@[simp] theorem idx_two : Weight.IsScalar.{0} Δ(3 | 34) := by exact?

/-- info: Try this: exact Field.ext_idx_three -/
#guard_msgs in
theorem idx_three : Δ(32 | 63).IsScalar := by exact?

end Ethos
