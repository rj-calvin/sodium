import Sodium.Ethos.Basic
import Sodium.Ethos.Possibly?

open Lean Elab Tactic Sodium Crypto Aesop Ethos Ristretto

@[inherit_doc Ethos.Field] abbrev Ethos.Universal.Field :=
  fun τ : Sodium (PLift (@default Prop Universal.prompt.{0})) =>
  Universal <| @Ethos.Guage Universal.prompt.{0} τ Syntax.Tactic

namespace Ethos.PField

protected def bot := "'ext' depends on axioms: [propext, sorryAx, Quot.sound]"

protected def top := "Try this:
  apply And.intro
  · unfold Lean.Level.toNat
    unfold Lean.Level.getOffset
    simp_all only [unimax_idx]
    rfl
  · unfold Lean.Level.toNat
    unfold Lean.Level.getOffset
    simp_all only [Option.bind, unimax_idx, Nat.succ_eq_add_one, Nat.reduceAdd, Option.pure_def]
    split
    next x x_1 heq =>
      simp_all only [Option.not_lt_none]
      split at heq
      next x_2 heq_1 => simp_all only [reduceCtorEq]
      next x_2 x_3 =>
        simp_all only [imp_false]
        (admit)
    next x x_1 a heq =>
      simp_all only [Option.some_lt_some]
      split at heq
      next x_2 heq_1 =>
        simp_all only [Option.some.injEq]
        subst heq
        (admit)
      next x_2 x_3 => simp_all only [imp_false, reduceCtorEq]"

protected def one := "Try this:
  apply And.intro
  · unfold Lean.Level.toNat
    unfold Lean.Level.getOffset
    simp_all only [unimax_idx]
    rfl
  · unfold Lean.Level.toNat
    unfold Lean.Level.getOffset
    simp_all only [Option.bind, unimax_idx, Nat.succ_eq_add_one, Nat.reduceAdd, Option.pure_def]
    split
    next x x_1 heq =>
      simp_all only [Option.not_lt_none]
      split at heq
      next x_2 heq_1 => simp_all only [reduceCtorEq]
      next x_2 x_3 =>
        simp_all only [imp_false]
        (contradiction)
    next x x_1 a heq =>
      simp_all only [Option.some_lt_some]
      split at heq
      next x_2 heq_1 =>
        simp_all only [Option.some.injEq]
        subst heq
        (native_decide)
      next x_2 x_3 => simp_all only [imp_false, reduceCtorEq]"

protected def two := "Try this:
  apply And.intro
  · unfold Lean.Level.toNat
    simp_all only [unimax_idx]
    rfl
  · unfold Lean.Level.toNat
    simp_all only [Option.bind, unimax_idx, Nat.succ_eq_add_one, Nat.reduceAdd, Option.pure_def]
    split
    next x x_1 heq =>
      simp_all only [Option.not_lt_none]
      split at heq
      next x_2 heq_1 => simp_all only [reduceCtorEq]
      next x_2 x_3 =>
        simp_all only [imp_false]
        (contradiction)
    next x x_1 a heq =>
      simp_all only [Option.some_lt_some]
      split at heq
      next x_2 heq_1 =>
        simp_all only [Option.some.injEq]
        subst heq
        (native_decide)
      next x_2 x_3 => simp_all only [imp_false, reduceCtorEq]"

end PField

/-- A `PField` is a mechanism for bootstrapping semantic reasoning from axioms. -/
def PField.{u} : PFunctor where
  A := ULift.{u} (String × Sodium (PLift (@default Prop Universal.prompt.{0})))
  B i :=
    if _ : some i.down.1 = (PField.bot.dropPrefix? "'ext' depends on axioms: ").bind (·.str) then Unit else
    if _ : some i.down.1 = (PField.top.dropPrefix? "Try this:").bind (·.str) then Lattice (τ := i.down.2) else
    if _ : some i.down.1 = (PField.one.dropPrefix? "Try this:").bind (·.str) then Lattice (τ := i.down.2) else
    if _ : some i.down.1 = (PField.two.dropPrefix? "Try this:").bind (·.str) then Lattice (τ := i.down.2) else
    Empty

namespace PField

@[simp] theorem pseudofield_idx : PField.A = ULift (String × Sodium (PLift (@default Prop Universal.prompt))) := rfl

/-- For pre-computed partial idx theorems, see `Sodium.Ethos.Probably?`. -/
@[simp] theorem pseudofield_partial_idx : ∀ i : PField.A, PField.B i =
    if _ : some i.down.1 = (PField.bot.dropPrefix? "'ext' depends on axioms: ").bind (·.str) then Unit else
    if _ : some i.down.1 = (PField.top.dropPrefix? "Try this:").bind (·.str) then Lattice (τ := i.down.2) else
    if _ : some i.down.1 = (PField.one.dropPrefix? "Try this:").bind (·.str) then Lattice (τ := i.down.2) else
    if _ : some i.down.1 = (PField.two.dropPrefix? "Try this:").bind (·.str) then Lattice (τ := i.down.2) else
    Empty := by
  intro ⟨_⟩; rfl

end PField

/-- Round-trip `f` through `unimax` -/
def lift (f : ∀ ε, (ψ : some (ε.quantize .global) = unimax.toNat) → δ% unimax, ε : ψ) : Universal.Field τ := by
  refine ⟨default, fun o => ?_⟩
  let o := o (by aesop (add norm unfold Universal.prompt))
  refine ⟨?_, fun w? => ?_⟩
  . exact fun ε hδ _ => f ε hδ hδ
  . unfold Universal.Field Field at w?
    simp only [unimax_idx] at w? -- what to do with `Bool.rec`?
    match w? with | _ => exact o.carrier.val

end Ethos
