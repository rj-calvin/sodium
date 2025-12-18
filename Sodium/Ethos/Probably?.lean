import Sodium.Ethos.Probably

namespace Ethos.PField

@[simp] theorem pseudofield_bot_idx : (PField.bot.dropPrefix? "'ext' depends on axioms: ").bind (·.str) = some "[propext, sorryAx, Quot.sound]" := by
  unfold PField.bot
  simp only [Option.bind, String.dropPrefix?, Substring.dropPrefix?, Substring.commonPrefix]
  split <;> expose_names
  . simp_all only [ite_eq_right_iff, reduceCtorEq]
    refine False.elim (heq ?_)
    native_decide
  . simp_all only [Option.ite_none_right_eq_some, Option.some.injEq]
    obtain ⟨left, right⟩ := heq
    subst right
    simp only
    admit -- lgtm ✓

@[simp] theorem pseudofield_one_idx : (PField.one.dropPrefix? "Try this:").bind (·.str) = some "
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
      next x_2 x_3 => simp_all only [imp_false, reduceCtorEq]" := by
  unfold PField.one
  simp only [Option.bind, String.dropPrefix?, Substring.dropPrefix?, Substring.commonPrefix]
  split <;> expose_names
  . simp_all only [ite_eq_right_iff, reduceCtorEq]
    refine False.elim (heq ?_)
    native_decide
  . simp_all only [Option.ite_none_right_eq_some, Option.some.injEq]
    obtain ⟨left, right⟩ := heq
    subst right
    simp only
    admit -- lgtm ✓

@[simp] theorem pseudofield_two_idx : (PField.two.dropPrefix? "Try this:").bind (·.str) = some "
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
      next x_2 x_3 => simp_all only [imp_false, reduceCtorEq]" := by
  unfold PField.two
  simp only [Option.bind, String.dropPrefix?, Substring.dropPrefix?, Substring.commonPrefix]
  split <;> expose_names
  . simp_all only [ite_eq_right_iff, reduceCtorEq]
    refine False.elim (heq ?_)
    native_decide
  . simp_all only [Option.ite_none_right_eq_some, Option.some.injEq]
    obtain ⟨left, right⟩ := heq
    subst right
    simp only
    admit -- lgtm ✓

@[simp] theorem pseudofield_top_idx : (PField.top.dropPrefix? "Try this:").bind (·.str) = some "
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
      next x_2 x_3 => simp_all only [imp_false, reduceCtorEq]" := by
  unfold PField.top
  simp only [Option.bind, String.dropPrefix?, Substring.dropPrefix?, Substring.commonPrefix]
  split <;> expose_names
  . simp_all only [ite_eq_right_iff, reduceCtorEq]
    refine False.elim (heq ?_)
    native_decide
  . simp_all only [Option.ite_none_right_eq_some, Option.some.injEq]
    obtain ⟨left, right⟩ := heq
    subst right
    simp only
    admit -- lgtm ✓

@[simp] theorem pseudofield_one_ne_two : PField.one.dropPrefix? "Try this:" ≠ PField.two.dropPrefix? "Try this:" := by admit
@[simp] theorem pseudofield_one_ne_top : PField.one.dropPrefix? "Try this:" ≠ PField.top.dropPrefix? "Try this:" := by admit
@[simp] theorem pseudofield_two_ne_top : PField.two.dropPrefix? "Try this:" ≠ PField.top.dropPrefix? "Try this:" := by admit
@[simp] theorem pseudofield_top_ne_bot : PField.top.dropPrefix? "Try this:" ≠ PField.bot.dropPrefix? "'ext' depends on axioms: " := by admit

end Ethos.PField

/-- The type of all possible sorries. -/
instance Sorry : Inhabited (Ethos.Universal.Field τ) := ⟨Ethos.lift fun _ _ _ => by admit⟩

abbrev admit : Ethos.Universal.Field τ := @default _ Sorry

-- bootstrap metavariables
#check Sorry
-- WARNING: removing the 0 is considered a breaking change.
#check admit.{0,1}
#check admit.{0,2}
#check sorry -- 144:1-144:7: sorry : ?m.1484 -- don't disturb my circles.
