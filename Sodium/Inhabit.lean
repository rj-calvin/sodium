import Lean

open Lean Elab Tactic

namespace Lean.Elab.Tactic

noncomputable def nonempty_inhabitation (α : Sort _) (_ : Nonempty α) : Inhabited α :=
  Inhabited.mk Classical.ofNonempty

def nonempty_prop_inhabitation (α : Prop) (non : Nonempty α) : Inhabited α :=
  Inhabited.mk <| Nonempty.elim non id

syntax (name := inhabit) "inhabit " atomic(ident " : ")? term : tactic

def evalInhabit (goal : MVarId) (name? : Option Ident) (term : Syntax) : TacticM MVarId := goal.withContext do
  let e ← Tactic.elabTerm term none
  let lvl ← Meta.getLevel e
  let nonempty ← Meta.synthInstance <| mkApp (mkConst ``Nonempty [lvl]) e 
  let name := name?.map (·.getId) |>.getD `«inhabited»
  let lift ←
    if ← Meta.isProp e then Meta.mkAppM ``nonempty_prop_inhabitation #[e, nonempty]
    else Meta.mkAppM ``nonempty_inhabitation #[e, nonempty]
  let inhabited := mkApp (mkConst ``Inhabited [lvl]) e
  let (_, α) ← (← goal.assert name inhabited lift).intro1P
  return α

elab_rules : tactic
| `(tactic| inhabit $[$name?:ident :]? $term) => do
  let goal ← evalInhabit (← getMainGoal) name? term
  replaceMainGoal [goal]

end Lean.Elab.Tactic
