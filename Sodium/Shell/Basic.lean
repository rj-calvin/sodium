import Sodium.Typography.Frontend.Qwerty

open Lean Sodium Ethos

set_option trace.aesop true

example : Universal (PLift (∀ α, (Observable.Shape.push α).pull = α)) := by
  aesop? (rule_sets := [«standard», «cautious», «external»]) (config := {warnOnNonterminal := false})
