import «Sodium».Typo.Frontend.Qwerty

universe «u»

open Lean Sodium Crypto Ethos

/--
HACK: This is a workaround for ensuring that `aesop`'s proof reconstruction works.
-/
@[aesop norm unfold (rule_sets := [«external»])]
instance prompt : Inhabited Prop := Universal.prompt.{0}

@[aesop norm forward (rule_sets := [«external»])]
def construct : @default Prop prompt := by
  unfold prompt Universal.prompt
  simp only [Encodable.encodek, implies_true, and_self]

@[aesop unsafe 0% apply (rule_sets := [«external»])] -- 0% to force termination before any "impossible" tactics are run.
def destruct (fwd : Universal.Forward.{«u»}) : Universal Universal.Destruct.{«u»} := by
  refine ⟨default, fun α => ?_⟩
  have : Observable := α construct
  exact ⟨fwd this.carrier⟩

example : Universal Universal.Destruct.{0} := by
  aesop? (rule_sets := [«standard», «cautious», «external»])
