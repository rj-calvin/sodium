import «Sodium».Typo.Frontend.Qwerty

open Lean Elab Tactic PrettyPrinter Sodium Crypto Ethos Typo Aesop

universe «u»

variable {τ : Sodium Universal.Destruct}

attribute [aesop norm 0]
  Universal.universal_idx Universal.universal_default_idx

attribute [aesop safe cases (rule_sets := [«external»])]
  WType

attribute [aesop safe forward (rule_sets := [«external»])]
  PFunctor.W.head

attribute [aesop norm 9973 unfold (rule_sets := [«external»])]
  PFunctor.W.children

attribute [aesop safe apply (rule_sets := [«external»])]
  PFunctor.W.cases

/--
HACK: This is a workaround for ensuring that `aesop`'s proof reconstruction works.
-/
@[aesop norm unfold (rule_sets := [«external»])]
instance prompt : Inhabited Prop := Universal.prompt.{0}

@[aesop norm forward (rule_sets := [«external»])]
def construct : @default Prop prompt := by
  unfold prompt Universal.prompt
  simp only [Encodable.encodek, implies_true, and_self]

@[aesop unsafe apply (rule_sets := [«external»])]
def destruct (fwd : Universal.Forward) : Universal Universal.Destruct := by
  refine ⟨default, fun α => ?_⟩
  have : Observable := α construct
  exact ⟨fwd this.carrier⟩

def framerule : RuleTac := RuleTac.ofTacticSyntax fun δ => do
  match ← δ.goal.getType with
  | .forallE _ (.app (.const ``Sodium [levelZero]) (.const ``Universal.Destruct [])) body _ =>
    unless ← Meta.isLevelDefEq levelZero levelOne do Meta.throwIsDefEqStuck
    CryptoM.toMetaM (ctx := .ofString "external") fun τ : Sodium Universal.Destruct => do
      let writer : Typewriter τ Tactic := ⟨default, fun next stx => try evalExact stx; catch _ => next stx⟩
      let (witness, _) ← runTacticMAsMetaM (Typewriter.print writer) δ.mvars.toArray.toList
      match Parser.runParserCategory (← getEnv) `tactic witness "external" with
      | .ok stx => return ⟨← `(tactic|intro _; $(⟨stx⟩))⟩
      | .error err => throwErrorAt (← delab body) err
  | _ => throwPostpone

def mkFreshGamma (type : Expr := .app (.const ``Universal [levelZero]) (.const ``Universal.Destruct [levelZero])) : MetaM Expr := by
  refine Meta.mkFreshExprMVar (mkForall `«τ» .implicit ?_ type)
  exact .app (.const ``Sodium [levelZero]) (.const ``Universal.Destruct [levelZero])

def runRuleOnce (rule : RuleTac := framerule) (deps : Array MVarId := #[]) : MetaM (Array MVarId) := do
  have : Ord MVarId := ⟨fun α β => α.name.quickCmp β.name⟩
  let γ ← mkFreshGamma
  let τ : Expr := .app (.const ``Sodium [levelZero]) (.const ``Universal.Destruct [levelZero])
  let stx ← Meta.mkAppOptM ``Sodium.Crypto.Verified #[mkConst ``Syntax.Tactic, none]
  let fwd : Expr := by
    refine .forallE `«z» stx ?_ .default
    refine .forallE `«o» (.const ``Observable [levelZero]) ?_ .default
    refine .app (.app (.const ``Eq [levelZero]) ?_) ?_
    refine .app (.const ``Observable.Shape.pull [levelZero]) ?_
    refine .app (.const ``Observable.Shape.push [levelZero]) ?_
    repeat exact .bvar default
  let input := {
    goal := γ.mvarId!
    mvars := (UnorderedArraySet.ofArray deps).insert γ.mvarId!
    indexMatchLocations := default
    patternSubsts? := default
    options := {generateScript := true, forwardMaxDepth? := none}
    hypTypes := (∅ : PHashSet _)
      |>.insert ⟨τ, pinfHash τ⟩
      |>.insert ⟨fwd, pinfHash fwd⟩
      |>.insert ⟨stx, pinfHash stx⟩
  }
  let (out, _) ← BaseM.run (rule input)
  match out.applications[0]? with
  | some app => app.postState.restore; return app.goals.map (·.mvarId)
  | _ => throwPostpone

def runRuleForever (rule : RuleTac := framerule) : MetaM Unit := do
  let mut mvars : Array MVarId := #[]
  repeat try mvars ← runRuleOnce rule mvars catch
  | ex@(.internal id ..) =>
    if id == Meta.isDefEqStuckExceptionId then
      IO.FS.Stream.writeLspNotification (← IO.getStdout) {
        method := "$/exception/stuck"
        param := json% null
      }
    unless id == postponeExceptionId do throw ex
  | .error stx msg =>
    IO.FS.Stream.writeLspNotification (← IO.getStdout) {
      method := "$/exception"
      param := json% [$(toString stx.prettyPrint), $(← msg.toString)]
    }
