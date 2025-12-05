import Sodium.Typography.Emulator

open Lean Elab Tactic

variable {σ}

namespace Typography

def Latin : PFunctor where
  A := Shape
  B | shape% 'a' | shape% 'A'
    | shape% 'b' | shape% 'B'
    | shape% 'c' | shape% 'C'
    | shape% 'd' | shape% 'D'
    | shape% 'e' | shape% 'E'
    | shape% 'f' | shape% 'F'
    | shape% 'g' | shape% 'G'
    | shape% 'h' | shape% 'H'
    | shape% 'i' | shape% 'I'
    | shape% 'j' | shape% 'J'
    | shape% 'k' | shape% 'K'
    | shape% 'l' | shape% 'L'
    | shape% 'm' | shape% 'M'
    | shape% 'n' | shape% 'N'
    | shape% 'o' | shape% 'O'
    | shape% 'p' | shape% 'P'
    | shape% 'q' | shape% 'Q'
    | shape% 'r' | shape% 'R'
    | shape% 's' | shape% 'S'
    | shape% 't' | shape% 'T'
    | shape% 'u' | shape% 'U'
    | shape% 'v' | shape% 'V'
    | shape% 'w' | shape% 'W'
    | shape% 'x' | shape% 'X'
    | shape% 'y' | shape% 'Y'
    | shape% 'z' | shape% 'Z' => PUnit
    | _ => PEmpty

@[simp] theorem latin_idx : Latin.A = Shape := rfl

@[simp] theorem latin_idx_alpha : Latin.B (shape% 'a') = PUnit := rfl
@[simp] theorem latin_idx_beta : Latin.B (shape% 'b') = PUnit := rfl
@[simp] theorem latin_idx_gamma : Latin.B (shape% 'c') = PUnit := rfl
@[simp] theorem latin_idx_delta : Latin.B (shape% 'd') = PUnit := rfl
@[simp] theorem latin_idx_epsilon : Latin.B (shape% 'e') = PUnit := rfl
@[simp] theorem latin_idx_zeta : Latin.B (shape% 'f') = PUnit := rfl
@[simp] theorem latin_idx_eta : Latin.B (shape% 'g') = PUnit := rfl
@[simp] theorem latin_idx_theta : Latin.B (shape% 'h') = PUnit := rfl
@[simp] theorem latin_idx_iota : Latin.B (shape% 'i') = PUnit := rfl
@[simp] theorem latin_idx_kappa : Latin.B (shape% 'j') = PUnit := rfl
@[simp] theorem latin_idx_lambda : Latin.B (shape% 'k') = PUnit := rfl
@[simp] theorem latin_idx_mu : Latin.B (shape% 'l') = PUnit := rfl
@[simp] theorem latin_idx_nu : Latin.B (shape% 'm') = PUnit := rfl
@[simp] theorem latin_idx_xi : Latin.B (shape% 'n') = PUnit := rfl
@[simp] theorem latin_idx_omicron : Latin.B (shape% 'o') = PUnit := rfl
@[simp] theorem latin_idx_pi : Latin.B (shape% 'p') = PUnit := rfl
@[simp] theorem latin_idx_rho : Latin.B (shape% 'q') = PUnit := rfl
@[simp] theorem latin_idx_sigma : Latin.B (shape% 'r') = PUnit := rfl
@[simp] theorem latin_idx_tau : Latin.B (shape% 's') = PUnit := rfl
@[simp] theorem latin_idx_upsilon : Latin.B (shape% 't') = PUnit := rfl
@[simp] theorem latin_idx_phi : Latin.B (shape% 'u') = PUnit := rfl
@[simp] theorem latin_idx_chi : Latin.B (shape% 'v') = PUnit := rfl
@[simp] theorem latin_idx_psi : Latin.B (shape% 'w') = PUnit := rfl
@[simp] theorem latin_idx_omega : Latin.B (shape% 'x') = PUnit := rfl
@[simp] theorem latin_idx_why : Latin.B (shape% 'y') = PUnit := rfl
@[simp] theorem latin_idx_zed : Latin.B (shape% 'z') = PUnit := rfl

@[simp] theorem latin_idx_Alpha : Latin.B (shape% 'A') = PUnit := rfl
@[simp] theorem latin_idx_Beta : Latin.B (shape% 'B') = PUnit := rfl
@[simp] theorem latin_idx_Gamma : Latin.B (shape% 'C') = PUnit := rfl
@[simp] theorem latin_idx_Delta : Latin.B (shape% 'D') = PUnit := rfl
@[simp] theorem latin_idx_Epsilon : Latin.B (shape% 'E') = PUnit := rfl
@[simp] theorem latin_idx_Zeta : Latin.B (shape% 'F') = PUnit := rfl
@[simp] theorem latin_idx_Eta : Latin.B (shape% 'G') = PUnit := rfl
@[simp] theorem latin_idx_Theta : Latin.B (shape% 'H') = PUnit := rfl
@[simp] theorem latin_idx_Iota : Latin.B (shape% 'I') = PUnit := rfl
@[simp] theorem latin_idx_Kappa : Latin.B (shape% 'J') = PUnit := rfl
@[simp] theorem latin_idx_Lambda : Latin.B (shape% 'K') = PUnit := rfl
@[simp] theorem latin_idx_Mu : Latin.B (shape% 'L') = PUnit := rfl
@[simp] theorem latin_idx_Nu : Latin.B (shape% 'M') = PUnit := rfl
@[simp] theorem latin_idx_Xi : Latin.B (shape% 'N') = PUnit := rfl
@[simp] theorem latin_idx_Omicron : Latin.B (shape% 'O') = PUnit := rfl
@[simp] theorem latin_idx_Pi : Latin.B (shape% 'P') = PUnit := rfl
@[simp] theorem latin_idx_Rho : Latin.B (shape% 'Q') = PUnit := rfl
@[simp] theorem latin_idx_Sigma : Latin.B (shape% 'R') = PUnit := rfl
@[simp] theorem latin_idx_Tau : Latin.B (shape% 'S') = PUnit := rfl
@[simp] theorem latin_idx_Upsilon : Latin.B (shape% 'T') = PUnit := rfl
@[simp] theorem latin_idx_Phi : Latin.B (shape% 'U') = PUnit := rfl
@[simp] theorem latin_idx_Chi : Latin.B (shape% 'V') = PUnit := rfl
@[simp] theorem latin_idx_Psi : Latin.B (shape% 'W') = PUnit := rfl
@[simp] theorem latin_idx_Omega : Latin.B (shape% 'X') = PUnit := rfl
@[simp] theorem latin_idx_Why : Latin.B (shape% 'Y') = PUnit := rfl
@[simp] theorem latin_idx_Zed : Latin.B (shape% 'Z') = PUnit := rfl
@[simp] theorem latin_idx_none : Latin.B (default : Shape) = PEmpty := rfl

private def mkExactULiftChar (c : Char) : Syntax.Tactic :=
  ⟨Syntax.node .none ``Lean.Parser.Tactic.exact #[
    Syntax.atom .none "exact",
    Syntax.node .none ``Lean.Parser.Term.anonymousCtor #[
      Syntax.atom .none "⟨",
      Syntax.node .none `null #[Syntax.mkCharLit c],
      Syntax.atom .none "⟩"
    ]
  ]⟩

protected def a : Syntax.Tactic := mkExactULiftChar 'a'
protected def b : Syntax.Tactic := mkExactULiftChar 'b'
protected def c : Syntax.Tactic := mkExactULiftChar 'c'
protected def d : Syntax.Tactic := mkExactULiftChar 'd'
protected def e : Syntax.Tactic := mkExactULiftChar 'e'
protected def f : Syntax.Tactic := mkExactULiftChar 'f'
protected def g : Syntax.Tactic := mkExactULiftChar 'g'
protected def h : Syntax.Tactic := mkExactULiftChar 'h'
protected def i : Syntax.Tactic := mkExactULiftChar 'i'
protected def j : Syntax.Tactic := mkExactULiftChar 'j'
protected def k : Syntax.Tactic := mkExactULiftChar 'k'
protected def l : Syntax.Tactic := mkExactULiftChar 'l'
protected def m : Syntax.Tactic := mkExactULiftChar 'm'
protected def n : Syntax.Tactic := mkExactULiftChar 'n'
protected def o : Syntax.Tactic := mkExactULiftChar 'o'
protected def p : Syntax.Tactic := mkExactULiftChar 'p'
protected def q : Syntax.Tactic := mkExactULiftChar 'q'
protected def r : Syntax.Tactic := mkExactULiftChar 'r'
protected def s : Syntax.Tactic := mkExactULiftChar 's'
protected def t : Syntax.Tactic := mkExactULiftChar 't'
protected def u : Syntax.Tactic := mkExactULiftChar 'u'
protected def v : Syntax.Tactic := mkExactULiftChar 'v'
protected def w : Syntax.Tactic := mkExactULiftChar 'w'
protected def x : Syntax.Tactic := mkExactULiftChar 'x'
protected def y : Syntax.Tactic := mkExactULiftChar 'y'
protected def z : Syntax.Tactic := mkExactULiftChar 'z'

protected def A : Syntax.Tactic := mkExactULiftChar 'A'
protected def B : Syntax.Tactic := mkExactULiftChar 'B'
protected def C : Syntax.Tactic := mkExactULiftChar 'C'
protected def D : Syntax.Tactic := mkExactULiftChar 'D'
protected def E : Syntax.Tactic := mkExactULiftChar 'E'
protected def F : Syntax.Tactic := mkExactULiftChar 'F'
protected def G : Syntax.Tactic := mkExactULiftChar 'G'
protected def H : Syntax.Tactic := mkExactULiftChar 'H'
protected def I : Syntax.Tactic := mkExactULiftChar 'I'
protected def J : Syntax.Tactic := mkExactULiftChar 'J'
protected def K : Syntax.Tactic := mkExactULiftChar 'K'
protected def L : Syntax.Tactic := mkExactULiftChar 'L'
protected def M : Syntax.Tactic := mkExactULiftChar 'M'
protected def N : Syntax.Tactic := mkExactULiftChar 'N'
protected def O : Syntax.Tactic := mkExactULiftChar 'O'
protected def P : Syntax.Tactic := mkExactULiftChar 'P'
protected def Q : Syntax.Tactic := mkExactULiftChar 'Q'
protected def R : Syntax.Tactic := mkExactULiftChar 'R'
protected def S : Syntax.Tactic := mkExactULiftChar 'S'
protected def T : Syntax.Tactic := mkExactULiftChar 'T'
protected def U : Syntax.Tactic := mkExactULiftChar 'U'
protected def V : Syntax.Tactic := mkExactULiftChar 'V'
protected def W : Syntax.Tactic := mkExactULiftChar 'W'
protected def X : Syntax.Tactic := mkExactULiftChar 'X'
protected def Y : Syntax.Tactic := mkExactULiftChar 'Y'
protected def Z : Syntax.Tactic := mkExactULiftChar 'Z'

namespace Latin

syntax "latin% " term ", " char ", " term : term

elab "latin% " τ:term ", " γ:char ", " stx:term : tactic => do
  let x := mkIdent `«γ»
  let δ := mkIdent `«δ»
  evalTactic <| ← `(tactic|refine ⟨⟨stage% $τ, $γ, fun _ => shape% $γ⟩, fun $x => ?_⟩)
  evalTactic <| ← `(tactic|obtain ⟨$x, _⟩ := $x)
  evalTactic <| ← `(tactic|exact do
    let $δ ← Meta.mkFreshExprMVar (mkApp (mkConst ``ULift [levelZero]) (mkConst ``Char));
    let _ ← Aesop.runTacticMAsTermElabM $(δ).mvarId! ($x $stx);
    return shape% $γ)

variable {τ : Sodium σ}

protected def a : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'a', Typography.a
protected def b : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'b', Typography.b
protected def c : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'c', Typography.c
protected def d : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'd', Typography.d
protected def e : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'e', Typography.e
protected def f : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'f', Typography.f
protected def g : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'g', Typography.g
protected def h : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'h', Typography.h
protected def i : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'i', Typography.i
protected def j : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'j', Typography.j
protected def k : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'k', Typography.k
protected def l : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'l', Typography.l
protected def m : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'm', Typography.m
protected def n : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'n', Typography.n
protected def o : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'o', Typography.o
protected def p : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'p', Typography.p
protected def q : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'q', Typography.q
protected def r : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'r', Typography.r
protected def s : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 's', Typography.s
protected def t : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 't', Typography.t
protected def u : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'u', Typography.u
protected def v : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'v', Typography.v
protected def w : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'w', Typography.w
protected def x : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'x', Typography.x
protected def y : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'y', Typography.y
protected def z : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'z', Typography.z

protected def A : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'A', Typography.A
protected def B : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'B', Typography.B
protected def C : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'C', Typography.C
protected def D : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'D', Typography.D
protected def E : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'E', Typography.E
protected def F : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'F', Typography.F
protected def G : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'G', Typography.G
protected def H : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'H', Typography.H
protected def I : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'I', Typography.I
protected def J : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'J', Typography.J
protected def K : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'K', Typography.K
protected def L : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'L', Typography.L
protected def M : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'M', Typography.M
protected def N : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'N', Typography.N
protected def O : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'O', Typography.O
protected def P : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'P', Typography.P
protected def Q : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'Q', Typography.Q
protected def R : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'R', Typography.R
protected def S : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'S', Typography.S
protected def T : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'T', Typography.T
protected def U : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'U', Typography.U
protected def V : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'V', Typography.V
protected def W : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'W', Typography.W
protected def X : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'X', Typography.X
protected def Y : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'Y', Typography.Y
protected def Z : (Emulator σ ⊚ Latin) (TermElabM Shape) := by latin% τ, 'Z', Typography.Z

end Latin

end Typography
