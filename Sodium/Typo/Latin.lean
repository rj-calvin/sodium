import Sodium.Typo.Emulator

open Lean Elab Tactic

variable {σ}

namespace Typo

protected def Latin.Shape : PFunctor where
  A := Shape
  B | shape% ' ' => ULift Unit
    | shape% 'a' | shape% 'A'
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

instance : Inhabited Latin.Shape.A := ⟨Escape⟩

abbrev Latin (σ) := Emulator σ ⊚ Latin.Shape

@[simp] theorem latin_idx : Latin.Shape.A = Shape := rfl

@[simp] theorem latin_idx_space : Latin.Shape.B (shape% ' ') = ULift Unit := rfl

@[simp] theorem latin_idx_alpha : Latin.Shape.B (shape% 'a') = PUnit := rfl
@[simp] theorem latin_idx_beta : Latin.Shape.B (shape% 'b') = PUnit := rfl
@[simp] theorem latin_idx_gamma : Latin.Shape.B (shape% 'c') = PUnit := rfl
@[simp] theorem latin_idx_delta : Latin.Shape.B (shape% 'd') = PUnit := rfl
@[simp] theorem latin_idx_epsilon : Latin.Shape.B (shape% 'e') = PUnit := rfl
@[simp] theorem latin_idx_zeta : Latin.Shape.B (shape% 'f') = PUnit := rfl
@[simp] theorem latin_idx_eta : Latin.Shape.B (shape% 'g') = PUnit := rfl
@[simp] theorem latin_idx_theta : Latin.Shape.B (shape% 'h') = PUnit := rfl
@[simp] theorem latin_idx_iota : Latin.Shape.B (shape% 'i') = PUnit := rfl
@[simp] theorem latin_idx_kappa : Latin.Shape.B (shape% 'j') = PUnit := rfl
@[simp] theorem latin_idx_lambda : Latin.Shape.B (shape% 'k') = PUnit := rfl
@[simp] theorem latin_idx_mu : Latin.Shape.B (shape% 'l') = PUnit := rfl
@[simp] theorem latin_idx_nu : Latin.Shape.B (shape% 'm') = PUnit := rfl
@[simp] theorem latin_idx_xi : Latin.Shape.B (shape% 'n') = PUnit := rfl
@[simp] theorem latin_idx_omicron : Latin.Shape.B (shape% 'o') = PUnit := rfl
@[simp] theorem latin_idx_pi : Latin.Shape.B (shape% 'p') = PUnit := rfl
@[simp] theorem latin_idx_rho : Latin.Shape.B (shape% 'q') = PUnit := rfl
@[simp] theorem latin_idx_sigma : Latin.Shape.B (shape% 'r') = PUnit := rfl
@[simp] theorem latin_idx_tau : Latin.Shape.B (shape% 's') = PUnit := rfl
@[simp] theorem latin_idx_upsilon : Latin.Shape.B (shape% 't') = PUnit := rfl
@[simp] theorem latin_idx_phi : Latin.Shape.B (shape% 'u') = PUnit := rfl
@[simp] theorem latin_idx_chi : Latin.Shape.B (shape% 'v') = PUnit := rfl
@[simp] theorem latin_idx_psi : Latin.Shape.B (shape% 'w') = PUnit := rfl
@[simp] theorem latin_idx_omega : Latin.Shape.B (shape% 'x') = PUnit := rfl
@[simp] theorem latin_idx_why : Latin.Shape.B (shape% 'y') = PUnit := rfl
@[simp] theorem latin_idx_zed : Latin.Shape.B (shape% 'z') = PUnit := rfl

@[simp] theorem latin_idx_Alpha : Latin.Shape.B (shape% 'A') = PUnit := rfl
@[simp] theorem latin_idx_Beta : Latin.Shape.B (shape% 'B') = PUnit := rfl
@[simp] theorem latin_idx_Gamma : Latin.Shape.B (shape% 'C') = PUnit := rfl
@[simp] theorem latin_idx_Delta : Latin.Shape.B (shape% 'D') = PUnit := rfl
@[simp] theorem latin_idx_Epsilon : Latin.Shape.B (shape% 'E') = PUnit := rfl
@[simp] theorem latin_idx_Zeta : Latin.Shape.B (shape% 'F') = PUnit := rfl
@[simp] theorem latin_idx_Eta : Latin.Shape.B (shape% 'G') = PUnit := rfl
@[simp] theorem latin_idx_Theta : Latin.Shape.B (shape% 'H') = PUnit := rfl
@[simp] theorem latin_idx_Iota : Latin.Shape.B (shape% 'I') = PUnit := rfl
@[simp] theorem latin_idx_Kappa : Latin.Shape.B (shape% 'J') = PUnit := rfl
@[simp] theorem latin_idx_Lambda : Latin.Shape.B (shape% 'K') = PUnit := rfl
@[simp] theorem latin_idx_Mu : Latin.Shape.B (shape% 'L') = PUnit := rfl
@[simp] theorem latin_idx_Nu : Latin.Shape.B (shape% 'M') = PUnit := rfl
@[simp] theorem latin_idx_Xi : Latin.Shape.B (shape% 'N') = PUnit := rfl
@[simp] theorem latin_idx_Omicron : Latin.Shape.B (shape% 'O') = PUnit := rfl
@[simp] theorem latin_idx_Pi : Latin.Shape.B (shape% 'P') = PUnit := rfl
@[simp] theorem latin_idx_Rho : Latin.Shape.B (shape% 'Q') = PUnit := rfl
@[simp] theorem latin_idx_Sigma : Latin.Shape.B (shape% 'R') = PUnit := rfl
@[simp] theorem latin_idx_Tau : Latin.Shape.B (shape% 'S') = PUnit := rfl
@[simp] theorem latin_idx_Upsilon : Latin.Shape.B (shape% 'T') = PUnit := rfl
@[simp] theorem latin_idx_Phi : Latin.Shape.B (shape% 'U') = PUnit := rfl
@[simp] theorem latin_idx_Chi : Latin.Shape.B (shape% 'V') = PUnit := rfl
@[simp] theorem latin_idx_Psi : Latin.Shape.B (shape% 'W') = PUnit := rfl
@[simp] theorem latin_idx_Omega : Latin.Shape.B (shape% 'X') = PUnit := rfl
@[simp] theorem latin_idx_Why : Latin.Shape.B (shape% 'Y') = PUnit := rfl
@[simp] theorem latin_idx_Zed : Latin.Shape.B (shape% 'Z') = PUnit := rfl

@[simp] theorem latin_idx_none : Latin.Shape.B (default : Shape) = PEmpty := rfl

namespace Latin.Syntax

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

end Syntax

syntax "latin% " term ", " char ", " term : term

elab "latin% " τ:term ", " γ:char ", " stx:term : tactic => do
  let x := mkIdent `«x»
  evalTactic <| ← `(tactic|refine ⟨⟨commit% $τ, $γ, $stx, fun _ => shape% $γ⟩, fun $x => ?_⟩)
  evalTactic <| ← `(tactic|obtain ⟨$x, _⟩ := $x)
  evalTactic <| ← `(tactic|exact $x)

variable {τ : Sodium σ}

protected def a : (Latin σ) (TermElabM Shape) := by latin% τ, 'a', Syntax.a
protected def b : (Latin σ) (TermElabM Shape) := by latin% τ, 'b', Syntax.b
protected def c : (Latin σ) (TermElabM Shape) := by latin% τ, 'c', Syntax.c
protected def d : (Latin σ) (TermElabM Shape) := by latin% τ, 'd', Syntax.d
protected def e : (Latin σ) (TermElabM Shape) := by latin% τ, 'e', Syntax.e
protected def f : (Latin σ) (TermElabM Shape) := by latin% τ, 'f', Syntax.f
protected def g : (Latin σ) (TermElabM Shape) := by latin% τ, 'g', Syntax.g
protected def h : (Latin σ) (TermElabM Shape) := by latin% τ, 'h', Syntax.h
protected def i : (Latin σ) (TermElabM Shape) := by latin% τ, 'i', Syntax.i
protected def j : (Latin σ) (TermElabM Shape) := by latin% τ, 'j', Syntax.j
protected def k : (Latin σ) (TermElabM Shape) := by latin% τ, 'k', Syntax.k
protected def l : (Latin σ) (TermElabM Shape) := by latin% τ, 'l', Syntax.l
protected def m : (Latin σ) (TermElabM Shape) := by latin% τ, 'm', Syntax.m
protected def n : (Latin σ) (TermElabM Shape) := by latin% τ, 'n', Syntax.n
protected def o : (Latin σ) (TermElabM Shape) := by latin% τ, 'o', Syntax.o
protected def p : (Latin σ) (TermElabM Shape) := by latin% τ, 'p', Syntax.p
protected def q : (Latin σ) (TermElabM Shape) := by latin% τ, 'q', Syntax.q
protected def r : (Latin σ) (TermElabM Shape) := by latin% τ, 'r', Syntax.r
protected def s : (Latin σ) (TermElabM Shape) := by latin% τ, 's', Syntax.s
protected def t : (Latin σ) (TermElabM Shape) := by latin% τ, 't', Syntax.t
protected def u : (Latin σ) (TermElabM Shape) := by latin% τ, 'u', Syntax.u
protected def v : (Latin σ) (TermElabM Shape) := by latin% τ, 'v', Syntax.v
protected def w : (Latin σ) (TermElabM Shape) := by latin% τ, 'w', Syntax.w
protected def x : (Latin σ) (TermElabM Shape) := by latin% τ, 'x', Syntax.x
protected def y : (Latin σ) (TermElabM Shape) := by latin% τ, 'y', Syntax.y
protected def z : (Latin σ) (TermElabM Shape) := by latin% τ, 'z', Syntax.z

protected def A : (Latin σ) (TermElabM Shape) := by latin% τ, 'A', Syntax.A
protected def B : (Latin σ) (TermElabM Shape) := by latin% τ, 'B', Syntax.B
protected def C : (Latin σ) (TermElabM Shape) := by latin% τ, 'C', Syntax.C
protected def D : (Latin σ) (TermElabM Shape) := by latin% τ, 'D', Syntax.D
protected def E : (Latin σ) (TermElabM Shape) := by latin% τ, 'E', Syntax.E
protected def F : (Latin σ) (TermElabM Shape) := by latin% τ, 'F', Syntax.F
protected def G : (Latin σ) (TermElabM Shape) := by latin% τ, 'G', Syntax.G
protected def H : (Latin σ) (TermElabM Shape) := by latin% τ, 'H', Syntax.H
protected def I : (Latin σ) (TermElabM Shape) := by latin% τ, 'I', Syntax.I
protected def J : (Latin σ) (TermElabM Shape) := by latin% τ, 'J', Syntax.J
protected def K : (Latin σ) (TermElabM Shape) := by latin% τ, 'K', Syntax.K
protected def L : (Latin σ) (TermElabM Shape) := by latin% τ, 'L', Syntax.L
protected def M : (Latin σ) (TermElabM Shape) := by latin% τ, 'M', Syntax.M
protected def N : (Latin σ) (TermElabM Shape) := by latin% τ, 'N', Syntax.N
protected def O : (Latin σ) (TermElabM Shape) := by latin% τ, 'O', Syntax.O
protected def P : (Latin σ) (TermElabM Shape) := by latin% τ, 'P', Syntax.P
protected def Q : (Latin σ) (TermElabM Shape) := by latin% τ, 'Q', Syntax.Q
protected def R : (Latin σ) (TermElabM Shape) := by latin% τ, 'R', Syntax.R
protected def S : (Latin σ) (TermElabM Shape) := by latin% τ, 'S', Syntax.S
protected def T : (Latin σ) (TermElabM Shape) := by latin% τ, 'T', Syntax.T
protected def U : (Latin σ) (TermElabM Shape) := by latin% τ, 'U', Syntax.U
protected def V : (Latin σ) (TermElabM Shape) := by latin% τ, 'V', Syntax.V
protected def W : (Latin σ) (TermElabM Shape) := by latin% τ, 'W', Syntax.W
protected def X : (Latin σ) (TermElabM Shape) := by latin% τ, 'X', Syntax.X
protected def Y : (Latin σ) (TermElabM Shape) := by latin% τ, 'Y', Syntax.Y
protected def Z : (Latin σ) (TermElabM Shape) := by latin% τ, 'Z', Syntax.Z

@[aesop norm unfold (rule_sets := [«standard»])]
protected def map {α β} := @PFunctor.map α β (Latin σ)

open Sodium Crypto Ethos in
def quantize (γ : (Latin σ) (TermElabM Shape)) (scope : ScopeName) : (Latin σ) (CryptoM τ Observable) := by
  refine Latin.map (fun γ => ?_) γ
  exact do let γ ← Aesop.runTermElabMAsCoreM γ; γ.quantize scope

def write (s : String) : Latin.Shape.W := Id.run do
  let mut w : Latin.Shape.W := ⟨Escape, PEmpty.elim⟩
  for c in s.toList.reverse do w := ⟨shape% c, fun _ => w⟩
  return w

end Latin

end Typo
