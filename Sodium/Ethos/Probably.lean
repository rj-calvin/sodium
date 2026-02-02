import Sodium.Ethos.Basic
import Sodium.Ethos.Possibly

open Lean Elab Sodium Crypto Ethos Ristretto

declare_aesop_rule_sets [«temporal»] (default := false)

namespace Ethos

notation "σ%" => PLift (@default _ Universal.prompt)

class World where
  τ : Sodium σ%

@[inherit_doc Ethos.Field] abbrev Universal.Field [io : World] :=
  Universal <| @Ethos.Field.{1,0} Universal.prompt io.τ Observable

@[inherit_doc Ethos.Lattice] abbrev Universal.Lattice [io : World] :=
  Universal <| @Ethos.Lattice.{0} Universal.prompt io.τ

/-- Round-trip `f` through `unimax`. -/
def Universal.lift {τ : Sodium σ%}
  (f : ∀ ε : Weight, (hε : some (ε.quantize .global) = unimax.toNat) → δ% unimax :
    ε.quantize_relativity.imp fun _ hδ => by rwa [hδ] at hε)
: Universal.Field (io := ⟨τ⟩) := by
  refine ⟨@default _ Universal.prompt.{0}, fun o => ?_⟩
  refine ⟨fun ε h _ => f ε.down h, fun w? => ?_⟩
  unfold Universal.Field Ethos.Field at w?
  simp only [unimax_idx] at w?
  match w? with | _ => exact o (by aesop (add norm unfold Universal.prompt))

/-- info: 'Ethos.Universal.lift' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound] -/
#guard_msgs in
#print axioms Universal.lift

namespace Prob

open FFI.Ristretto

variable [x : Scalar] [io : World]

def mkFreshScalar : CryptoM io.τ (Δ% io.τ, x.toWeight) := do
  let fpt ← scalarRandom (τ := io.τ)
  return ⟨x.toWeight, x.scalar_nat_idx ▸ fpt, rfl⟩

def mkStaleScalar (w : NonReduced) : CryptoM io.τ (Δ% io.τ, x.toWeight) := do
  let some fpt ← scalarReduce (τ := io.τ) w | throwSpecViolation Curve25519 decl_name%
  return ⟨x.toWeight, x.scalar_nat_idx ▸ fpt, rfl⟩

def reduce {α} [Encodable α] (a : α) (name? : Option Name := none) : CryptoM io.τ (Δ% io.τ, x.toWeight) := do
  mkStaleScalar (.ofEncodable a name?)

def base (p : Δ% io.τ, x.toWeight) : Option Reduced :=
  scalarbase (τ := io.τ) <| x.scalar_nat_idx ▸ p.fpt_shape ▸ p.fpt 

def form (p : Δ% io.τ, x.toWeight) : Option Reduced → Option Reduced
| some c => scalarmult (τ := io.τ) (x.scalar_nat_idx ▸ p.fpt_shape ▸ p.fpt) c
| _ => none

def inv (p : Δ% io.τ, x.toWeight) : CryptoM io.τ (Δ% io.τ, x.toWeight) := do
  let fpt := x.scalar_nat_idx ▸ p.fpt_shape ▸ p.fpt
  let some fpt ← scalarInvert (τ := io.τ) fpt | throwSpecViolation Curve25519 decl_name%
  have : io.τ.SecretVector (Weight.quantize p.toPSigma .global) := by rwa [← Prob.fpt_shape, Scalar.scalar_nat_idx]
  return ⟨p.toPSigma, this, p.fpt_shape⟩

def neg (p : Δ% io.τ, x.toWeight) : CryptoM io.τ (Δ% io.τ, x.toWeight) := do
  let fpt := x.scalar_nat_idx ▸ p.fpt_shape ▸ p.fpt
  let some fpt ← scalarNegate (τ := io.τ) fpt | throwSpecViolation Curve25519 decl_name%
  have : io.τ.SecretVector (Weight.quantize p.toPSigma .global) := by rwa [← Prob.fpt_shape, Scalar.scalar_nat_idx]
  return ⟨p.toPSigma, this, p.fpt_shape⟩

def com (p : Δ% io.τ, x.toWeight) : CryptoM io.τ (Δ% io.τ, x.toWeight) := do
  let fpt := x.scalar_nat_idx ▸ p.fpt_shape ▸ p.fpt
  let some fpt ← scalarComplement (τ := io.τ) fpt | throwSpecViolation Curve25519 decl_name%
  have : io.τ.SecretVector (Weight.quantize p.toPSigma .global) := by rwa [← Prob.fpt_shape, Scalar.scalar_nat_idx]
  return ⟨p.toPSigma, this, p.fpt_shape⟩

def mul (p q : Δ% io.τ, x.toWeight) : CryptoM io.τ (Δ% io.τ, x.toWeight) := do
  let fpt := x.scalar_nat_idx ▸ p.fpt_shape ▸ p.fpt
  let fqt := x.scalar_nat_idx ▸ q.fpt_shape ▸ q.fpt
  let some fpt ← scalarMul (τ := io.τ) fpt fqt | throwSpecViolation Curve25519 decl_name%
  have : io.τ.SecretVector (Weight.quantize p.toPSigma .global) := by rwa [← Prob.fpt_shape, Scalar.scalar_nat_idx]
  return ⟨p.toPSigma, this, p.fpt_shape⟩

def add (p q : Δ% io.τ, x.toWeight) : CryptoM io.τ (Δ% io.τ, x.toWeight) := do
  let fpt := x.scalar_nat_idx ▸ p.fpt_shape ▸ p.fpt
  let fqt := x.scalar_nat_idx ▸ q.fpt_shape ▸ q.fpt
  let some fpt ← scalarAdd (τ := io.τ) fpt fqt | throwSpecViolation Curve25519 decl_name%
  have : io.τ.SecretVector (Weight.quantize p.toPSigma .global) := by rwa [← Prob.fpt_shape, Scalar.scalar_nat_idx]
  return ⟨p.toPSigma, this, p.fpt_shape⟩

def sub (p q : Δ% io.τ, x.toWeight) : CryptoM io.τ (Δ% io.τ, x.toWeight) := do
  let fpt := x.scalar_nat_idx ▸ p.fpt_shape ▸ p.fpt
  let fqt := x.scalar_nat_idx ▸ q.fpt_shape ▸ q.fpt
  let some fpt ← scalarSub (τ := io.τ) fpt fqt | throwSpecViolation Curve25519 decl_name%
  have : io.τ.SecretVector (Weight.quantize p.toPSigma .global) := by rwa [← Prob.fpt_shape, Scalar.scalar_nat_idx]
  return ⟨p.toPSigma, this, p.fpt_shape⟩

end Prob

@[reducible] def Poly : PFunctor where
  A := NonReduced ⊕ PhaseAngle
  B | .inl _ => PEmpty
    | .inr .up | .inr .down | .inr .bot => PUnit
    | .inr .left | .inr .right | .inr .top => Bool

namespace Poly

instance : Inhabited Poly.A := by unfold Poly; infer_instance
instance : Encodable Poly.A := by unfold Poly; infer_instance
instance : DecidableEq Poly.A := by unfold Poly; infer_instance

instance : ∀ a, Encodable (Poly.B a) := fun a => by
  have : Encodable Empty := Empty.encodable
  have : Encodable.{0} PEmpty := Encodable.ofEquiv Empty {push | x => PEmpty.elim x, pull | x => Empty.elim x}
  unfold Poly
  cases a
  . infer_instance
  . rename_i val
    cases val
    repeat infer_instance

instance : Encodable Poly.Id := by infer_instance
instance : Encodable (List Poly.Id) := by infer_instance

abbrev arity : Poly.A → Nat
| .inl _ => 0
| .inr .up | .inr .down | .inr .bot => 1
| .inr .left | .inr .right | .inr .top => 2

def root (a : NonReduced) : Poly.W := ⟨.inl a, PEmpty.elim⟩
def reduce {α} [Encodable α] (a : α) (name? : Option Name := none) := root (.ofEncodable a name?)

instance : Zero Poly.W := ⟨root default⟩
instance : One Poly.W := ⟨root (.succ default)⟩
instance : Inhabited Poly.W := ⟨1⟩

instance {n} : OfNat Poly.W n where
  ofNat := if n = 0 then 0 else if n = 1 then 1 else root (.ofNat n)

def com (w : Poly.W) : Poly.W := ⟨.inr .bot, fun _ => w⟩
def inv (w : Poly.W) : Poly.W := ⟨.inr .up, fun _ => w⟩
def neg (w : Poly.W) : Poly.W := ⟨.inr .down, fun _ => w⟩
def mul (w₁ w₂ : Poly.W) : Poly.W := ⟨.inr .left, fun | false => w₁ | true => w₂⟩
def add (w₁ w₂ : Poly.W) : Poly.W := ⟨.inr .right, fun | false => w₁ | true => w₂⟩
def sub (w₁ w₂ : Poly.W) : Poly.W := ⟨.inr .top, fun | false => w₁ | true => w₂⟩

instance : Complement Poly.W := ⟨com⟩
instance : Inv Poly.W := ⟨inv⟩
instance : Neg Poly.W := ⟨neg⟩
instance : Mul Poly.W := ⟨mul⟩
instance : Add Poly.W := ⟨add⟩
instance : Sub Poly.W := ⟨sub⟩

protected partial def mk [x : Scalar] [io : World] : Poly.W → CryptoM io.τ (Δ% io.τ, x.toWeight) := aux
where aux : Poly.W → CryptoM io.τ (Δ% io.τ, x.toWeight) := PFunctor.W.cases fun
| ⟨.inl c, _⟩ => Prob.mkStaleScalar c
| ⟨.inr .bot, k⟩ => do
  let α ← aux <| k ()
  α.com
| ⟨.inr .up, k⟩ => do
  let α ← aux <| k ()
  α.inv
| ⟨.inr .down, k⟩ => do
  let α ← aux <| k ()
  α.neg
| ⟨.inr .left, k⟩ => do
  let α ← aux <| k false
  let β ← aux <| k true
  α.mul β
| ⟨.inr .right, k⟩ => do
  let α ← aux <| k false
  let β ← aux <| k true
  α.add β
| ⟨.inr .top, k⟩ => do
  let α ← aux <| k false
  let β ← aux <| k true
  α.sub β

protected abbrev corec : Poly.W → Poly.M := PFunctor.M.corec (·.next)

elab "root% " n:num : term => do
  Term.elabTermEnsuringType n (← Meta.mkAppM ``PFunctor.W #[mkConst ``Poly])

end Poly

@[reducible] def Point : PFunctor where
  A := Poly.W × Reduced ⊕ Bool
  B | .inl _ => PEmpty
    | .inr _ => Bool

namespace Point

instance : Inhabited Point.A := ⟨.inl (default, default)⟩

def arity : Point.A → Nat
| .inl _ => 0
| .inr _ => 2

def add (w₁ w₂ : Point.W) : Point.W := ⟨.inr false, fun | false => w₁ | true => w₂⟩
def sub (w₁ w₂ : Point.W) : Point.W := ⟨.inr true, fun | false => w₁ | true => w₂⟩

def smul (α : Poly.W) : Option Reduced → Point.W
| some p => ⟨.inl ⟨α, p⟩, PEmpty.elim⟩
| _ => ⟨.inl ⟨α, default⟩, PEmpty.elim⟩

instance : Add Point.W := ⟨add⟩
instance : Sub Point.W := ⟨sub⟩
instance : HSMul Poly.W (Option Reduced) Point.W := ⟨smul⟩

instance : Zero Point.W := ⟨⟨default, PEmpty.elim⟩⟩
instance : Inhabited Point.W := ⟨0⟩

open FFI.Ristretto in
protected partial def mk [io : World] (x : Point.W) : CryptoM io.τ Ristretto := do
  let y ← aux x
  return y.bind fun z => if h : isValidPoint z then some ⟨z, h⟩ else none
where aux : Point.W → CryptoM io.τ (Option Reduced) := PFunctor.W.cases fun
| ⟨.inl ⟨α, b⟩, _⟩ =>
  if isValidPoint b then return (← Poly.mk α).form b
  else pure none
| ⟨.inr false, k⟩ => do
  let some p ← aux <| k false | return none
  let some q ← aux <| k true | return none
  return pointAdd p q
| ⟨.inr true, k⟩ => do
  let some p ← aux <| k false | return none
  let some q ← aux <| k true | return none
  return pointSub p q

protected abbrev corec : Point.W → Point.M := PFunctor.M.corec (·.next)

macro "idx " n:ident " : " config:Aesop.tactic_clause+ : tactic => do
  let o ← `(term| bind `(tactic| aesop $config*) fun x => bind (Observable.new x) Prob.reduce)
  `(tactic| refine bind $o fun $n => ?_)

macro "idx? " n:ident " : " config:Aesop.tactic_clause+ : tactic => do
  let o ← `(term| bind `(tactic| aesop? $config*) fun x => bind (Observable.new x) Prob.reduce)
  `(tactic| refine bind $o fun $n => ?_)

macro "point " p:term : tactic => `(tactic| refine' Point.mk $p)
macro "corec " p:term : tactic => `(tactic| refine' (pure ∘ Point.corec) $p)

macro "poly " e:term ", " p:term : tactic => `(tactic| refine (show Poly.W from $p) • $(e).base)
macro "form " e:term ", " x:term ", " p:term : tactic => `(tactic| refine (show Poly.W from $p) • $(e).form $x)

example [io : World] : CryptoM io.τ Point.M := by
  idx α : (rule_sets := [«standard», «cautious»])
  idx β : (rule_sets := [«standard», «cautious», «external»])
  idx γ : (rule_sets := [«standard», «cautious», «external», «temporal»])
  idx δ : (rule_sets := [«standard», «cautious», «external», «temporal»]) (add norm unfold Level.getOffset)
  corec ?_ + ?_ + ?_ - ?_
  poly α, root% 2 + root% 3
  poly β, root% 5
  poly γ, root% 7
  poly δ, root% 8

end Point

end Ethos
