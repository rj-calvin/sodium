import Sodium.Ethos.Weight
import Sodium.FFI.Basic

open Lean Sodium

namespace Ethos

/--
Analysis requires finite field arithmetic on Ed25519. Bindings for these have not yet been written.

Defined for pedagogical completeness.
-/
def Prob {σ} {τ : Sodium σ} (x : Weight) := {x : SecretVector τ (x.quantize .global) // x.isZero}

notation "Δ% " x => @Prob _ _ x
notation "δ% " x => Σ' τ : Sodium (PLift (@default Prop _)), @Prob (PLift (@default Prop _)) τ x

def toWeight {σ} {τ : Sodium σ} (_ : @Prob _ τ x) : Weight := x

#check δ% Δ(0 | 1)
#check Δ% Δ(1 | 3)

end Ethos
