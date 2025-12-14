import Sodium.Ethos.Weight
import Sodium.Crypto.Monad

open Lean Sodium Crypto

namespace Ethos

/--
Defined for pedagogical completeness.
-/
def Prob {σ} {τ : Sodium σ} (x : Weight) := {x : SecretVector τ (x.quantize .global) // x.isZero}

notation "Δ% " x => @Prob _ _ x
notation "δ% " x => Σ' τ : Sodium (PLift (@default Prop _)), @Prob (PLift (@default Prop _)) τ x

#check Δ% Δ(1 | 3)
#check δ% Δ(0 | 1)

end Ethos
