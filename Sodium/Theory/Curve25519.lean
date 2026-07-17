import Sodium.Theory.Ristretto
import Sodium.Data.Curve25519

namespace Sodium.Theory.Curve25519

open Sodium.Theory.Ristretto
  (order enc dec dec_enc_lt order_pos mod_mul_mod_right)

def clamp (x : Nat) : Nat := 2 ^ 254 + 8 * (x % 2 ^ 254 / 8)

theorem clamp_lb (x : Nat) : 2 ^ 254 ≤ clamp x := Nat.le_add_right _ _

theorem clamp_ub (x : Nat) : clamp x < 2 ^ 255 := by
  have h1 : x % 2 ^ 254 < 2 ^ 254 := Nat.mod_lt _ (Nat.two_pow_pos 254)
  have h2 : x % 2 ^ 254 / 8 * 8 ≤ x % 2 ^ 254 := Nat.div_mul_le_self _ _
  unfold clamp
  omega

theorem clamp_mod8 (x : Nat) : clamp x % 8 = 0 := by
  unfold clamp
  omega

theorem clamp_mod_order_pos (x : Nat) : 0 < clamp x % order := by
  rcases Nat.eq_zero_or_pos (clamp x % order) with h | h
  · exfalso
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
    have hlb := clamp_lb x
    have hub := clamp_ub x
    have h8 := clamp_mod8 x
    have horder8 : order % 8 = 5 := by decide
    have hbig : 2 ^ 255 < 8 * order := by decide
    have hk8 : k % 8 = 0 := by
      rw [hk, Nat.mul_mod, horder8] at h8
      omega
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, Nat.mul_zero] at hk
      omega
    · have hk8' : 8 ≤ k := by omega
      have hle : 8 * order ≤ order * k := by
        rw [Nat.mul_comm 8 order]
        exact Nat.mul_le_mul (Nat.le_refl order) hk8'
      omega
  · exact h

section Impl

variable (n p : @& ByteVector 32)

@[implemented_by Sodium.Curve25519.mulBase]
def mulBase := some (enc 32 (clamp (dec n) % order))

@[implemented_by Sodium.Curve25519.mul]
def mul :=
  if dec p < order then
    if clamp (dec n) * dec p % order = 0 then none
    else some (enc 32 (clamp (dec n) * dec p % order))
  else none

end Impl

def spec : DhFunction where
  name := `curve25519.model
  scalarBytes := 32
  pointBytes := 32
  mulBase
  mul

theorem mulBase_eq {n p : ByteVector 32} (h : spec.mulBase n = some p) :
    p = enc 32 (clamp (dec n) % order) := by
  simp only [spec] at h
  exact (Option.some.inj h).symm

theorem spec_lawful (hp : ∀ x y, order ∣ x * y → order ∣ x ∨ order ∣ y) : spec.Lawful where
  mul_comm a b pa pb hpa hpb := by
    obtain rfl := mulBase_eq hpa
    obtain rfl := mulBase_eq hpb
    simp only [spec, mul]
    rw [dec_enc_lt (Nat.mod_lt _ order_pos), dec_enc_lt (Nat.mod_lt _ order_pos),
      if_pos (Nat.mod_lt _ order_pos), if_pos (Nat.mod_lt _ order_pos),
      mod_mul_mod_right, mod_mul_mod_right, Nat.mul_comm (clamp (dec a)) (clamp (dec b))]
  mul_isSome a b pa pb hpa hpb := by
    obtain rfl := mulBase_eq hpa
    obtain rfl := mulBase_eq hpb
    simp only [spec, mul]
    rw [dec_enc_lt (Nat.mod_lt _ order_pos), if_pos (Nat.mod_lt _ order_pos), mod_mul_mod_right]
    have hne : clamp (dec a) * clamp (dec b) % order ≠ 0 := fun h =>
      (hp _ _ (Nat.dvd_of_mod_eq_zero h)).elim
        (fun d => absurd (Nat.mod_eq_zero_of_dvd d)
          (Nat.pos_iff_ne_zero.mp (clamp_mod_order_pos (dec a))))
        (fun d => absurd (Nat.mod_eq_zero_of_dvd d)
          (Nat.pos_iff_ne_zero.mp (clamp_mod_order_pos (dec b))))
    rw [if_neg hne]
    rfl

end Sodium.Theory.Curve25519
