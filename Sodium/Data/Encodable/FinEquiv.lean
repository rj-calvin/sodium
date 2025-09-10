import Sodium.Data.Encodable.Pi

open Lean

universe u v w

class FinEquiv (α : Type u) (β : Type v) where
  encodable_alpha : Encodable α
  encodable_beta : Encodable β
  equiv_left : ∀ a, ∃ b, @decode? α _ (@encode β _ b) = some a
  equiv_right : ∀ b, ∃ a, @decode? β _ (@encode α _ a) = some b
