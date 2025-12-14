import Sodium.Lean.Syntax

namespace Lean.Meta

instance FVarId.encodable : Encodable FVarId := Encodable.ofEquiv _ {
  push := FVarId.name
  pull := FVarId.mk
}

instance Literal.encodable : Encodable Literal := Encodable.ofEquiv (Nat ⊕ String) {
  push
    | .natVal n => .inl n
    | .strVal s => .inr s
  pull
    | .inl n => .natVal n
    | .inr s => .strVal s
}

namespace DiscrTree.Key

def Shape :=
  Fin 3
  ⊕ Literal
  ⊕ FVarId × Nat
  ⊕ Name × Nat
  ⊕ Name × Nat × Nat

instance Shape.encodable : Encodable Shape := by unfold Shape; infer_instance

def Shape.push : Key → Shape
  | star => .inl 0
  | arrow => .inl 1
  | other => .inl 2
  | lit v => .inr (.inl v)
  | fvar x n => .inr (.inr (.inl ⟨x, n⟩))
  | const x n => .inr (.inr (.inr (.inl ⟨x, n⟩)))
  | proj x n₁ n₂ => .inr (.inr (.inr (.inr ⟨x, n₁, n₂⟩)))

def Shape.pull : Shape → Key
  | .inl 0 => star
  | .inl 1 => arrow
  | .inl 2 => other
  | .inr (.inl v) => lit v
  | .inr (.inr (.inl ⟨x, n⟩)) => fvar x n
  | .inr (.inr (.inr (.inl ⟨x, n⟩))) => const x n
  | .inr (.inr (.inr (.inr ⟨x, n₁, n₂⟩))) => proj x n₁ n₂

instance encodable : Encodable Key :=
  Encodable.ofEquiv _ {
    push := Shape.push
    pull := Shape.pull
  }

end DiscrTree.Key

end Lean.Meta
