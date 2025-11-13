import Aesop
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

namespace DiscrTree

namespace Key

def Shape :=
  Fin 3
  ⊕ Literal
  ⊕ FVarId × Nat
  ⊕ Name × Nat
  ⊕ Name × Nat × Nat

instance Shape.encodable : Encodable Shape := by unfold Shape; infer_instance

def toShape : Key → Shape
  | star => .inl 0
  | arrow => .inl 1
  | other => .inl 2
  | lit v => .inr (.inl v)
  | fvar x n => .inr (.inr (.inl ⟨x, n⟩))
  | const x n => .inr (.inr (.inr (.inl ⟨x, n⟩)))
  | proj x n₁ n₂ => .inr (.inr (.inr (.inr ⟨x, n₁, n₂⟩)))

def ofShape : Shape → Key
  | .inl 0 => star
  | .inl 1 => arrow
  | .inl 2 => other
  | .inr (.inl v) => lit v
  | .inr (.inr (.inl ⟨x, n⟩)) => fvar x n
  | .inr (.inr (.inr (.inl ⟨x, n⟩))) => const x n
  | .inr (.inr (.inr (.inr ⟨x, n₁, n₂⟩))) => proj x n₁ n₂

instance encodable : Encodable Key :=
  Encodable.ofEquiv _ {
    push := toShape
    pull := ofShape
  }

end Key

namespace Trie

variable {α} [Encodable α]

def Shape := Json × Array Json

instance : Encodable Shape := by unfold Shape; infer_instance

def Shape.arity : Shape → Nat
  | ⟨_, ks⟩ => ks.size

def Shape.push : Trie α → WType fun i : Shape => Fin i.arity
  | .node ns nk => by
    refine ⟨⟨encode ns, nk.map fun ⟨n, _⟩ => encode n⟩, fun i => ?_⟩
    simp [arity] at i
    cases h : nk.size with
    | zero =>
      rw [h] at i
      exact Fin.elim0 i
    | succ n =>
      let k := nk[i].2
      exact Shape.push k
decreasing_by
  sorry

def Shape.pull : WType (fun i : Shape => Fin i.arity) → Option (Trie α)
  | ⟨⟨x, #[]⟩, _⟩ => do
    let ns ← decode? (α := Array α) x
    return .node ns #[]
  | ⟨⟨x, ks⟩, f⟩ => do
    let ns ← decode? (α := Array α) x
    let nk ← Array.mapM id <| Array.ofFn (n := ks.size) id |>.map fun i => do
      let k ← decode? (α := Key) (ks[i]'i.isLt)
      let n ← Shape.pull (f i)
      return ⟨k, n⟩
    return .node ns nk

instance encodable : Encodable (Trie α) :=
  Encodable.ofLeftInj Shape.push Shape.pull fun x => by
    sorry

end Trie

end DiscrTree

end Lean.Meta
