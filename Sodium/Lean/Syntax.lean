import Sodium.Data.Digest
import Sodium.Data.Chunk
import Sodium.Data.Encodable.WType

namespace Lean

namespace Name

def Shape := Unit ⊕ String ⊕ Nat

local notation "anonymous%" => Sum.inl ()
local notation "str% " s => Sum.inr (Sum.inl s)
local notation "num% " n => Sum.inr (Sum.inr n)

def Shape.arity : Shape → Nat
  | anonymous% => 0
  | str% _ => 1
  | num% _ => 1

instance : ∀ s, NeZero (Shape.arity (str% s)) := fun _ => ⟨Nat.one_ne_zero⟩
instance : ∀ n, NeZero (Shape.arity (num% n)) := fun _ => ⟨Nat.one_ne_zero⟩

def Shape.push : Name → WType fun i : Shape => Fin i.arity
  | .anonymous => ⟨anonymous%, Fin.elim0⟩
  | .str k s => ⟨str% s, fun _ => push k⟩
  | .num k n => ⟨num% n, fun _ => push k⟩

def Shape.pull : WType (fun i : Shape => Fin i.arity) → Name
  | ⟨anonymous%, _⟩ => .anonymous
  | ⟨str% s, fn⟩ => .str (pull (fn 0)) s
  | ⟨num% n, fn⟩ => .num (pull (fn 0)) n

instance encodable.equiv : Encodable.Equiv Name (WType (fun i : Shape => Fin i.arity)) where
  push := Shape.push
  pull := Shape.pull
  push_pull_eq n := by
    induction n with
    | anonymous => simp only [Shape.push, Shape.pull]
    | str k s ih => simp only [Shape.push, Shape.pull, ih]
    | num k n ih => simp only [Shape.push, Shape.pull, ih]

instance encodable : Encodable Name :=
  have : Encodable Shape := by unfold Shape; infer_instance
  Encodable.ofEquiv _ encodable.equiv

end Name

instance SyntaxNodeKind.encodable : Encodable SyntaxNodeKind :=
  inferInstanceAs (Encodable Name)

namespace SourceInfo

def Shape :=
  Unit
  ⊕ Substring × String.Pos × Substring × String.Pos
  ⊕ String.Pos × String.Pos × Bool

instance encodable : Encodable SourceInfo :=
  have : Encodable Shape := by unfold Shape; infer_instance
  have : Encodable.Equiv SourceInfo Shape := {
    push
      | .none => .inl ()
      | .original leading pos trailing endPos => .inr (.inl (leading, pos, trailing, endPos))
      | .synthetic pos endPos canonical => .inr (.inr (pos, endPos, canonical))
    pull
      | .inl _ => .none
      | .inr (.inl (leading, pos, trailing, endPos)) => .original leading pos trailing endPos
      | .inr (.inr (pos, endPos, canonical)) => .synthetic pos endPos canonical
  }
  Encodable.ofEquiv _ this

end SourceInfo

namespace Syntax.Preresolved

def Shape := Name ⊕ Name × List String

instance encodable : Encodable Syntax.Preresolved :=
  have : Encodable Shape := by unfold Shape; infer_instance
  have : Encodable.Equiv Syntax.Preresolved Shape := {
    push
      | .namespace n => .inl n
      | .decl n fs => .inr (n, fs)
    pull
      | .inl n => .namespace n
      | .inr (n, fs) => .decl n fs
  }
  Encodable.ofEquiv _ this

end Syntax.Preresolved

namespace Syntax

def Shape :=
  Unit
  ⊕ SourceInfo × String
  ⊕ SourceInfo × Substring × Name × List Syntax.Preresolved
  ⊕ SourceInfo × SyntaxNodeKind × Nat

local notation "missing%" => Sum.inl ()
local notation "atom% " info ", " s => Sum.inr (Sum.inl ⟨info, s⟩)
local notation "ident% " info ", " s ", " n ", " pre => Sum.inr (Sum.inr (Sum.inl (info, s, n, pre)))
local notation "node% " info ", " kind ", " k => Sum.inr (Sum.inr (Sum.inr (info, kind, k)))

def Shape.arity : Shape → Nat
  | missing% | atom% _, _ | ident% _, _, _, _ => 0
  | node% _, _, k => k

def Shape.push : Syntax → WType fun i : Shape => Fin i.arity
  | .missing => ⟨missing%, Fin.elim0⟩
  | .atom info s => ⟨atom% info, s, Fin.elim0⟩
  | .ident info s n pre => ⟨ident% info, s, n, pre, Fin.elim0⟩
  | .node info kind stx =>
    if _ : stx.size = 0 then ⟨node% info, kind, 0, Fin.elim0⟩
    else ⟨node% info, kind, stx.size, fun i => Shape.push (stx[i]'i.isLt)⟩
decreasing_by
  simp_all only [Syntax.node.sizeOf_spec, gt_iff_lt]
  have h₁ : sizeOf stx < 1 + sizeOf info + sizeOf stx := by omega
  have h₂ : sizeOf (stx[i]'i.isLt) < sizeOf stx := by
    simp_all only [Nat.lt_add_left_iff_pos, Fin.getElem_fin, Array.sizeOf_getElem]
  omega

def Shape.pull : WType (fun i : Shape => Fin i.arity) → Syntax
  | ⟨missing%, _⟩ => .missing
  | ⟨atom% info, s, _⟩ => .atom info s
  | ⟨ident% info, s, n, pre, _⟩ => .ident info s n pre
  | ⟨node% info, kind, k, fn⟩ => .node info kind <| (Array.ofFn (n := k) id).map fun i => Shape.pull (fn i)

instance encodable.equiv : Encodable.Equiv Syntax (WType fun i : Shape => Fin i.arity) where
  push := Shape.push
  pull := Shape.pull
  push_pull_eq stx := by
    have : ∀ n (s : Syntax), sizeOf s < n → Shape.pull (Shape.push s) = s := fun n => by
      induction n with
      | zero => intros; omega
      | succ n ih =>
        intro s hs
        cases s <;> try simp only [Shape.push, Shape.pull]
        rename_i args
        if h : args.size = 0 then
          simp only [h, Array.eq_empty_of_size_eq_zero, List.size_toArray, List.length_nil, Shape.push,
            ↓reduceDIte, Shape.pull, Array.ofFn_zero, List.map_toArray, List.map_nil]
        else
          rw [dif_neg h, Shape.pull]
          congr
          ext i
          . simp only [Array.size_map, Array.size_ofFn]
          . rename_i h
            simp only [Array.getElem_map, Array.getElem_ofFn, id_eq]
            have : sizeOf args[i] < n := by
              simp only [Syntax.node.sizeOf_spec] at hs
              have : sizeOf args[i] < sizeOf args := Array.sizeOf_getElem _ i h
              omega
            exact ih args[i] this
    exact this (sizeOf stx + 1) stx (Nat.lt_succ_self _)

instance encodable : Encodable Syntax :=
  have : Encodable Shape := by unfold Shape; infer_instance
  Encodable.ofEquiv _ encodable.equiv

end Syntax

namespace TSyntax

instance encodable {kind : SyntaxNodeKind} : Encodable (TSyntax kind) :=
  let f (stx : TSyntax kind) : Json := Json.mkObj [(kind.toString, encode stx.raw)]
  let finv (json : Json) : Option (TSyntax kind) :=
    match json.getObjVal? kind.toString with
    | .error _ => none
    | .ok json =>
      match decode? json with
      | none => none
      | some a => some ⟨a⟩
  Encodable.ofLeftInj f finv fun _ => by simp only [Json.mkObj_getObjVal?_eq_ok, Encodable.encodek, f, finv]

def encodable.syntax (kind : SyntaxNodeKind) : TSyntax ``Lean.Parser.Tactic.tacticSeq :=
  Unhygienic.run `(tacticSeq|
    let f (stx : TSyntax $(Syntax.mkNameLit kind.toString)) : Json := Json.mkObj [($(Syntax.mkStrLit kind.toString), encode stx.raw)];
    let finv (json : Json) : Option (TSyntax $(Syntax.mkNameLit kind.toString)) :=
      match json.getObjVal? $(Syntax.mkStrLit kind.toString) with
      | .error _ => none
      | .ok json =>
        match decode? (α := Syntax) json with
        | none => none
        | some a => some ⟨a⟩;
    exact Encodable.ofLeftInj f finv fun _ => by simp [f, finv])

instance : ToChunks (TSyntax ``Lean.Parser.Tactic.tacticSeq) where
  toChunks tacticSeq :=
    match tacticSeq with
    | `(tacticSeq| $tacs*) => tacs.getElems.map encode |>.toList
    | _ => []

instance : FromChunks (TSyntax ``Lean.Parser.Tactic.tacticSeq) where
  fromChunks? xs := do
    let seq ← xs.mapM (@decode? Syntax _)
    let args := seq.foldl (init := #[]) fun acc stx =>
      if acc.isEmpty then acc.push stx
      else acc.push .missing |>.push stx
    let node := .node .none ``Lean.Parser.Tactic.tacticSeq #[.node .none ``Lean.Parser.Tactic.tacticSeq1Indented args]
    return ⟨node⟩

end TSyntax

/- #eval show MetaM Format from do -/
/-   let stx := TSyntax.encodable_syntax `tactic -/
/-   println! encode stx -/
/-   println! decode? (α := TSyntax ``Lean.Parser.Tactic.tacticSeq) (encode stx) -/
/-   return stx.raw.prettyPrint -/

end Lean
