import Sodium.Data.Encodable.WType

namespace Lean

namespace Name

private def Shape := Unit ⊕ String ⊕ Nat

local notation "anonymous%" => Sum.inl ()
local notation "str% " s => Sum.inr (Sum.inl s)
local notation "num% " n => Sum.inr (Sum.inr n)

private def Shape.arity : Shape → Nat
  | anonymous% => 0
  | str% _ => 1
  | num% _ => 1

local instance : ∀ s, NeZero (Shape.arity (str% s)) := fun _ => ⟨Nat.one_ne_zero⟩
local instance : ∀ n, NeZero (Shape.arity (num% n)) := fun _ => ⟨Nat.one_ne_zero⟩

private def f : Name → WType fun i : Shape => Fin i.arity
  | .anonymous => ⟨anonymous%, Fin.elim0⟩
  | .str k s => ⟨str% s, fun _ => f k⟩
  | .num k n => ⟨num% n, fun _ => f k⟩

private def finv : WType (fun i : Shape => Fin i.arity) → Name
  | ⟨anonymous%, _⟩ => .anonymous
  | ⟨str% s, fn⟩ => .str (finv (fn 0)) s
  | ⟨num% n, fn⟩ => .num (finv (fn 0)) n

instance instEncodable : Encodable Name :=
  haveI : Encodable Shape := by unfold Shape; infer_instance
  Encodable.ofEquiv f finv fun n => by
    induction n with
    | anonymous => simp only [f, finv]
    | str k s ih => simp only [f, finv, ih]
    | num k n ih => simp only [f, finv, ih]

end Name

instance SyntaxNodeKind.instEncodable : Encodable SyntaxNodeKind :=
  inferInstanceAs (Encodable Name)

namespace SourceInfo

private def Shape :=
  Unit
  ⊕ Substring × String.Pos × Substring × String.Pos
  ⊕ String.Pos × String.Pos × Bool

instance instEncodable : Encodable SourceInfo :=
  haveI : Encodable Shape := by unfold Shape; infer_instance
  let f : SourceInfo → Shape
    | .none => .inl ()
    | .original leading pos trailing endPos => .inr (.inl (leading, pos, trailing, endPos))
    | .synthetic pos endPos canonical => .inr (.inr (pos, endPos, canonical))
  let finv : Shape → SourceInfo
    | .inl _ => .none
    | .inr (.inl (leading, pos, trailing, endPos)) => .original leading pos trailing endPos
    | .inr (.inr (pos, endPos, canonical)) => .synthetic pos endPos canonical
  Encodable.ofEquiv f finv fun n => by induction n <;> rfl

end SourceInfo

namespace Syntax.Preresolved

private def Shape := Name ⊕ Name × List String

instance instEncodable : Encodable Syntax.Preresolved :=
  haveI : Encodable Shape := by unfold Shape; infer_instance
  let f : Syntax.Preresolved → Shape
    | .namespace n => .inl n
    | .decl n fs => .inr (n, fs)
  let finv : Shape → Syntax.Preresolved
    | .inl n => .namespace n
    | .inr (n, fs) => .decl n fs
  Encodable.ofEquiv f finv fun n => by induction n <;> rfl

end Syntax.Preresolved

namespace Syntax

private def Shape :=
  Unit
  ⊕ SourceInfo × String
  ⊕ SourceInfo × Substring × Name × List Syntax.Preresolved
  ⊕ SourceInfo × SyntaxNodeKind × Nat

local notation "missing%" => Sum.inl ()
local notation "atom% " info ", " s => Sum.inr (Sum.inl ⟨info, s⟩)
local notation "ident% " info ", " s ", " n ", " pre => Sum.inr (Sum.inr (Sum.inl (info, s, n, pre)))
local notation "node% " info ", " kind ", " k => Sum.inr (Sum.inr (Sum.inr (info, kind, k)))

private def Shape.arity : Shape → Nat
  | missing% | atom% _, _ | ident% _, _, _, _ => 0
  | node% _, _, k => k

private def f : Syntax → WType fun i : Shape => Fin i.arity
  | .missing => ⟨missing%, Fin.elim0⟩
  | .atom info s => ⟨atom% info, s, Fin.elim0⟩
  | .ident info s n pre => ⟨ident% info, s, n, pre, Fin.elim0⟩
  | .node info kind stx =>
    if _ : stx.size = 0 then ⟨node% info, kind, 0, Fin.elim0⟩
    else ⟨node% info, kind, stx.size, fun i => f (stx[i]'i.isLt)⟩
decreasing_by
  simp_all only [Syntax.node.sizeOf_spec, gt_iff_lt]
  have h₁ : sizeOf stx < 1 + sizeOf info + sizeOf stx := by omega
  have h₂ : sizeOf (stx[i]'i.isLt) < sizeOf stx := by
    simp_all only [Nat.lt_add_left_iff_pos, Fin.getElem_fin, Array.sizeOf_getElem]
  omega

private def finv : WType (fun i : Shape => Fin i.arity) → Syntax
  | ⟨missing%, _⟩ => .missing
  | ⟨atom% info, s, _⟩ => .atom info s
  | ⟨ident% info, s, n, pre, _⟩ => .ident info s n pre
  | ⟨node% info, kind, k, fn⟩ => .node info kind <| (Array.ofFn (n := k) id).map fun i => finv (fn i)

instance instEncodable : Encodable Syntax :=
  haveI : Encodable Shape := by unfold Shape; infer_instance
  Encodable.ofEquiv f finv fun stx => by
    have : ∀ n (s : Syntax), sizeOf s < n → finv (f s) = s := fun n => by
      induction n with
      | zero => intros; omega
      | succ n ih =>
        intro s hs
        cases s <;> try simp only [f, finv]
        rename_i args
        if h : args.size = 0 then
          simp only [h, Array.eq_empty_of_size_eq_zero, List.size_toArray, List.length_nil, f,
            ↓reduceDIte, finv, Array.ofFn_zero, List.map_toArray, List.map_nil]
        else
          rw [dif_neg h, finv]
          congr
          ext i
          . simp only [Array.size_map, Array.size_ofFn]
          . rename_i h₁ h₂
            simp only [Array.getElem_map, Array.getElem_ofFn, id_eq]
            have h_lt : sizeOf args[i] < n := by
              simp only [Syntax.node.sizeOf_spec] at hs
              have : sizeOf args[i] < sizeOf args := Array.sizeOf_getElem _ i h₂
              omega
            exact ih args[i] h_lt
    exact this (sizeOf stx + 1) stx (Nat.lt_succ_self _)

end Syntax

namespace TSyntax

instance instEncodable {kind : SyntaxNodeKind} : Encodable (TSyntax kind) :=
  let f (stx : TSyntax kind) : Json := Json.mkObj [(kind.toString, encode stx.raw)]
  let finv (json : Json) : Option (TSyntax kind) :=
    match json.getObjVal? kind.toString with
    | .error _ => none
    | .ok json =>
      match decode? (α := Syntax) json with
      | none => none
      | some a => some ⟨a⟩
  Encodable.ofLeftInj f finv fun _ => by
    simp only [Json.mkObj_getObjVal?_eq_ok, Encodable.encodek, f, finv]

end TSyntax

#eval show MetaM Unit from do
  let x ← `(tactic| exact?)
  println! encode x
  println! decode? (α := TSyntax `tactic) (encode x)

end Lean
