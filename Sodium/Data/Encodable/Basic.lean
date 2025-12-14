import Sodium.Data.ByteArray

open Lean

universe u v

namespace RBNode

variable {α : Type u} [Ord α] [Std.ReflOrd α] {β : Type v}

@[simp]
theorem insert_find_eq_some : ∀ (k : α) (v : β), RBNode.find compare (RBNode.insert compare RBNode.leaf k v) k = some v := by
  intro k v
  unfold RBNode.insert RBNode.ins
  split
  . contradiction
  . unfold RBNode.find
    have : compare k k = .eq := by exact Std.compare_self
    split <;> rename_i h
    . rw [this] at h
      contradiction
    . rw [this] at h
      contradiction
    . rfl

end RBNode

namespace String

instance instReflOrd : Std.ReflOrd String where
  compare_self := by
    intro s
    unfold compare instOrdString compareOfLessAndEq
    simp only [String.lt_irrefl, ↓reduceIte]

end String

namespace Json

variable {α β : Json}

@[simp]
theorem num_getNat?_eq_ok : ∀ n, (Json.num (JsonNumber.fromNat n)).getNat? = .ok n := by
  intro n
  unfold Json.getNat? JsonNumber.fromNat
  split
  . rename_i m h
    simp_all only [Int.ofNat_eq_coe, Json.num.injEq, JsonNumber.mk.injEq, and_true]
    rw [← Int.mem_toNat?] at h
    unfold Int.toNat? at h
    simp at h
    subst h
    rfl
  . rfl

@[simp]
theorem mkObj_getObjVal?_eq_ok : ∀ s, (Json.mkObj [(s, α)]).getObjVal? s = .ok α := by
  intro s
  unfold Json.mkObj Json.getObjVal?
  simp only [Id.run, bind_pure_comp, map_pure, List.forIn_pure_yield_eq_foldl, List.foldl_cons,
    List.foldl_nil, pure_bind, RBNode.insert_find_eq_some]
  rfl

@[simp]
theorem arr_getArrVal?_zero_eq_ok : (Json.arr #[α, β]).getArrVal? 0 = .ok α := by
  unfold Json.getArrVal?
  rfl

@[simp]
theorem arr_getArrVal?_one_eq_ok : (Json.arr #[α, β]).getArrVal? 1 = .ok β := by
  unfold Json.getArrVal?
  rfl

end Json

class Encodable (α : Type u) where
  encode : α → Json
  decode? : Json → Option α
  encodek : ∀ a, decode? (encode a) = some a

export Encodable (encode decode?)

attribute [simp] Encodable.encodek

class LawfulJson (α : Type u) [ToJson α] [FromJson α] where
  jsonk : ∀ a, fromJson? (α := α) (toJson a) = .ok a

attribute [simp] LawfulJson.jsonk

instance {α : Type u} [ToJson α] [FromJson α] [h : LawfulJson α] : Encodable α where
  encode := toJson
  decode? x := fromJson? x |>.toOption
  encodek := by
    intro a
    obtain ⟨jsonk⟩ := h
    specialize jsonk a
    simp_all only
    rfl

namespace Encodable

open Encodable (encodek)

variable {α : Type u} {β : Type v} [Encodable α]

def withJson (inst : Encodable β) : ToJson β where
  toJson := encode

def withErrorMsg (msg : String) (inst : Encodable β) : FromJson β where
  fromJson? json := decode? (α := β) json |>.getDM (throw msg)

@[simp]
theorem decode?_encode_eq : decode? ∘ encode (α := α) = some := by
  funext
  simp only [Function.comp_apply, encodek]

theorem encode_inj : ∀ ⦃a b : α⦄, encode a = encode b → a = b
  | x, y, h => Option.some.inj (by rw [← encodek, h, encodek])

@[simp]
theorem encode_eq_iff {a b : α} : encode a = encode b ↔ a = b :=
  ⟨by exact @encode_inj _ _ _ _, congrArg encode⟩

@[simp]
def ofLeftInj (f : β → α) (g : α → Option β) (h : ∀ x, g (f x) = some x) : Encodable β :=
  ⟨fun b => encode (f b), fun json => (decode? json).bind g, by simp [encodek, h]⟩

class Equiv (α : Type u) (β : Type v) where
  push : α → β
  pull : β → α
  push_pull_eq : ∀ a, pull (push a) = a := by
    intro n
    first
      | rfl
      | ext <;> rfl
      | induction n <;> rfl

@[simp]
def ofEquiv (α) [Encodable α] (h : Equiv β α) : Encodable β :=
  ⟨fun b => encode (h.push b), fun json => (decode? json).map h.pull, by simp; exact h.push_pull_eq⟩

def _root_.Empty.encodable : Encodable Empty :=
  ⟨Empty.elim, fun _ => none, fun x => Empty.elim x⟩

instance _root_.Json.encodable : Encodable Json where
  encode := id
  decode? := pure
  encodek _ := by rfl

instance _root_.Nat.encodable : Encodable Nat where
  encode n := json% $n
  decode? json := json.getNat?.toOption
  encodek _ := by rfl

instance _root_.String.encodable : Encodable String where
  encode s := json% $s
  decode? json := json.getStr?.toOption
  encodek _ := by rfl

instance _root_.Bool.encodable : Encodable Bool where
  encode | true => json% true | false => json% false
  decode? json := fromJson? (α := Bool) json |>.toOption
  encodek _ := by split <;> rfl

instance _root_.Unit.encodable : Encodable Unit where
  encode _ := json% null
  decode? | json% null => some () | _ => none
  encodek _ := by rfl

instance _root_.Array.encodable : Encodable (Array α) where
  encode xs := Json.arr (xs.map encode)
  decode?
    | .arr xs => xs.mapM decode?
    | _ => none
  encodek _ := by
    simp [Array.mapM_map]
    have : some (α := α) = fun x => pure (id x) := by rfl
    rw [this, Array.mapM_pure]
    simp only [Array.map_id_fun, id_eq, Option.pure_def]

instance _root_.List.encodable : Encodable (List α) :=
  have : Equiv (List α) (Array α) := {push := (·.toArray), pull := (·.toList)}
  ofEquiv _ this

instance _root_.Fin.encodable {n : Nat} : Encodable (Fin n) where
  encode x := json% $x.toNat
  decode? json := do
    let m ← json.getNat?.toOption
    if h : m < n then some ⟨m, h⟩ else none
  encodek _ := by
    unfold Except.toOption
    simp only [toJson, Fin.toNat_eq_val, Json.num_getNat?_eq_ok, Option.bind_eq_bind,
      Option.bind_some, Fin.is_lt, ↓reduceDIte, Fin.eta]

def _root_.Fin.encodable0 : Encodable (Fin 0) :=
  have : Encodable Empty := by exact Empty.encodable
  have : Equiv (Fin 0) Empty := {
    push := Fin.elim0
    pull := Empty.elim
    push_pull_eq x := by exact Fin.elim0 x
  }
  ofEquiv _ this

instance _root_.UInt8.encodable : Encodable UInt8 :=
  ofEquiv _ {push := UInt8.toFin, pull := UInt8.ofFin}

instance _root_.UInt16.encodable : Encodable UInt16 :=
  ofEquiv _ {push := UInt16.toFin, pull := UInt16.ofFin}

instance _root_.UInt32.encodable : Encodable UInt32 :=
  ofEquiv _ {push := UInt32.toFin, pull := UInt32.ofFin}

instance _root_.UInt64.encodable : Encodable UInt64 :=
  ofEquiv _ {push := UInt64.toFin, pull := UInt64.ofFin}

private def _root_.ByteArray.encodeImpl : ByteArray → Json := ByteArray.toJson
private def _root_.ByteArray.decode?Impl : Json → Option ByteArray := Except.toOption ∘ ByteArray.fromJson?

@[implemented_by ByteArray.encodeImpl]
def _root_.ByteArray.encode (bs : ByteArray) : Json := Encodable.encode bs.data

@[implemented_by ByteArray.decode?Impl]
def _root_.ByteArray.decode? (json : Json) : Option ByteArray := do
  let bs ← Encodable.decode? (α := Array UInt8) json
  return ⟨bs⟩

instance _root_.ByteArray.encodable : Encodable ByteArray where
  encode := ByteArray.encode
  decode? := ByteArray.decode?
  encodek _ := by
    unfold ByteArray.decode? ByteArray.encode
    simp only [encodek, Option.pure_def, Option.bind_eq_bind, Option.bind_some]

instance _root_.Option.encodable : Encodable (Option α) where
  encode
    | none => json% null
    | some x => json% { "@": $(encode x) }
  decode?
    | json% null => some none
    | json =>
      match json.getObjVal? "@" with
      | .error _ => none
      | .ok json =>
        match decode? (α := α) json with
        | none => none
        | some a => some (some a)
  encodek o := by
    cases o with
    | none => rfl
    | some a =>
      split
      . contradiction
      . simp_all only [imp_false]
        split
        . contradiction
        . rename_i json heq
          simp [toJson] at heq
          subst heq
          simp only [encodek]

instance _root_.Sum.encodable [Encodable β] : Encodable (α ⊕ β) where
  encode
    | .inl a => json% { "0": $(encode a) }
    | .inr b => json% { "1": $(encode b) }
  decode? json :=
    match json.getObjVal? "0" with
    | .ok json => decode? (α := α) json |>.map .inl
    | .error _ =>
      match json.getObjVal? "1" with
      | .ok json => decode? (α := β) json |>.map .inr
      | .error _ => none
  encodek a := by
    cases a with
    | inl _ =>
      simp_all only [Json.mkObj_getObjVal?_eq_ok, Option.map_eq_some_iff, Sum.inl.injEq, exists_eq_right]
      simp only [toJson, id_eq, encodek]
    | inr _ =>
      simp_all only [Json.mkObj_getObjVal?_eq_ok]
      split
      . simp_all only [Option.map_eq_some_iff, reduceCtorEq, and_false, exists_false]
        contradiction
      . simp_all only [Option.map_eq_some_iff, Sum.inr.injEq, exists_eq_right]
        simp only [toJson, id_eq, encodek]

instance _root_.Prod.encodable [Encodable β] : Encodable (α × β) where
  encode x := json% [$(encode x.1), $(encode x.2)]
  decode? json :=
    match json.getArrVal? 0, json.getArrVal? 1 with
    | .ok fst, .ok snd =>
      (decode? (α := α) fst).bind fun a => (decode? (α := β) snd).bind fun b => some (a, b)
    | _, _ => none
  encodek a := by
    obtain ⟨fst, snd⟩ := a
    simp only [toJson, Json.arr_getArrVal?_zero_eq_ok, Json.arr_getArrVal?_one_eq_ok, encodek,
      Option.bind_some, id_eq]

instance _root_.Except.encodable [Encodable β] : Encodable (Except α β) :=
  ofEquiv (α ⊕ β) {
    push
      | .ok b => .inr b
      | .error a => .inl a
    pull
      | .inr b => .ok b
      | .inl a => .error a
  }

instance _root_.String.Pos.encodable : Encodable String.Pos :=
  ofEquiv _ {push := String.Pos.byteIdx, pull := String.Pos.mk}

instance _root_.Substring.encodable : Encodable Substring :=
  ofEquiv (String × String.Pos × String.Pos) {
    push x := ⟨x.str, x.startPos, x.stopPos⟩
    pull x := ⟨x.1, x.2.1, x.2.2⟩
  }

section Sigma

variable {γ : α → Type v} [∀ a, Encodable (γ a)]

instance _root_.Sigma.encodable : Encodable (Σ a, γ a) where
  encode x := json% [$(encode x.1), $(encode x.2)]
  decode? json :=
    match json.getArrVal? 0, json.getArrVal? 1 with
    | .ok fst, .ok snd =>
      (decode? (α := α) fst).bind fun a => (decode? (α := γ a) snd).bind fun b => some ⟨a, b⟩
    | _, _ => none
  encodek a := by
    obtain ⟨fst, snd⟩ := a
    simp only [toJson, Json.arr_getArrVal?_zero_eq_ok, Json.arr_getArrVal?_one_eq_ok, encodek,
      Option.bind_some, id_eq]

end Sigma

section PSigma

variable {γ : α → Type v} [∀ a, Encodable (γ a)]

instance _root_.PSigma.encodable : Encodable (Σ' a, γ a) where
  encode x := json% [$(encode x.1), $(encode x.2)]
  decode? json :=
    match json.getArrVal? 0, json.getArrVal? 1 with
    | .ok fst, .ok snd =>
      (decode? (α := α) fst).bind fun a => (decode? (α := γ a) snd).bind fun b => some ⟨a, b⟩
    | _, _ => none
  encodek a := by
    obtain ⟨fst, snd⟩ := a
    simp only [toJson, Json.arr_getArrVal?_zero_eq_ok, Json.arr_getArrVal?_one_eq_ok, encodek,
      Option.bind_some, id_eq]

end PSigma

section Subtype

variable {P : α → Prop} [DecidablePred P]

instance _root_.Subtype.encodable : Encodable {a : α // P a} where
  encode x := encode x.1
  decode? json := (decode? (α := α) json).bind fun a => if h : P a then some ⟨a, h⟩ else none
  encodek x := by
    obtain ⟨_, h⟩ := x
    simp only [encodek, Option.bind_some, Option.dite_none_right_eq_some, exists_prop, and_true]
    exact h

end Subtype

instance _root_.Char.encodable : Encodable Char :=
  Encodable.ofEquiv {x : UInt32 // x.isValidChar} {
    push | ⟨x, h⟩ => ⟨x, h⟩
    pull | ⟨x, h⟩ => ⟨x, h⟩
  }

end Encodable
