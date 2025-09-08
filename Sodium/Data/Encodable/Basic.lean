import Aesop
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
theorem arr_getArrVal?_0_eq_ok : (Json.arr #[α, β]).getArrVal? 0 = .ok α := by
  unfold Json.getArrVal?
  rfl

@[simp]
theorem arr_getArrVal?_1_eq_ok : (Json.arr #[α, β]).getArrVal? 1 = .ok β := by
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

instance {α : Type u} [ToJson α] [FromJson α] [h : LawfulJson α] : Encodable α where
  encode := toJson
  decode? x := fromJson? x |>.toOption
  encodek := by
    intro a
    obtain ⟨jsonk⟩ := h
    specialize jsonk a
    simp_all only
    rfl

instance {α : Type u} [Encodable α] : ToJson α := ⟨encode⟩

instance {α : Type u} [TypeName α] [Encodable α] : FromJson α where
  fromJson? json := decode? (α := α) json |>.getDM (throw (TypeName.typeName α).toString)

private instance {α : Type u} [Encodable α] : FromJson α :=
  ⟨fun json => decode? (α := α) json |>.getDM (throw default)⟩

instance {α : Type u} [Encodable α] : LawfulJson α where
  jsonk _ := by
    simp [fromJson?, toJson]
    rfl

namespace Encodable

open Encodable (encodek)

variable {α : Type u} {β : Type v} [Encodable α]

def withErrorMsg (msg : String) (inst : Encodable β) : FromJson β where
  fromJson? json := decode? (α := β) json |>.getDM (throw msg)

@[simp]
theorem decode?_encode_eq : decode? ∘ encode (α := α) = some := by
  funext x
  simp only [Function.comp_apply, encodek]

theorem encode_inj : ∀ ⦃a b : α⦄, encode a = encode b → a = b
  | x, y, h => Option.some.inj (by rw [← encodek, h, encodek])

@[simp]
theorem encode_eq_iff {a b : α} : encode a = encode b ↔ a = b :=
  ⟨by exact @encode_inj _ _ _ _, congrArg encode⟩

def ofLeftInj (f : β → α) (g : α → Option β) (h : ∀ x, g (f x) = some x) : Encodable β :=
  ⟨fun b => encode (f b), fun json => (decode? json).bind g, by simp [encodek, h]⟩

def ofEquiv (f : β → α) (g : α → β) (h : ∀ x, g (f x) = x) : Encodable β :=
  ⟨fun b => encode (f b), fun json => (decode? json).map g, by simp [encodek, h]⟩

def _root_.Empty.encodable : Encodable Empty :=
  ⟨Empty.elim, fun _ => none, fun x => Empty.elim x⟩

instance _root_.Json.instEncodable : Encodable Json where
  encode := id
  decode? := pure
  encodek _ := by rfl

instance _root_.Nat.instEncodable : Encodable Nat where
  encode n := json% $n
  decode? json := json.getNat?.toOption
  encodek _ := by rfl

instance _root_.String.instEncodable : Encodable String where
  encode s := json% $s
  decode? json := json.getStr?.toOption
  encodek _ := by rfl

instance _root_.Bool.instEncodable : Encodable Bool where
  encode | true => json% true | false => json% false
  decode? json := fromJson? (α := Bool) json |>.toOption
  encodek _ := by split <;> rfl

instance _root_.Unit.instEncodable : Encodable Unit where
  encode _ := json% null
  decode? | json% null => some () | _ => none
  encodek _ := by rfl

instance _root_.Array.instEncodable : Encodable (Array α) where
  encode xs := Json.arr (xs.map encode)
  decode?
    | .arr xs => xs.mapM decode?
    | _ => none
  encodek _ := by
    simp [Array.mapM_map]
    have : some (α := α) = fun x => pure (id x) := by rfl
    rw [this, Array.mapM_pure]
    simp only [Array.map_id_fun, id_eq, Option.pure_def]

instance _root_.Fin.instEncodable {n : Nat} : Encodable (Fin n) where
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
  ofEquiv (α := Empty) Fin.elim0 Empty.elim (by exact fun x => Fin.elim0 x)

instance _root_.UInt8.instEncodable : Encodable UInt8 :=
  ofEquiv UInt8.toFin UInt8.ofFin (by exact fun _ => rfl)

instance _root_.UInt16.instEncodable : Encodable UInt16 :=
  ofEquiv UInt16.toFin UInt16.ofFin (by exact fun _ => rfl)

instance _root_.UInt32.instEncodable : Encodable UInt32 :=
  ofEquiv UInt32.toFin UInt32.ofFin (by exact fun _ => rfl)

instance _root_.UInt64.instEncodable : Encodable UInt64 :=
  ofEquiv UInt64.toFin UInt64.ofFin (by exact fun _ => rfl)

private def _root_.ByteArray.encodeImpl : ByteArray → Json := ByteArray.toJson
private def _root_.ByteArray.decode?Impl : Json → Option ByteArray := Except.toOption ∘ ByteArray.fromJson?

@[implemented_by ByteArray.encodeImpl]
def _root_.ByteArray.encode (bs : ByteArray) : Json := Encodable.encode bs.data

@[implemented_by ByteArray.decode?Impl]
def _root_.ByteArray.decode? (json : Json) : Option ByteArray := do
  let bs ← Encodable.decode? (α := Array UInt8) json
  return ⟨bs⟩

instance _root_.ByteArray.instEncodable : Encodable ByteArray where
  encode := ByteArray.encode
  decode? := ByteArray.decode?
  encodek _ := by
    unfold ByteArray.decode? ByteArray.encode
    simp only [encodek, Option.pure_def, Option.bind_eq_bind, Option.bind_some]

instance _root_.Option.instEncodable : Encodable (Option α) where
  encode
    | none => json% null
    | some x => json% { some: $(encode x) }
  decode?
    | json% null => some none
    | json =>
      match json.getObjVal? "some" with
      | .error _ => none
      | .ok json =>
        match decode? (α := α) json with
        | none => none
        | some a => some (some a)
  encodek o := by
    cases o with
    | some a =>
      simp
      split
      . contradiction
      . simp_all only [imp_false]
        split
        . contradiction
        . rename_i json heq
          simp [toJson] at heq
          subst heq
          simp only [encodek]
    | none => rfl

instance _root_.Sum.instEncodable [Encodable β] : Encodable (α ⊕ β) where
  encode
    | .inl a => json% { inl: $a }
    | .inr b => json% { inr: $b }
  decode? json :=
    match json.getObjVal? "inl" with
    | .ok json => decode? (α := α) json |>.map .inl
    | .error _ =>
      match json.getObjVal? "inr" with
      | .ok json => decode? (α := β) json |>.map .inr
      | .error _ => none
  encodek a := by
    cases a with
    | inl _ =>
      simp_all only [Json.mkObj_getObjVal?_eq_ok, Option.map_eq_some_iff, Sum.inl.injEq, exists_eq_right]
      simp only [toJson, encodek]
    | inr _ =>
      simp_all only [Json.mkObj_getObjVal?_eq_ok]
      split
      . simp_all only [Option.map_eq_some_iff, reduceCtorEq, and_false, exists_false]
        contradiction
      . simp_all only [Option.map_eq_some_iff, Sum.inr.injEq, exists_eq_right]
        simp only [toJson, encodek]

instance _root_.Prod.instEncodable [Encodable β] : Encodable (α × β) where
  encode x := json% [$(x.1), $(x.2)]
  decode? json :=
    match json.getArrVal? 0, json.getArrVal? 1 with
    | .ok fst, .ok snd =>
      (decode? (α := α) fst).bind fun a => (decode? (α := β) snd).bind fun b => some (a, b)
    | _, _ => none
  encodek a := by
    obtain ⟨fst, snd⟩ := a
    simp only [toJson, Json.arr_getArrVal?_0_eq_ok, Json.arr_getArrVal?_1_eq_ok, encodek,
      Option.bind_some]

instance _root_.String.Pos.instEncodable : Encodable String.Pos :=
  ofEquiv (α := Nat) String.Pos.byteIdx String.Pos.mk (by exact fun _ => rfl)

instance _root_.Substring.instEncodable : Encodable Substring :=
  ofEquiv (α := String × String.Pos × String.Pos)
    (fun x => ⟨x.str, x.startPos, x.stopPos⟩)
    (fun x => ⟨x.1, x.2.1, x.2.2⟩)
    (by exact fun _ => rfl)

section Sigma

variable {γ : α → Type v} [∀ a, Encodable (γ a)]

instance _root_.Sigma.instEncodable : Encodable (Sigma γ) where
  encode x := json% [$(x.1), $(x.2)]
  decode? json :=
    match json.getArrVal? 0, json.getArrVal? 1 with
    | .ok fst, .ok snd =>
      (decode? (α := α) fst).bind fun a => (decode? (α := γ a) snd).bind fun b => some ⟨a, b⟩
    | _, _ => none
  encodek a := by
    obtain ⟨fst, snd⟩ := a
    simp only [toJson, Json.arr_getArrVal?_0_eq_ok, Json.arr_getArrVal?_1_eq_ok, encodek,
      Option.bind_some]

end Sigma

section Subtype

variable {P : α → Prop} [DecidablePred P]

instance _root_.Subtype.instEncodable : Encodable {a : α // P a} where
  encode x := encode x.1
  decode? json := (decode? (α := α) json).bind fun a => if h : P a then some ⟨a, h⟩ else none
  encodek x := by
    obtain ⟨_, h⟩ := x
    simp only [encodek, Option.bind_some, Option.dite_none_right_eq_some, exists_prop, and_true]
    exact h

end Subtype

end Encodable
