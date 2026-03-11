import Sodium.Data.Encodable

namespace Sodium

inductive Decrypt (α)
  | refused
  | mangled (data : ByteArray)
  | unknown (string : String)
  | almost (json : Lean.Json)
  | accepted (a : α)

namespace Decrypt

inductive Error
  | refused
  | invalidEncoding (data : ByteArray)
  | invalidString (string : String)
  | invalidJson (json : Lean.Json)
  deriving TypeName, Hashable, Inhabited

variable {α}

@[coe]
def toExcept : Decrypt α → Except Error α
| .refused => .error .refused
| .mangled data => .error (.invalidEncoding data)
| .unknown string => .error (.invalidString string)
| .almost json => .error (.invalidJson json)
| .accepted a => .ok a

@[coe]
def ofExcept : Except Error α → Decrypt α
| .error .refused => .refused
| .ok a => .accepted a
| .error (.invalidEncoding data) => .mangled data
| .error (.invalidString string) => .unknown string
| .error (.invalidJson json) => .almost json

instance : Coe (Decrypt α) (Except Error α) := ⟨toExcept⟩
instance : Coe (Except Error α) (Decrypt α) := ⟨ofExcept⟩

@[simp]
theorem toExcept_inj : ∀ r : Except Error α, toExcept (ofExcept r) = r := by
  intro
  unfold toExcept ofExcept
  split <;> next _ _ h => split at h <;> simp_all

@[simp]
theorem ofExcept_inj : ∀ r : Decrypt α, ofExcept (toExcept r) = r := by
  intro
  unfold ofExcept toExcept
  split <;> next _ _ h => split at h <;> simp_all

@[simp]
theorem toExcept_ok_iff {a : α} : ∀ r : Decrypt α, toExcept r = .ok a ↔ r = .accepted a := by
  intro
  unfold toExcept
  constructor
  · intro a
    split at a <;> next _ _ => simp_all
  · intro a
    subst a
    simp_all only

variable (α) [Encodable α]

def ofJson (json : Lean.Json) : Decrypt α :=
  match decode? (α := α) json with
  | .some a => .accepted a
  | _ => .almost json

def ofString (string : String) : Decrypt α :=
  match Lean.Json.parse string with
  | .ok json => ofJson _ json
  | _ => .unknown string

def ofByteArray (data : ByteArray) : Decrypt α :=
  match String.fromUTF8? data with
  | .some string => ofString _ string
  | _ => .mangled data

end Decrypt

end Sodium
