namespace Sodium.LittleEndian

def decList : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decList bs

def encList : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, x => UInt8.ofNat (x % 256) :: encList k (x / 256)

theorem length_encList (k x : Nat) : (encList k x).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [encList, ih]

theorem decList_encList (k x : Nat) : decList (encList k x) = x % 256 ^ k := by
  induction k generalizing x with
  | zero => simp [encList, decList, Nat.mod_one]
  | succ k ih =>
    rw [Nat.pow_succ', Nat.mod_mul]
    simp [encList, decList, ih]

def bytesLE (k x : Nat) : ByteArray := ⟨(encList k x).toArray⟩

theorem bytesLE_size (k x : Nat) : (bytesLE k x).size = k := by
  simp [bytesLE, ByteArray.size, length_encList]

def natLE (b : ByteArray) : Nat := decList b.data.toList

end Sodium.LittleEndian
