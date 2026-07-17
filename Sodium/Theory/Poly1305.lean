import Sodium.Theory.Basic
import Sodium.Data.LittleEndian

namespace Sodium.Theory

open LittleEndian

/-! ## 32-bit word operations (little-endian), shared by Salsa20 and ChaCha20 -/

def load32 (b : ByteArray) (i : Nat) : UInt32 :=
  b[i]!.toUInt32 ||| (b[i + 1]!.toUInt32 <<< 8) |||
    (b[i + 2]!.toUInt32 <<< 16) ||| (b[i + 3]!.toUInt32 <<< 24)

def store32 (w : UInt32) : List UInt8 :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

def rotl (x n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-! ## Poly1305 -/

def clampMask : Nat := 0x0ffffffc0ffffffc0ffffffc0fffffff

def polyP : Nat := 2 ^ 130 - 5

/-- Poly1305 accumulator: `((Σ blocks) + s) mod 2^128`. -/
def poly1305Acc (key msg : ByteArray) : Nat := Id.run do
  let r := natLE (key.extract 0 16) &&& clampMask
  let s := natLE (key.extract 16 32)
  let mut h : Nat := 0
  for bi in [0:(msg.size + 15) / 16] do
    let stop := min (bi * 16 + 16) msg.size
    h := (h + (natLE (msg.extract (bi * 16) stop) + 2 ^ (8 * (stop - bi * 16)))) * r % polyP
  return (h + s) % 2 ^ 128

/-- Poly1305 one-time MAC over `msg` with 32-byte key `r ‖ s`. -/
def poly1305 (key msg : ByteArray) : ByteArray := bytesLE 16 (poly1305Acc key msg)

theorem poly1305_size (key msg : ByteArray) : (poly1305 key msg).size = 16 :=
  bytesLE_size 16 _

/-! ## XOR of byte arrays and its involution -/

theorem u8_xor_cancel (a b : UInt8) : a ^^^ b ^^^ b = a := by
  simp [UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]

def xorList : List UInt8 → List UInt8 → List UInt8
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, b :: bs => (a ^^^ b) :: xorList as bs

theorem xorList_length : ∀ a b : List UInt8, (xorList a b).length = min a.length b.length
  | [], _ => by simp [xorList]
  | _ :: _, [] => by simp [xorList]
  | a :: as, b :: bs => by
    simp only [xorList, List.length_cons]; rw [xorList_length as bs]; omega

theorem xorList_involution : ∀ m s : List UInt8, m.length ≤ s.length →
    xorList (xorList m s) s = m
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [xorList]
    rw [u8_xor_cancel, xorList_involution as bs (by simp only [List.length_cons] at h; omega)]

def xorBytes (a b : ByteArray) : ByteArray := ⟨(xorList a.data.toList b.data.toList).toArray⟩

theorem xorBytes_size (a b : ByteArray) : (xorBytes a b).size = min a.size b.size := by
  simp only [xorBytes, ByteArray.size, List.size_toArray, xorList_length, Array.length_toList]

theorem xorBytes_involution (m s : ByteArray) (h : m.size ≤ s.size) :
    xorBytes (xorBytes m s) s = m := by
  have hlen : m.data.toList.length ≤ s.data.toList.length := by
    rw [Array.length_toList, Array.length_toList]; exact h
  have e : (xorBytes m s).data.toList = xorList m.data.toList s.data.toList := by
    simp only [xorBytes, List.toList_toArray]
  rw [xorBytes, e, xorList_involution _ _ hlen]

end Sodium.Theory
