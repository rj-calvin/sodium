import Sodium.Theory.Basic
import Sodium.Data.Aead

namespace Sodium.Theory.XSalsa20poly1305

/-! ## Little-endian byte codec -/

def decLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decLE bs

def encLE : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, x => UInt8.ofNat (x % 256) :: encLE k (x / 256)

theorem length_encLE (k x : Nat) : (encLE k x).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [encLE, ih]

def bytesLE (k x : Nat) : ByteArray := ⟨(encLE k x).toArray⟩

theorem bytesLE_size (k x : Nat) : (bytesLE k x).size = k := by
  simp [bytesLE, ByteArray.size, length_encLE]

def natLE (b : ByteArray) : Nat := decLE b.data.toList

/-! ## Salsa20 / HSalsa20 core -/

def load32 (b : ByteArray) (i : Nat) : UInt32 :=
  b[i]!.toUInt32 ||| (b[i + 1]!.toUInt32 <<< 8) |||
    (b[i + 2]!.toUInt32 <<< 16) ||| (b[i + 3]!.toUInt32 <<< 24)

def store32 (w : UInt32) : List UInt8 :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

def rotl (x n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-- One Salsa20 double round (column round then row round): 32 ARX steps. -/
def doubleRound (x : Array UInt32) : Array UInt32 :=
  ([ (4,0,12,7),(8,4,0,9),(12,8,4,13),(0,12,8,18),
     (9,5,1,7),(13,9,5,9),(1,13,9,13),(5,1,13,18),
     (14,10,6,7),(2,14,10,9),(6,2,14,13),(10,6,2,18),
     (3,15,11,7),(7,3,15,9),(11,7,3,13),(15,11,7,18),
     (1,0,3,7),(2,1,0,9),(3,2,1,13),(0,3,2,18),
     (6,5,4,7),(7,6,5,9),(4,7,6,13),(5,4,7,18),
     (11,10,9,7),(8,11,10,9),(9,8,11,13),(10,9,8,18),
     (12,15,14,7),(13,12,15,9),(14,13,12,13),(15,14,13,18) ]
    : List (Nat × Nat × Nat × UInt32)).foldl
      (fun x (i, a, b, r) => x.set! i (x[i]! ^^^ rotl (x[a]! + x[b]!) r)) x

def sigma : Array UInt32 := #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

/-- Build the 16-word Salsa20 input matrix from constants, key and 16-byte input block. -/
def salsaState (input key : ByteArray) : Array UInt32 :=
  #[sigma[0]!, load32 key 0, load32 key 4, load32 key 8,
    load32 key 12, sigma[1]!, load32 input 0, load32 input 4,
    load32 input 8, load32 input 12, sigma[2]!, load32 key 16,
    load32 key 20, load32 key 24, load32 key 28, sigma[3]!]

def rounds20 (x : Array UInt32) : Array UInt32 :=
  (List.range 10).foldl (fun x _ => doubleRound x) x

/-- Salsa20 core: 20 rounds with feed-forward, producing a 64-byte block. -/
def salsa20Core (input key : ByteArray) : ByteArray :=
  let j := salsaState input key
  let x := rounds20 j
  ⟨((List.range 16).flatMap fun i => store32 (x[i]! + j[i]!)).toArray⟩

/-- HSalsa20: 20 rounds without feed-forward, extracting words 0,5,10,15,6,7,8,9. -/
def hsalsa20 (input16 key : ByteArray) : ByteArray :=
  let x := rounds20 (salsaState input16 key)
  ⟨([0, 5, 10, 15, 6, 7, 8, 9].flatMap fun i => store32 x[i]!).toArray⟩

/-- `n` consecutive Salsa20 keystream blocks starting at block `counter`. -/
def salsaBlocks (key nonce8 : ByteArray) (counter : Nat) : Nat → ByteArray
  | 0 => .empty
  | n + 1 => salsa20Core (nonce8 ++ bytesLE 8 counter) key ++ salsaBlocks key nonce8 (counter + 1) n

/-- Salsa20 keystream of `len` bytes for a 32-byte key and 8-byte nonce. -/
def salsa20Keystream (key nonce8 : ByteArray) (len : Nat) : ByteArray :=
  (salsaBlocks key nonce8 0 ((len + 63) / 64)).extract 0 len

/-- XSalsa20 keystream: HSalsa20 subkey from nonce[0:16], then Salsa20 with nonce[16:24]. -/
def xsalsaKeystream (key : ByteVector 32) (nonce : ByteVector 24) (len : Nat) : ByteArray :=
  let subkey := hsalsa20 (nonce.toByteArray.extract 0 16) key.toByteArray
  salsa20Keystream subkey (nonce.toByteArray.extract 16 24) len

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

/-! ## XOR and the secretbox construction -/

def xorList : List UInt8 → List UInt8 → List UInt8
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, b :: bs => (a ^^^ b) :: xorList as bs

def xorBytes (a b : ByteArray) : ByteArray := ⟨(xorList a.data.toList b.data.toList).toArray⟩

/-- Seal `msg` under keystream `ks`: Poly1305 tag over the XOR ciphertext, then tag ‖ ciphertext. -/
def boxSeal (ks msg : ByteArray) : ByteArray :=
  let ct := xorBytes msg (ks.extract 32 (32 + msg.size))
  poly1305 (ks.extract 0 32) ct ++ ct

/-- Open ciphertext `c` under keystream `ks`, verifying the Poly1305 tag. -/
def boxOpen (ks c : ByteArray) : Option ByteArray :=
  if 16 ≤ c.size then
    let ct := c.extract 16 c.size
    if c.extract 0 16 = poly1305 (ks.extract 0 32) ct then
      some (xorBytes ct (ks.extract 32 (32 + ct.size)))
    else none
  else none

@[implemented_by Sodium.XSalsa20Poly1305.encrypt]
def encrypt (key : @& ByteVector 32) (nonce : @& ByteVector 24) (_ad msg : @& ByteArray) : ByteArray :=
  boxSeal (xsalsaKeystream key nonce (32 + msg.size)) msg

@[implemented_by Sodium.XSalsa20Poly1305.decrypt?]
def decrypt? (key : @& ByteVector 32) (nonce : @& ByteVector 24) (_ad c : @& ByteArray) :
    Option ByteArray :=
  boxOpen (xsalsaKeystream key nonce (32 + (c.extract 16 c.size).size)) c

/-! ## Size and XOR-involution lemmas -/

theorem u8_xor_cancel (a b : UInt8) : a ^^^ b ^^^ b = a := by
  simp [UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]

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

theorem xorBytes_size (a b : ByteArray) : (xorBytes a b).size = min a.size b.size := by
  simp only [xorBytes, ByteArray.size, List.size_toArray, xorList_length, Array.length_toList]

theorem xorBytes_involution (m s : ByteArray) (h : m.size ≤ s.size) :
    xorBytes (xorBytes m s) s = m := by
  have hlen : m.data.toList.length ≤ s.data.toList.length := by
    rw [Array.length_toList, Array.length_toList]
    exact h
  have e : (xorBytes m s).data.toList = xorList m.data.toList s.data.toList := by
    simp only [xorBytes, List.toList_toArray]
  rw [xorBytes, e, xorList_involution _ _ hlen]

theorem salsa20Core_size (input key : ByteArray) : (salsa20Core input key).size = 64 := by
  simp only [salsa20Core, ByteArray.size, List.size_toArray, List.length_flatMap, store32,
    List.length_cons, List.length_nil]
  decide

theorem salsaBlocks_size (key nonce8 : ByteArray) (counter n : Nat) :
    (salsaBlocks key nonce8 counter n).size = n * 64 := by
  induction n generalizing counter with
  | zero => rfl
  | succ n ih =>
    simp only [salsaBlocks, ByteArray.size_append, salsa20Core_size, ih]
    omega

theorem xsalsaKeystream_size (key : ByteVector 32) (nonce : ByteVector 24) (len : Nat) :
    (xsalsaKeystream key nonce len).size = len := by
  simp only [xsalsaKeystream, salsa20Keystream, ByteArray.size_extract, salsaBlocks_size,
    Nat.sub_zero]
  have h := Nat.div_add_mod (len + 63) 64
  have h2 : (len + 63) % 64 < 64 := Nat.mod_lt _ (by decide)
  omega

/-- The secretbox round trip under a shared keystream: encrypt-then-MAC with a XOR stream
cipher decrypts correctly, because XOR is involutive and the MAC recomputes identically. -/
theorem boxOpen_boxSeal (ks msg : ByteArray) (hks : 32 + msg.size ≤ ks.size) :
    boxOpen ks (boxSeal ks msg) = some msg := by
  have hSs : (ks.extract 32 (32 + msg.size)).size = msg.size := by
    rw [ByteArray.size_extract]; omega
  have hCTs : (xorBytes msg (ks.extract 32 (32 + msg.size))).size = msg.size := by
    rw [xorBytes_size, hSs]; omega
  have hMACs : (poly1305 (ks.extract 0 32)
      (xorBytes msg (ks.extract 32 (32 + msg.size)))).size = 16 := poly1305_size _ _
  rw [boxSeal, boxOpen, if_pos (by rw [ByteArray.size_append, hMACs]; omega),
    ByteArray.extract_append_eq_right hMACs.symm ByteArray.size_append,
    ByteArray.extract_append_eq_left hMACs.symm, if_pos rfl, hCTs,
    xorBytes_involution msg (ks.extract 32 (32 + msg.size)) (Nat.le_of_eq hSs.symm)]

def spec : Aead where
  name := `xsalsa20poly1305
  keyBytes := 32
  nonceBytes := 24
  tagBytes := 16
  encrypt := encrypt
  decrypt? := decrypt?

theorem spec_lawful : spec.Lawful where
  decrypt?_encrypt key nonce _ad msg := by
    have hcs : (boxSeal (xsalsaKeystream key nonce (32 + msg.size)) msg).size = 16 + msg.size := by
      rw [boxSeal, ByteArray.size_append, poly1305_size, xorBytes_size, ByteArray.size_extract,
        xsalsaKeystream_size]; omega
    have hextrs : ((boxSeal (xsalsaKeystream key nonce (32 + msg.size)) msg).extract 16
        (boxSeal (xsalsaKeystream key nonce (32 + msg.size)) msg).size).size = msg.size := by
      rw [ByteArray.size_extract, hcs]; omega
    show spec.decrypt? key nonce _ad (spec.encrypt key nonce _ad msg) = some msg
    simp only [spec]
    rw [encrypt, decrypt?, hextrs]
    exact boxOpen_boxSeal _ msg (Nat.le_of_eq (xsalsaKeystream_size _ _ _).symm)
  size_encrypt key nonce _ad msg := by
    show (spec.encrypt key nonce _ad msg).size = msg.size + spec.tagBytes
    simp only [spec]
    rw [encrypt, boxSeal, ByteArray.size_append, poly1305_size, xorBytes_size,
      ByteArray.size_extract, xsalsaKeystream_size]
    omega

end Sodium.Theory.XSalsa20poly1305
