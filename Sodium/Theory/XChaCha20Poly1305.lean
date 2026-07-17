import Sodium.Theory.Basic
import Sodium.Theory.Poly1305
import Sodium.Data.Aead

namespace Sodium.Theory.XChaCha20Poly1305

open LittleEndian

/-! ## ChaCha20 / HChaCha20 core -/

/-- ChaCha20 quarter-round on words `a,b,c,d` of the state. -/
def chachaQR (x : Array UInt32) (a b c d : Nat) : Array UInt32 :=
  let x := x.set! a (x[a]! + x[b]!); let x := x.set! d (rotl (x[d]! ^^^ x[a]!) 16)
  let x := x.set! c (x[c]! + x[d]!); let x := x.set! b (rotl (x[b]! ^^^ x[c]!) 12)
  let x := x.set! a (x[a]! + x[b]!); let x := x.set! d (rotl (x[d]! ^^^ x[a]!) 8)
  let x := x.set! c (x[c]! + x[d]!); let x := x.set! b (rotl (x[b]! ^^^ x[c]!) 7)
  x

/-- One ChaCha20 double round: four column then four diagonal quarter-rounds. -/
def chachaDoubleRound (x : Array UInt32) : Array UInt32 :=
  ([ (0,4,8,12),(1,5,9,13),(2,6,10,14),(3,7,11,15),
     (0,5,10,15),(1,6,11,12),(2,7,8,13),(3,4,9,14) ] : List (Nat × Nat × Nat × Nat)).foldl
    (fun x (a, b, c, d) => chachaQR x a b c d) x

def chachaRounds (x : Array UInt32) : Array UInt32 :=
  (List.range 10).foldl (fun x _ => chachaDoubleRound x) x

/-- ChaCha20 (IETF) state: constants, 32-byte key, 32-bit counter, 12-byte nonce. -/
def chachaState (counter : UInt32) (key nonce12 : ByteArray) : Array UInt32 :=
  #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574,
    load32 key 0, load32 key 4, load32 key 8, load32 key 12,
    load32 key 16, load32 key 20, load32 key 24, load32 key 28,
    counter, load32 nonce12 0, load32 nonce12 4, load32 nonce12 8]

/-- ChaCha20 core: 20 rounds with feed-forward, producing a 64-byte block. -/
def chachaCore (counter : UInt32) (key nonce12 : ByteArray) : ByteArray :=
  let j := chachaState counter key nonce12
  let x := chachaRounds j
  ⟨((List.range 16).flatMap fun i => store32 (x[i]! + j[i]!)).toArray⟩

/-- HChaCha20 state: constants, 32-byte key, 16-byte input. -/
def hchachaState (input16 key : ByteArray) : Array UInt32 :=
  #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574,
    load32 key 0, load32 key 4, load32 key 8, load32 key 12,
    load32 key 16, load32 key 20, load32 key 24, load32 key 28,
    load32 input16 0, load32 input16 4, load32 input16 8, load32 input16 12]

/-- HChaCha20: 20 rounds without feed-forward, extracting words 0,1,2,3,12,13,14,15. -/
def hchacha20 (input16 key : ByteArray) : ByteArray :=
  let x := chachaRounds (hchachaState input16 key)
  ⟨([0, 1, 2, 3, 12, 13, 14, 15].flatMap fun i => store32 x[i]!).toArray⟩

/-- `n` consecutive ChaCha20 keystream blocks starting at block `counter`. -/
def chachaBlocks (key nonce12 : ByteArray) (counter : Nat) : Nat → ByteArray
  | 0 => .empty
  | n + 1 =>
    chachaCore (UInt32.ofNat counter) key nonce12 ++ chachaBlocks key nonce12 (counter + 1) n

def chachaKeystream (key nonce12 : ByteArray) (len : Nat) : ByteArray :=
  (chachaBlocks key nonce12 0 ((len + 63) / 64)).extract 0 len

/-- XChaCha20 keystream: HChaCha20 subkey from nonce[0:16]; ChaCha20 with IETF nonce
`0⁴ ‖ nonce[16:24]`. -/
def xchachaKeystream (key : ByteVector 32) (nonce : ByteVector 24) (len : Nat) : ByteArray :=
  let subkey := hchacha20 (nonce.toByteArray.extract 0 16) key.toByteArray
  let nonce12 := (⟨Array.replicate 4 0⟩ : ByteArray) ++ nonce.toByteArray.extract 16 24
  chachaKeystream subkey nonce12 len

/-! ## The RFC 8439 AEAD construction -/

def pad16Zeros (n : Nat) : ByteArray := ⟨Array.replicate ((16 - n % 16) % 16) 0⟩

/-- Poly1305 MAC input: `ad ‖ pad16 ‖ ct ‖ pad16 ‖ LE64(|ad|) ‖ LE64(|ct|)`. -/
def macData (ad ct : ByteArray) : ByteArray :=
  ad ++ pad16Zeros ad.size ++ ct ++ pad16Zeros ct.size ++ bytesLE 8 ad.size ++ bytesLE 8 ct.size

/-- Seal `msg` (with associated data `ad`) under keystream `ks`: XOR ciphertext then tag. -/
def aeadSeal (ks ad msg : ByteArray) : ByteArray :=
  let ct := xorBytes msg (ks.extract 64 (64 + msg.size))
  ct ++ poly1305 (ks.extract 0 32) (macData ad ct)

/-- Open ciphertext `c` under keystream `ks`, verifying the Poly1305 tag (which trails the ct). -/
def aeadOpen (ks ad c : ByteArray) : Option ByteArray :=
  if 16 ≤ c.size then
    let ct := c.extract 0 (c.size - 16)
    if c.extract (c.size - 16) c.size = poly1305 (ks.extract 0 32) (macData ad ct) then
      some (xorBytes ct (ks.extract 64 (64 + ct.size)))
    else none
  else none

@[implemented_by Sodium.XChaCha20Poly1305.encrypt]
def encrypt (key : @& ByteVector 32) (nonce : @& ByteVector 24) (ad msg : @& ByteArray) :
    ByteArray :=
  aeadSeal (xchachaKeystream key nonce (64 + msg.size)) ad msg

@[implemented_by Sodium.XChaCha20Poly1305.decrypt?]
def decrypt? (key : @& ByteVector 32) (nonce : @& ByteVector 24) (ad c : @& ByteArray) :
    Option ByteArray :=
  aeadOpen (xchachaKeystream key nonce (64 + (c.extract 0 (c.size - 16)).size)) ad c

/-! ## Size lemmas and the AEAD round trip -/

theorem chachaCore_size (counter : UInt32) (key nonce12 : ByteArray) :
    (chachaCore counter key nonce12).size = 64 := by
  simp only [chachaCore, ByteArray.size, List.size_toArray, List.length_flatMap, store32,
    List.length_cons, List.length_nil]
  decide

theorem chachaBlocks_size (key nonce12 : ByteArray) (counter n : Nat) :
    (chachaBlocks key nonce12 counter n).size = n * 64 := by
  induction n generalizing counter with
  | zero => rfl
  | succ n ih => simp only [chachaBlocks, ByteArray.size_append, chachaCore_size, ih]; omega

theorem xchachaKeystream_size (key : ByteVector 32) (nonce : ByteVector 24) (len : Nat) :
    (xchachaKeystream key nonce len).size = len := by
  simp only [xchachaKeystream, chachaKeystream, ByteArray.size_extract, chachaBlocks_size,
    Nat.sub_zero]
  have h := Nat.div_add_mod (len + 63) 64
  have h2 : (len + 63) % 64 < 64 := Nat.mod_lt _ (by decide)
  omega

/-- The AEAD round trip under a shared keystream: encrypt-then-MAC with a XOR stream cipher
decrypts correctly, because XOR is involutive and the MAC recomputes identically on the same
associated data and ciphertext. -/
theorem aeadOpen_aeadSeal (ks ad msg : ByteArray) (hks : 64 + msg.size ≤ ks.size) :
    aeadOpen ks ad (aeadSeal ks ad msg) = some msg := by
  have hSs : (ks.extract 64 (64 + msg.size)).size = msg.size := by
    rw [ByteArray.size_extract]; omega
  have hCTs : (xorBytes msg (ks.extract 64 (64 + msg.size))).size = msg.size := by
    rw [xorBytes_size, hSs]; omega
  have hMACs : (poly1305 (ks.extract 0 32)
      (macData ad (xorBytes msg (ks.extract 64 (64 + msg.size))))).size = 16 := poly1305_size _ _
  rw [aeadSeal, aeadOpen, ByteArray.size_append, hMACs, Nat.add_sub_cancel,
    if_pos (by omega), ByteArray.extract_append_eq_left rfl,
    ByteArray.extract_append_eq_right rfl (by rw [hMACs]), if_pos rfl, hCTs,
    xorBytes_involution msg (ks.extract 64 (64 + msg.size)) (Nat.le_of_eq hSs.symm)]

def spec : Aead where
  name := `xchacha20poly1305
  keyBytes := 32
  nonceBytes := 24
  tagBytes := 16
  encrypt := encrypt
  decrypt? := decrypt?

theorem spec_lawful : spec.Lawful where
  decrypt?_encrypt key nonce ad msg := by
    have hcs : (aeadSeal (xchachaKeystream key nonce (64 + msg.size)) ad msg).size
        = msg.size + 16 := by
      rw [aeadSeal, ByteArray.size_append, poly1305_size, xorBytes_size, ByteArray.size_extract,
        xchachaKeystream_size]; omega
    have hextrs : ((aeadSeal (xchachaKeystream key nonce (64 + msg.size)) ad msg).extract 0
        ((aeadSeal (xchachaKeystream key nonce (64 + msg.size)) ad msg).size - 16)).size
        = msg.size := by
      rw [ByteArray.size_extract, hcs]; omega
    show spec.decrypt? key nonce ad (spec.encrypt key nonce ad msg) = some msg
    simp only [spec]
    rw [encrypt, decrypt?, hextrs]
    exact aeadOpen_aeadSeal _ ad msg (Nat.le_of_eq (xchachaKeystream_size _ _ _).symm)
  size_encrypt key nonce ad msg := by
    show (spec.encrypt key nonce ad msg).size = msg.size + spec.tagBytes
    simp only [spec]
    rw [encrypt, aeadSeal, ByteArray.size_append, poly1305_size, xorBytes_size,
      ByteArray.size_extract, xchachaKeystream_size]
    omega

end Sodium.Theory.XChaCha20Poly1305
