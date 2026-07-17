import Sodium.Theory.Basic
import Sodium.Theory.Poly1305
import Sodium.Data.Aead

namespace Sodium.Theory.Aegis256

open Sodium.LittleEndian

/-! ## AES round (byte-exact AESENC, column-major state) -/

def gfMul (a b : UInt8) : UInt8 := Id.run do
  let mut a := a; let mut b := b; let mut p : UInt8 := 0
  for _ in [0:8] do
    if b &&& 1 == 1 then p := p ^^^ a
    let hi := a &&& 0x80
    a := a <<< 1
    if hi == 0x80 then a := a ^^^ 0x1b
    b := b >>> 1
  return p

def gfInv (a : UInt8) : UInt8 := Id.run do
  if a == 0 then return 0
  let mut r : UInt8 := 1
  for _ in [0:254] do r := gfMul r a
  return r

/-- The AES S-box, computed as the GF(2⁸) inverse followed by the affine transform. -/
def sbox : Array UInt8 := Id.run do
  let mut arr := Array.replicate 256 (0 : UInt8)
  for x in [0:256] do
    let inv := gfInv (UInt8.ofNat x)
    let r1 := (inv <<< 1) ||| (inv >>> 7)
    let r2 := (inv <<< 2) ||| (inv >>> 6)
    let r3 := (inv <<< 3) ||| (inv >>> 5)
    let r4 := (inv <<< 4) ||| (inv >>> 4)
    arr := arr.set! x (inv ^^^ r1 ^^^ r2 ^^^ r3 ^^^ r4 ^^^ 0x63)
  return arr

def subBytes (b : ByteArray) : ByteArray :=
  ⟨(b.data.toList.map fun x => sbox[x.toNat]!).toArray⟩

def shiftRows (b : ByteArray) : ByteArray :=
  ⟨Array.ofFn (n := 16) fun i =>
    let row := i.val % 4
    b.get! (((i.val / 4 + row) % 4) * 4 + row)⟩

def mixColumns (b : ByteArray) : ByteArray :=
  ⟨Array.ofFn (n := 16) fun i =>
    let col := i.val / 4; let r := i.val % 4
    let a0 := b.get! (col * 4); let a1 := b.get! (col * 4 + 1)
    let a2 := b.get! (col * 4 + 2); let a3 := b.get! (col * 4 + 3)
    match r with
    | 0 => gfMul 2 a0 ^^^ gfMul 3 a1 ^^^ a2 ^^^ a3
    | 1 => a0 ^^^ gfMul 2 a1 ^^^ gfMul 3 a2 ^^^ a3
    | 2 => a0 ^^^ a1 ^^^ gfMul 2 a2 ^^^ gfMul 3 a3
    | _ => gfMul 3 a0 ^^^ a1 ^^^ a2 ^^^ gfMul 2 a3⟩

/-- One AES encryption round: `MixColumns(ShiftRows(SubBytes(a))) ⊕ roundkey`. -/
def aesenc (a rk : ByteArray) : ByteArray := xorBytes (mixColumns (shiftRows (subBytes a))) rk

/-! ## AEGIS-256 state machine -/

def andBytes (a b : ByteArray) : ByteArray :=
  ⟨(List.zipWith (· &&& ·) a.data.toList b.data.toList).toArray⟩

def padTo16 (b : ByteArray) : ByteArray := b ++ ⟨Array.replicate (16 - b.size) 0⟩

/-- AEGIS-256 state update with data block `d`. -/
def update (S : Array ByteArray) (d : ByteArray) : Array ByteArray :=
  #[xorBytes (aesenc S[5]! S[0]!) d, aesenc S[0]! S[1]!, aesenc S[1]! S[2]!,
    aesenc S[2]! S[3]!, aesenc S[3]! S[4]!, aesenc S[4]! S[5]!]

/-- Keystream block: `S₁ ⊕ S₄ ⊕ S₅ ⊕ (S₂ ∧ S₃)`. -/
def ksBlock (S : Array ByteArray) : ByteArray :=
  xorBytes (xorBytes (xorBytes S[1]! S[4]!) S[5]!) (andBytes S[2]! S[3]!)

/-- Apply `update … d` to `S` a total of `n` times. -/
def iterUpdate (d : ByteArray) : Nat → Array ByteArray → Array ByteArray
  | 0, S => S
  | n + 1, S => iterUpdate d n (update S d)

/-- One initialization round: absorb `k0, k1, k0n0, k1n1` in turn. -/
def initRounds (k0 k1 k0n0 k1n1 : ByteArray) : Nat → Array ByteArray → Array ByteArray
  | 0, S => S
  | n + 1, S =>
    initRounds k0 k1 k0n0 k1n1 n (update (update (update (update S k0) k1) k0n0) k1n1)

def c0 : ByteArray :=
  ⟨#[0x00,0x01,0x01,0x02,0x03,0x05,0x08,0x0d,0x15,0x22,0x37,0x59,0x90,0xe9,0x79,0x62]⟩
def c1 : ByteArray :=
  ⟨#[0xdb,0x3d,0x18,0x55,0x6d,0xc2,0x2f,0xf1,0x20,0x11,0x31,0x42,0x73,0xb5,0x28,0xdd]⟩

def initState (key nonce : ByteArray) : Array ByteArray :=
  let k0 := key.extract 0 16; let k1 := key.extract 16 32
  let n0 := nonce.extract 0 16; let n1 := nonce.extract 16 32
  let k0n0 := xorBytes k0 n0; let k1n1 := xorBytes k1 n1
  initRounds k0 k1 k0n0 k1n1 4 #[k0n0, k1n1, c1, c0, xorBytes k0 c0, xorBytes k1 c1]

/-- Split a byte array into 16-byte chunks (the last chunk may be shorter). -/
def chunk16 (b : ByteArray) : List ByteArray :=
  if b.size = 0 then []
  else if b.size ≤ 16 then [b]
  else b.extract 0 16 :: chunk16 (b.extract 16 b.size)
termination_by b.size
decreasing_by
  simp only [ByteArray.size_extract]; omega

def absorbAd (S : Array ByteArray) (ad : ByteArray) : Array ByteArray :=
  (chunk16 ad).foldl (fun S c => update S (padTo16 c)) S

def encStep (S : Array ByteArray) (c : ByteArray) : ByteArray × Array ByteArray :=
  let z := ksBlock S
  ((xorBytes (padTo16 c) z).extract 0 c.size, update S (padTo16 c))

def encChunks (S : Array ByteArray) : List ByteArray → ByteArray × Array ByteArray
  | [] => (ByteArray.empty, S)
  | c :: cs =>
    let (ct0, S') := encStep S c
    let (rest, Sf) := encChunks S' cs
    (ct0 ++ rest, Sf)

def decStep (S : Array ByteArray) (c : ByteArray) : ByteArray × Array ByteArray :=
  let z := ksBlock S
  let msgOut := (xorBytes (padTo16 c) z).extract 0 c.size
  (msgOut, update S (padTo16 msgOut))

def decChunks (S : Array ByteArray) : List ByteArray → ByteArray × Array ByteArray
  | [] => (ByteArray.empty, S)
  | c :: cs =>
    let (m0, S') := decStep S c
    let (rest, Sf) := decChunks S' cs
    (m0 ++ rest, Sf)

/-- Finalization: absorb the length block, then emit the 32-byte tag. -/
def macTag (S : Array ByteArray) (adlen mlen : Nat) : ByteArray :=
  let tmp := xorBytes (bytesLE 8 (adlen * 8) ++ bytesLE 8 (mlen * 8)) S[3]!
  let Sf := iterUpdate tmp 7 S
  xorBytes (xorBytes Sf[2]! Sf[1]!) Sf[0]! ++ xorBytes (xorBytes Sf[5]! Sf[4]!) Sf[3]!

/-! ## The AEAD -/

def aeadSeal (key nonce ad msg : ByteArray) : ByteArray :=
  let (ct, Sf) := encChunks (absorbAd (initState key nonce) ad) (chunk16 msg)
  ct ++ macTag Sf ad.size msg.size

def aeadOpen (key nonce ad c : ByteArray) : Option ByteArray :=
  if 32 ≤ c.size then
    let ct := c.extract 0 (c.size - 32)
    let (msg, Sf) := decChunks (absorbAd (initState key nonce) ad) (chunk16 ct)
    if c.extract (c.size - 32) c.size = macTag Sf ad.size ct.size then some msg else none
  else none

@[implemented_by Sodium.Aegis256.encrypt]
def encrypt (key nonce : @& ByteVector 32) (ad msg : @& ByteArray) : ByteArray :=
  aeadSeal key.toByteArray nonce.toByteArray ad msg

@[implemented_by Sodium.Aegis256.decrypt?]
def decrypt? (key nonce : @& ByteVector 32) (ad c : @& ByteArray) : Option ByteArray :=
  aeadOpen key.toByteArray nonce.toByteArray ad c

def spec : Aead where
  name := `aegis256
  keyBytes := 32
  nonceBytes := 32
  tagBytes := 32
  encrypt := encrypt
  decrypt? := decrypt?

theorem mixColumns_size (b : ByteArray) : (mixColumns b).size = 16 := by
  simp [mixColumns, ByteArray.size]

theorem andBytes_size (a b : ByteArray) : (andBytes a b).size = min a.size b.size := by
  simp only [andBytes, ByteArray.size, List.size_toArray, List.length_zipWith,
    Array.length_toList]

theorem aesenc_size (a rk : ByteArray) : (aesenc a rk).size = min 16 rk.size := by
  rw [aesenc, xorBytes_size, mixColumns_size]

theorem padTo16_size (c : ByteArray) (h : c.size ≤ 16) : (padTo16 c).size = 16 := by
  rw [padTo16, ByteArray.size_append]
  show c.size + (Array.replicate (16 - c.size) 0).size = 16
  rw [Array.size_replicate]; omega

def WF (S : Array ByteArray) : Prop :=
  (S[0]!).size = 16 ∧ (S[1]!).size = 16 ∧ (S[2]!).size = 16 ∧
  (S[3]!).size = 16 ∧ (S[4]!).size = 16 ∧ (S[5]!).size = 16

theorem update_wf {S : Array ByteArray} {d : ByteArray} (hS : WF S) (hd : d.size = 16) :
    WF (update S d) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (xorBytes (aesenc S[5]! S[0]!) d).size = 16
    rw [xorBytes_size, aesenc_size, h0, hd]; omega
  · show (aesenc S[0]! S[1]!).size = 16
    rw [aesenc_size, h1]; omega
  · show (aesenc S[1]! S[2]!).size = 16
    rw [aesenc_size, h2]; omega
  · show (aesenc S[2]! S[3]!).size = 16
    rw [aesenc_size, h3]; omega
  · show (aesenc S[3]! S[4]!).size = 16
    rw [aesenc_size, h4]; omega
  · show (aesenc S[4]! S[5]!).size = 16
    rw [aesenc_size, h5]; omega

theorem ksBlock_size {S : Array ByteArray} (hS : WF S) : (ksBlock S).size = 16 := by
  obtain ⟨_, h1, h2, h3, h4, h5⟩ := hS
  rw [ksBlock, xorBytes_size, xorBytes_size, xorBytes_size, andBytes_size, h1, h2, h3, h4, h5]
  omega

theorem iterUpdate_wf {d : ByteArray} (hd : d.size = 16) (n : Nat) {S : Array ByteArray}
    (hS : WF S) : WF (iterUpdate d n S) := by
  induction n generalizing S with
  | zero => exact hS
  | succ n ih => simp only [iterUpdate]; exact ih (update_wf hS hd)

theorem initRounds_wf {k0 k1 k0n0 k1n1 : ByteArray}
    (h0 : k0.size = 16) (h1 : k1.size = 16) (h2 : k0n0.size = 16) (h3 : k1n1.size = 16)
    (n : Nat) {S : Array ByteArray} (hS : WF S) : WF (initRounds k0 k1 k0n0 k1n1 n S) := by
  induction n generalizing S with
  | zero => exact hS
  | succ n ih =>
    simp only [initRounds]
    exact ih (update_wf (update_wf (update_wf (update_wf hS h0) h1) h2) h3)

theorem c0_size : c0.size = 16 := by decide
theorem c1_size : c1.size = 16 := by decide

theorem initState_wf {key nonce : ByteArray} (hk : key.size = 32) (hn : nonce.size = 32) :
    WF (initState key nonce) := by
  simp only [initState]
  have ek0 : (key.extract 0 16).size = 16 := by rw [ByteArray.size_extract]; omega
  have ek1 : (key.extract 16 32).size = 16 := by rw [ByteArray.size_extract]; omega
  have en0 : (nonce.extract 0 16).size = 16 := by rw [ByteArray.size_extract]; omega
  have en1 : (nonce.extract 16 32).size = 16 := by rw [ByteArray.size_extract]; omega
  have hk0n0 : (xorBytes (key.extract 0 16) (nonce.extract 0 16)).size = 16 := by
    rw [xorBytes_size, ek0, en0]; omega
  have hk1n1 : (xorBytes (key.extract 16 32) (nonce.extract 16 32)).size = 16 := by
    rw [xorBytes_size, ek1, en1]; omega
  apply initRounds_wf ek0 ek1 hk0n0 hk1n1
  refine ⟨hk0n0, hk1n1, c1_size, c0_size, ?_, ?_⟩
  · show (xorBytes (key.extract 0 16) c0).size = 16
    rw [xorBytes_size, ek0, c0_size]; omega
  · show (xorBytes (key.extract 16 32) c1).size = 16
    rw [xorBytes_size, ek1, c1_size]; omega

theorem chunk16_size_le (b : ByteArray) : ∀ c ∈ chunk16 b, c.size ≤ 16 := by
  fun_induction chunk16 b with
  | case1 b h0 => intro c hc; simp at hc
  | case2 b h0 hle => intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact hle
  | case3 b h0 hgt ih =>
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · rw [ByteArray.size_extract]; omega
    · exact ih c hc

theorem foldl_upd_wf (cs : List ByteArray) (h : ∀ c ∈ cs, c.size ≤ 16) {S : Array ByteArray}
    (hS : WF S) : WF (cs.foldl (fun S c => update S (padTo16 c)) S) := by
  induction cs generalizing S with
  | nil => exact hS
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      (update_wf hS (padTo16_size c (h c (by simp))))

theorem absorbAd_wf {S : Array ByteArray} (hS : WF S) (ad : ByteArray) :
    WF (absorbAd S ad) := by
  simp only [absorbAd]
  exact foldl_upd_wf (chunk16 ad) (chunk16_size_le ad) hS

theorem macTag_size {S : Array ByteArray} (hS : WF S) (adlen mlen : Nat) :
    (macTag S adlen mlen).size = 32 := by
  have htmp : (xorBytes (bytesLE 8 (adlen * 8) ++ bytesLE 8 (mlen * 8)) S[3]!).size = 16 := by
    obtain ⟨_, _, _, h3, _, _⟩ := hS
    rw [xorBytes_size, ByteArray.size_append, bytesLE_size, bytesLE_size, h3]; omega
  have hSf : WF (iterUpdate (xorBytes (bytesLE 8 (adlen * 8) ++ bytesLE 8 (mlen * 8)) S[3]!) 7 S) :=
    iterUpdate_wf htmp 7 hS
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hSf
  simp only [macTag]
  rw [ByteArray.size_append, xorBytes_size, xorBytes_size, xorBytes_size, xorBytes_size,
    h0, h1, h2, h3, h4, h5]
  omega

/-! ## Prefix-XOR and the encrypt/decrypt step inverse -/

theorem xorList_take : ∀ (al bl : List UInt8) (k : Nat),
    (xorList al bl).take k = xorList (al.take k) (bl.take k)
  | [], bl, k => by simp [xorList]
  | a :: as, [], k => by cases k <;> simp [xorList]
  | a :: as, b :: bs, 0 => by simp [xorList]
  | a :: as, b :: bs, k+1 => by
    simp only [xorList, List.take_succ_cons]; rw [xorList_take as bs k]

theorem extract0_toList (b : ByteArray) (k : Nat) :
    (b.extract 0 k).data.toList = b.data.toList.take k := by
  rw [ByteArray.data_extract]; simp [Array.toList_extract]

theorem xorBytes_toList (a b : ByteArray) :
    (xorBytes a b).data.toList = xorList a.data.toList b.data.toList := by
  simp only [xorBytes, List.toList_toArray]

theorem xorBytes_extract0 (a b : ByteArray) (k : Nat) :
    (xorBytes a b).extract 0 k = xorBytes (a.extract 0 k) (b.extract 0 k) := by
  apply ByteArray.ext; apply Array.ext'
  rw [extract0_toList, xorBytes_toList, xorBytes_toList, extract0_toList, extract0_toList,
    xorList_take]

theorem padTo16_extract_self (x : ByteArray) : (padTo16 x).extract 0 x.size = x := by
  rw [padTo16, ByteArray.extract_append_eq_left rfl]

theorem encStep_fst_size (S : Array ByteArray) (c : ByteArray) (h : c.size ≤ 16)
    (hS : WF S) : (encStep S c).1.size = c.size := by
  simp only [encStep, ByteArray.size_extract]
  rw [xorBytes_size, padTo16_size c h, ksBlock_size hS]; omega

theorem decStep_encStep (S : Array ByteArray) (c : ByteArray) (h : c.size ≤ 16) (hS : WF S) :
    decStep S (encStep S c).1 = (c, (encStep S c).2) := by
  have hz : (ksBlock S).size = 16 := ksBlock_size hS
  have hzc : ((ksBlock S).extract 0 c.size).size = c.size := by
    rw [ByteArray.size_extract, hz]; omega
  have hct0size : (encStep S c).1.size = c.size := encStep_fst_size S c h hS
  have eq_ct0 : (encStep S c).1 = xorBytes c ((ksBlock S).extract 0 c.size) := by
    simp only [encStep]; rw [xorBytes_extract0, padTo16_extract_self]
  have hpad : (padTo16 (encStep S c).1).extract 0 c.size = (encStep S c).1 := by
    rw [← hct0size]; exact padTo16_extract_self _
  have hM : (xorBytes (padTo16 (encStep S c).1) (ksBlock S)).extract 0 (encStep S c).1.size = c :=
      by rw [hct0size, xorBytes_extract0, hpad, eq_ct0,
        xorBytes_involution c _ (Nat.le_of_eq hzc.symm)]
  apply Prod.ext
  · show (xorBytes (padTo16 (encStep S c).1) (ksBlock S)).extract 0 (encStep S c).1.size = c
    exact hM
  · show update S (padTo16 ((xorBytes (padTo16 (encStep S c).1) (ksBlock S)).extract 0
        (encStep S c).1.size)) = (encStep S c).2
    rw [hM]; rfl

/-! ## Chunking algebra and the AEAD round trip -/

theorem chunk16_empty : chunk16 ByteArray.empty = [] := by rw [chunk16]; rfl

theorem chunk16_single (a : ByteArray) (h0 : a.size ≠ 0) (hle : a.size ≤ 16) :
    chunk16 a = [a] := by
  rw [chunk16, if_neg h0, if_pos hle]

theorem chunk16_append (a b : ByteArray) (ha : a.size = 16) :
    chunk16 (a ++ b) = a :: chunk16 b := by
  have hsz : (a ++ b).size = 16 + b.size := by rw [ByteArray.size_append, ha]
  by_cases hb : b.size = 0
  · have hbe : b = ByteArray.empty := ByteArray.size_eq_zero_iff.mp hb
    rw [hbe, ByteArray.append_empty, chunk16_single a (by omega) (by omega), chunk16_empty]
  · rw [chunk16, if_neg (by omega), if_neg (by omega),
      ByteArray.extract_append_eq_left ha.symm,
      ByteArray.extract_append_eq_right ha.symm (by rw [hsz, ha])]

theorem encChunks_nil (S : Array ByteArray) : encChunks S [] = (ByteArray.empty, S) := rfl
theorem decChunks_nil (S : Array ByteArray) : decChunks S [] = (ByteArray.empty, S) := rfl

theorem encChunks_cons (S : Array ByteArray) (c : ByteArray) (cs : List ByteArray) :
    encChunks S (c :: cs) =
      ((encStep S c).1 ++ (encChunks (encStep S c).2 cs).1, (encChunks (encStep S c).2 cs).2) := by
  simp only [encChunks]

theorem decChunks_cons (S : Array ByteArray) (c : ByteArray) (cs : List ByteArray) :
    decChunks S (c :: cs) =
      ((decStep S c).1 ++ (decChunks (decStep S c).2 cs).1, (decChunks (decStep S c).2 cs).2) := by
  simp only [decChunks]

theorem split16 (m : ByteArray) (h : 16 ≤ m.size) :
    m.extract 0 16 ++ m.extract 16 m.size = m := by
  rw [← ByteArray.extract_eq_extract_append_extract 16 (by omega) h, ByteArray.extract_zero_size]

theorem seal_open_core (m : ByteArray) (S : Array ByteArray) (hS : WF S) :
    (encChunks S (chunk16 m)).1.size = m.size ∧
    decChunks S (chunk16 (encChunks S (chunk16 m)).1) = (m, (encChunks S (chunk16 m)).2) := by
  by_cases h0 : m.size = 0
  · have hme : m = ByteArray.empty := ByteArray.size_eq_zero_iff.mp h0
    subst hme
    rw [chunk16_empty, encChunks_nil]
    exact ⟨rfl, by rw [chunk16_empty, decChunks_nil]⟩
  · by_cases hle : m.size ≤ 16
    · rw [chunk16_single m h0 hle, encChunks_cons, encChunks_nil, ByteArray.append_empty]
      have hct : (encStep S m).1.size = m.size := encStep_fst_size S m hle hS
      refine ⟨hct, ?_⟩
      rw [chunk16_single _ (by rw [hct]; exact h0) (by rw [hct]; exact hle),
        decChunks_cons, decChunks_nil, ByteArray.append_empty, decStep_encStep S m hle hS]
    · have hgt : 16 ≤ m.size := by omega
      have ha : (m.extract 0 16).size = 16 := by rw [ByteArray.size_extract]; omega
      have hrest : (m.extract 16 m.size).size = m.size - 16 := by
        rw [ByteArray.size_extract]; omega
      have hWF' : WF (encStep S (m.extract 0 16)).2 := by
        show WF (update S (padTo16 (m.extract 0 16)))
        exact update_wf hS (padTo16_size _ (by omega))
      have IH := seal_open_core (m.extract 16 m.size) (encStep S (m.extract 0 16)).2 hWF'
      rw [chunk16, if_neg h0, if_neg hle, encChunks_cons]
      have hct0 : (encStep S (m.extract 0 16)).1.size = 16 := by
        rw [encStep_fst_size S _ (by omega) hS, ha]
      refine ⟨?_, ?_⟩
      · rw [ByteArray.size_append, hct0, IH.1, hrest]; omega
      · rw [chunk16_append _ _ hct0, decChunks_cons,
          decStep_encStep S (m.extract 0 16) (by omega) hS]
        rw [IH.2, split16 m hgt]
termination_by m.size
decreasing_by rw [ByteArray.size_extract]; omega

theorem encChunks_wf (cs : List ByteArray) (h : ∀ c ∈ cs, c.size ≤ 16) {S : Array ByteArray}
    (hS : WF S) : WF (encChunks S cs).2 := by
  induction cs generalizing S with
  | nil => exact hS
  | cons c cs ih =>
    rw [encChunks_cons]
    refine ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) ?_
    show WF (update S (padTo16 c))
    exact update_wf hS (padTo16_size c (h c (by simp)))

theorem aeadSeal_size (key nonce ad msg : ByteArray) (hk : key.size = 32) (hn : nonce.size = 32) :
    (aeadSeal key nonce ad msg).size = msg.size + 32 := by
  have hWF : WF (absorbAd (initState key nonce) ad) := absorbAd_wf (initState_wf hk hn) ad
  have hWFf : WF (encChunks (absorbAd (initState key nonce) ad) (chunk16 msg)).2 :=
    encChunks_wf (chunk16 msg) (chunk16_size_le msg) hWF
  simp only [aeadSeal]
  rw [ByteArray.size_append, (seal_open_core msg _ hWF).1, macTag_size hWFf]

theorem aeadSeal_eq (key nonce ad msg : ByteArray) :
    aeadSeal key nonce ad msg =
      (encChunks (absorbAd (initState key nonce) ad) (chunk16 msg)).1 ++
      macTag (encChunks (absorbAd (initState key nonce) ad) (chunk16 msg)).2 ad.size msg.size :=
  rfl

theorem aeadOpen_aeadSeal (key nonce ad msg : ByteArray) (hk : key.size = 32)
    (hn : nonce.size = 32) : aeadOpen key nonce ad (aeadSeal key nonce ad msg) = some msg := by
  have hWF := absorbAd_wf (initState_wf hk hn) ad
  obtain ⟨hsz, hdec⟩ := seal_open_core msg (absorbAd (initState key nonce) ad) hWF
  have htag : (macTag (encChunks (absorbAd (initState key nonce) ad) (chunk16 msg)).2
      ad.size msg.size).size = 32 :=
    macTag_size (encChunks_wf (chunk16 msg) (chunk16_size_le msg) hWF) _ _
  rw [aeadSeal_eq]
  generalize hSf : (encChunks (absorbAd (initState key nonce) ad) (chunk16 msg)).2 = Sf at *
  generalize hct : (encChunks (absorbAd (initState key nonce) ad) (chunk16 msg)).1 = ct at *
  have hcsize : (ct ++ macTag Sf ad.size msg.size).size = msg.size + 32 := by
    rw [ByteArray.size_append, hsz, htag]
  have hsub : (ct ++ macTag Sf ad.size msg.size).size - 32 = msg.size := by rw [hcsize]; omega
  have hleft : (ct ++ macTag Sf ad.size msg.size).extract 0
      ((ct ++ macTag Sf ad.size msg.size).size - 32) = ct := by
    rw [hsub]; exact ByteArray.extract_append_eq_left hsz.symm
  have hright : (ct ++ macTag Sf ad.size msg.size).extract
      ((ct ++ macTag Sf ad.size msg.size).size - 32)
      (ct ++ macTag Sf ad.size msg.size).size = macTag Sf ad.size msg.size := by
    rw [hsub, hcsize]
    exact ByteArray.extract_append_eq_right hsz.symm (by rw [hsz, htag])
  simp only [aeadOpen]
  rw [if_pos (by rw [hcsize]; omega), hleft, hright, hdec]
  simp [hsz]

theorem spec_lawful : spec.Lawful where
  decrypt?_encrypt key nonce ad msg := by
    show spec.decrypt? key nonce ad (spec.encrypt key nonce ad msg) = some msg
    simp only [spec]
    rw [encrypt, decrypt?]
    exact aeadOpen_aeadSeal key.toByteArray nonce.toByteArray ad msg
      key.size_toByteArray nonce.size_toByteArray
  size_encrypt key nonce ad msg := by
    show (spec.encrypt key nonce ad msg).size = msg.size + spec.tagBytes
    simp only [spec]
    rw [encrypt]
    exact aeadSeal_size key.toByteArray nonce.toByteArray ad msg
      key.size_toByteArray nonce.size_toByteArray

end Sodium.Theory.Aegis256
