import Sodium.Crypto.Types

open Lean Std Sodium

namespace Sodium.Crypto

variable {spec : Spec}

variable {α β σ : Type}

structure NonceId (spec : Spec) where
  Dom : spec.HasValidShape `nonce
  get : (h : spec.HasValidShape `nonce) → Nonce spec

private structure EntropyState (τ : Sodium σ) where
  entropy : EntropyVector τ
  nonces : NameMap (Σ s, NonceId s) := ∅

structure CryptoContext (τ : Sodium σ) where
  private mtx : Mutex (EntropyState τ)
  ctx : Context Blake2b
  mkey : SymmKey τ Blake2b

inductive CryptoMessage
  | specViolation (spec : Spec) (kind : Name)
  | insufficientEntropy (bytes : Nat)
  deriving Inhabited

@[coe] def CryptoMessage.toMessageData : CryptoMessage → MessageData
  | .specViolation s k => m!"spec violation: shape of kind {k} not supported by {s.name}"
  | .insufficientEntropy bytes => m!"insufficient entropy bytes allocated (expected at least {bytes} bytes)"

instance : ToMessageData CryptoMessage := ⟨CryptoMessage.toMessageData⟩

@[coe] def CryptoMessage.toException (e : CryptoMessage) : Exception :=
  .error .missing (e.toMessageData)

instance : Coe CryptoMessage Exception := ⟨CryptoMessage.toException⟩

abbrev CryptoM (τ : Sodium σ) := ReaderT (CryptoContext τ) MetaM

variable {τ : Sodium σ}

def throwSpecViolation (spec : Spec) (kind : Name) : CryptoM τ α :=
  throw (CryptoMessage.specViolation spec kind).toException

def throwInsufficientEntropy (bytes : Nat) : CryptoM τ α :=
  throw (CryptoMessage.insufficientEntropy bytes).toException

namespace Context

instance : Coe (ByteVector 8) (Context Blake2b) where
  coe x := ⟨x.cast⟩

def ofString (x : String) (h : x.utf8ByteSize = 8) : Context Blake2b :=
  let ctx := x.toUTF8
  have : Blake2b.shapeOf `context = ctx.size := by
    simp [blake2b_context_eq]
    rw [String.size_toUTF8, h]
    rfl
  ⟨this ▸ ctx.toVector⟩

instance : Inhabited (Context Blake2b) where
  default := ofString "standard" (by rfl)

end Context

namespace CryptoM

register_option crypto.entropyBytes : Nat := {
  defValue := 24 * 256
  descr := "The number of random bytes to allocate for entropy."
}

def toMetaM (x : {σ : Type} → (τ : Sodium σ) → CryptoM τ α) (ctx : Context Blake2b := default) : MetaM α := do
  let τ ← init Unit
  let entropy ← EntropyVector.new (τ := τ) (crypto.entropyBytes.get (← getOptions)).toUSize
  let mkey ← FFI.KeyDeriv.keygen (τ := τ)
  let mtx ← Mutex.new {entropy}
  x τ {mtx, ctx, mkey := ⟨mkey.cast⟩}

def resetNonces : CryptoM τ Unit := do
  let mtx := (← read).mtx
  mtx.atomically <| modify ({· with nonces := ∅})

def mkFreshNonce [h : spec.HasValidShape `nonce] : CryptoM τ (Nonce spec) := do
  let mtx := (← read).mtx
  mtx.atomically fun ref => do
    let st ← ref.get
    match st.nonces.find? spec.name with
    | some ⟨spec', stale⟩ =>
      if eq_shape : spec.shapeOf `nonce = spec'.shapeOf `nonce then
        haveI : spec'.HasValidShape `nonce := by
          rw [Spec.has_valid_shape_iff, ← eq_shape]
          exact h.shape_is_valid
        let shape := stale.get this |>.data.succ
        let nonce := ⟨eq_shape ▸ shape⟩
        let nonces := st.nonces.insert spec.name ⟨spec, ⟨h, fun _ => nonce⟩⟩
        ref.modifyGet fun st => (nonce, {st with nonces})
      else
        let (nonce, st) ← next st
        ref.set st
        return nonce
    | _ =>
      let (nonce, st) ← next st
      ref.set st
      return nonce
where
  next (st : EntropyState τ) : CryptoM τ (Nonce spec × EntropyState τ) := do
    let {nonces, entropy, ..} := st
    let shape := spec.shapeOf `nonce

    let (nonce, entropy) ←
      if entropy.size - entropy.off < shape then
        let entropy ← entropy.refresh
        entropy.extract shape
      else
        entropy.extract shape

    if size_eq : nonce.size = shape then
      let nonce : Nonce spec := ⟨nonce, size_eq⟩
      let nonces := nonces.insert spec.name ⟨spec, ⟨h, fun _ => nonce⟩⟩
      return (nonce, {st with nonces, entropy})
    else throwInsufficientEntropy shape

instance : MonadNameGenerator (CryptoM τ) where
  getNGen := do
    let nonce ← mkFreshNonce (spec := UniqId)
    return {namePrefix := UniqId.name, idx := nonce.data.cast.toUInt64LE.toNat}
  setNGen _ :=
    return () -- not allowed, so we ignore.

end CryptoM

export CryptoM (mkFreshNonce)

def mkFreshKey {kind : Name} {X : {σ : Type} → Sodium σ → (spec : Spec) → [spec.HasValidShape kind] → Type} [spec.HasValidShape kind]
    (lift : SecureVector τ spec[kind] → X τ spec) : CryptoM τ (X τ spec) := do
  let key ← SecureVector.new spec[kind]
  return lift key

open FFI KeyDeriv in
def mkStaleKey {kind : Name} {X : {σ : Type} → Sodium σ → (spec : Spec) → [spec.HasValidShape kind] → Type} [spec.HasValidShape kind]
    (lift : SecureVector τ spec[kind] → X τ spec) : CryptoM τ (X τ spec) := do
  let {mkey, ctx, ..} ← read
  let mctx ← getMCtx
  let key ← derive spec[kind] mctx.depth ctx.data.cast mkey.data.cast
  return lift key

open FFI KeyExch in
def mkFreshKeys : CryptoM τ (KeyPair τ Curve25519) := do
  let (pkey, skey) ← keypair
  return ⟨⟨pkey.cast⟩, ⟨skey.cast⟩⟩

open FFI KeyExch in
def mkStaleKeys : CryptoM τ (KeyPair τ Curve25519) := do
  let key : Seed τ UniqId ← mkStaleKey fun data => ⟨data.cast⟩
  let (pkey, skey) ← seedKeypair key.data.cast
  return ⟨⟨pkey.cast⟩, ⟨skey.cast⟩⟩

open FFI Box in
def newSharedKey? (yours : SecretKey τ Curve25519) (theirs : PublicKey Curve25519) : CryptoM τ (Option (SharedKey τ Curve25519HSalsa20)) := do
  let some key ← beforenm theirs.data.cast (yours.data.cast (by simp [USize.ofNatLT_eq_ofNat]; congr))
    | return none
  return some ⟨key.cast (by native_decide)⟩

open FFI KeyExch in
def newClientSession? (yours : KeyPair τ Curve25519) (theirs : PublicKey Curve25519) : CryptoM τ (Option (Session τ Curve25519Blake2b)) := do
  let some sess ← clientSessionKeys (yours.pkey.data.cast) (yours.skey.data.cast) (theirs.data.cast)
    | return none
  return some ⟨⟨sess.1.cast (by native_decide)⟩, ⟨sess.2.cast (by native_decide)⟩⟩

open FFI KeyExch in
def newServerSession? (yours : KeyPair τ Curve25519) (theirs : PublicKey Curve25519) : CryptoM τ (Option (Session τ Curve25519Blake2b)) := do
  let some sess ← serverSessionKeys yours.pkey.data.cast yours.skey.data.cast theirs.data.cast
    | return none
  return some ⟨⟨sess.1.cast (by native_decide)⟩, ⟨sess.2.cast (by native_decide)⟩⟩

def withSessionKey (key : SymmKey τ Curve25519Blake2b) (x : {σ : Type} → (τ : Sodium σ) → CryptoM τ α) : CryptoM τ α := do
  let st ← read
  show MetaM α from Meta.withNewMCtxDepth do
    x τ {st with mkey := ⟨key.data.cast (by native_decide)⟩}

def withNewMetaKey (x : {σ : Type} → (τ : Sodium σ) → CryptoM τ α) : CryptoM τ α := do
  let st ← read
  let mkey : SymmKey τ Blake2b ← mkStaleKey fun data => ⟨data.cast⟩
  show MetaM α from Meta.withNewMCtxDepth do
    x τ {st with mkey}

open FFI SecretBox in
def encrypt [ToJson α] (key : SymmKey τ XSalsa20) (msg : α) : CryptoM τ (CipherText XSalsa20Poly1305) := do
  let nonce ← mkFreshNonce (spec := XSalsa20Poly1305)
  let data := toJson msg |>.compress.toUTF8.toVector
  let cipher ← easy data nonce.data.cast (key.data.cast)
  return {
    nonce
    size := cipher.size
    data := cipher
    shapeOf_mac_le_size := by
      have : XSalsa20Poly1305.shapeOf `mac = MACBYTES := by native_decide
      rw [this]
      exact Nat.le_add_right MACBYTES (toJson msg).compress.toUTF8.size
  }

open FFI SecretBox in
def decrypt? [FromJson α] (key : SymmKey τ XSalsa20) (cipher : CipherText XSalsa20Poly1305) : CryptoM τ (DecryptResult α) := do
  have : cipher.size = MACBYTES + (cipher.size - MACBYTES) := by
    have mac_le : XSalsa20Poly1305.shapeOf `mac ≤ cipher.size := cipher.shapeOf_mac_le_size
    have : XSalsa20Poly1305.shapeOf `mac = MACBYTES := by native_decide
    rw [this] at mac_le
    rw [Nat.add_comm, Nat.sub_add_cancel mac_le]

  let some bytes ← openEasy (cipher.data.cast this) cipher.nonce.data.cast key.data.cast
    | return .refused
  let some msg := String.fromUTF8? bytes.toArray
    | return .mangled bytes.toArray
  let .ok json := Json.parse msg
    | return .unknown msg

  return fromJson? (α := α) json |>.mapError (DecryptError.invalidJson json)

open FFI Box in
def encryptTo [ToJson α] (key : SharedKey τ Curve25519HSalsa20) (msg : α) : CryptoM τ (CipherText XSalsa20Poly1305) := do
  let nonce ← mkFreshNonce (spec := XSalsa20Poly1305)
  let data := toJson msg |>.compress.toUTF8.toVector
  let cipher ← easyAfternm data nonce.data.cast (key.data.cast (by native_decide))
  return {
    nonce
    size := cipher.size
    data := cipher
    shapeOf_mac_le_size := by
      have : XSalsa20Poly1305.shapeOf `mac = MACBYTES := by native_decide
      rw [this]
      exact Nat.le_add_right MACBYTES (toJson msg).compress.toUTF8.size
  }

open FFI Box in
def decryptFrom? [FromJson α] (key : SharedKey τ Curve25519HSalsa20) (cipher : CipherText XSalsa20Poly1305) : CryptoM τ (DecryptResult α) := do
  have : cipher.size = MACBYTES + (cipher.size - MACBYTES) := by
    have mac_le : XSalsa20Poly1305.shapeOf `mac ≤ cipher.size := cipher.shapeOf_mac_le_size
    have : XSalsa20Poly1305.shapeOf `mac = MACBYTES := by native_decide
    rw [this] at mac_le
    rw [Nat.add_comm, Nat.sub_add_cancel mac_le]

  let some bytes ← openEasyAfternm (cipher.data.cast this) cipher.nonce.data.cast (key.data.cast (by native_decide))
    | return .refused
  let some msg := String.fromUTF8? bytes.toArray
    | return .mangled bytes.toArray
  let .ok json := Json.parse msg
    | return .unknown msg

  return fromJson? (α := α) json |>.mapError (DecryptError.invalidJson json)

open FFI Box in
def encryptAnon? [ToJson α] (theirs : PublicKey Curve25519) (msg : α) : CryptoM τ (Option (SealedCipherText XSalsa20Poly1305)) := do
  let nonce ← mkFreshNonce (spec := XSalsa20Poly1305)
  let data := toJson msg |>.compress.toUTF8.toVector
  let some cipher ← easyAnonymous (τ := τ) data theirs.data.cast | return none
  return some {
    size := cipher.size
    data := cipher.cast (by rfl)
    shapeOf_seal_le_size := by
      have : XSalsa20Poly1305.shapeOf `seal = SEALBYTES := by native_decide
      rw [this]
      exact Nat.le_add_right SEALBYTES (toJson msg).compress.toUTF8.size
  }

open FFI Box in
def decryptAnon? [FromJson α] (keys : KeyPair τ Curve25519) (cipher : SealedCipherText XSalsa20Poly1305) : CryptoM τ (DecryptResult α) := do
  have : cipher.size = SEALBYTES + (cipher.size - SEALBYTES) := by
    have seal_le : XSalsa20Poly1305.shapeOf `seal ≤ cipher.size := cipher.shapeOf_seal_le_size
    have : XSalsa20Poly1305.shapeOf `seal = SEALBYTES := by native_decide
    rw [this] at seal_le
    rw [Nat.add_comm, Nat.sub_add_cancel seal_le]

  let some bytes ← openAnonymous (cipher.data.cast this) keys.pkey.data.cast (keys.skey.data.cast (by native_decide))
    | return .refused
  let some msg := String.fromUTF8? bytes.toArray
    | return .mangled bytes.toArray
  let .ok json := Json.parse msg
    | return .unknown msg

  return fromJson? (α := α) json |>.mapError (DecryptError.invalidJson json)

open FFI Aead in
def encryptFst [ToJson α] [ToJson β] (key : SymmKey τ XChaCha20) (msg : α × β) : CryptoM τ (CipherText XChaCha20Poly1305 × Json) := do
  let nonce ← mkFreshNonce (spec := XChaCha20Poly1305)
  let data := toJson msg.1 |>.compress.toUTF8.toVector
  let ad := toJson msg.2
  let cipher ← Aead.encrypt data ad.compress.toUTF8.toVector nonce.data.cast key.data.cast
  let cipher := {
    nonce
    size := cipher.size
    data := cipher
    shapeOf_mac_le_size := by
      have : XChaCha20Poly1305.shapeOf `mac = ABYTES := by native_decide
      rw [this]
      exact Nat.le_add_right ABYTES (toJson msg.1).compress.toUTF8.size
  }
  return (cipher, ad)

open FFI Aead in
def decryptFst? [FromJson α] [FromJson β] (key : SymmKey τ XChaCha20) (cipher : CipherText XChaCha20Poly1305 × Json) : CryptoM τ (DecryptResult (α × β)) := do
  have : cipher.1.size = ABYTES + (cipher.1.size - ABYTES) := by
    have mac_le : XChaCha20Poly1305.shapeOf `mac ≤ cipher.1.size := cipher.1.shapeOf_mac_le_size
    have : XChaCha20Poly1305.shapeOf `mac = ABYTES := by native_decide
    rw [this] at mac_le
    rw [Nat.add_comm, Nat.sub_add_cancel mac_le]

  let .ok b := fromJson? (α := β) cipher.2
    | return .refused

  let some bytes ← Aead.decrypt (cipher.1.data.cast this) cipher.2.compress.toUTF8.toVector cipher.1.nonce.data.cast key.data.cast
    | return .refused
  let some msg := String.fromUTF8? bytes.toArray
    | return .mangled bytes.toArray
  let .ok json := Json.parse msg
    | return .unknown msg

  return fromJson? (α := α) json |>.map (·, b) |>.mapError (DecryptError.invalidJson json)

open FFI Aead in
def encryptSnd [ToJson α] [ToJson β] (key : SymmKey τ XChaCha20) (msg : α × β) : CryptoM τ (Json × CipherText XChaCha20Poly1305) := do
  let nonce ← mkFreshNonce (spec := XChaCha20Poly1305)
  let data := toJson msg.2 |>.compress.toUTF8.toVector
  let ad := toJson msg.1
  let cipher ← Aead.encrypt data ad.compress.toUTF8.toVector nonce.data.cast key.data.cast
  let cipher := {
    nonce
    size := cipher.size
    data := cipher
    shapeOf_mac_le_size := by
      have : XChaCha20Poly1305.shapeOf `mac = ABYTES := by native_decide
      rw [this]
      exact Nat.le_add_right ABYTES (toJson msg.2).compress.toUTF8.size
  }
  return (ad, cipher)

open FFI Aead in
def decryptSnd? [FromJson α] [FromJson β] (key : SymmKey τ XChaCha20) (cipher : Json × CipherText XChaCha20Poly1305) : CryptoM τ (DecryptResult (α × β)) := do
  have : cipher.2.size = ABYTES + (cipher.2.size - ABYTES) := by
    have mac_le : XChaCha20Poly1305.shapeOf `mac ≤ cipher.2.size := cipher.2.shapeOf_mac_le_size
    have : XChaCha20Poly1305.shapeOf `mac = ABYTES := by native_decide
    rw [this] at mac_le
    rw [Nat.add_comm, Nat.sub_add_cancel mac_le]

  let .ok a := fromJson? (α := α) cipher.1
    | return .refused

  let some bytes ← Aead.decrypt (cipher.2.data.cast this) cipher.1.compress.toUTF8.toVector cipher.2.nonce.data.cast key.data.cast
    | return .refused
  let some msg := String.fromUTF8? bytes.toArray
    | return .mangled bytes.toArray
  let .ok json := Json.parse msg
    | return .unknown msg

  return fromJson? (α := β) json |>.map (a, ·) |>.mapError (DecryptError.invalidJson json)

def loadSecret {kind : Name} {X : {σ : Type} → Sodium σ → (spec : Spec) → [spec.HasValidShape kind] → Type} [spec.HasValidShape kind]
    (key : SymmKey τ XSalsa20) (file : System.FilePath)
    (lift : SecureVector τ spec[kind] → X τ spec) : CryptoM τ (X τ spec) := do
  let data ← SecureVector.ofFile key.data file spec[kind]
  return lift data

def loadSeed (key : SymmKey τ XSalsa20) (file : System.FilePath) [spec.HasValidShape `seed] : CryptoM τ (Seed τ spec) :=
  loadSecret key file (fun data => ⟨data.cast (by simp [USize.ofNatLT_eq_ofNat]; congr)⟩)

def loadSecretKey (key : SymmKey τ XSalsa20) (file : System.FilePath) : CryptoM τ (SecretKey τ Curve25519) :=
  loadSecret key file (fun data => ⟨data.cast⟩)

def loadSymmKey (key : SymmKey τ XSalsa20) (file : System.FilePath) : CryptoM τ (SymmKey τ XSalsa20) :=
  loadSecret key file (fun data => ⟨data.cast⟩)

def loadSession (key : SymmKey τ XSalsa20) (fileRx : System.FilePath) (fileTx : System.FilePath) : CryptoM τ (Session τ Curve25519Blake2b) := do
  let rx ← loadSecret key fileTx (fun data => ⟨data.cast (by simp [USize.ofNatLT_eq_ofNat]; congr)⟩)
  let tx ← loadSecret key fileRx (fun data => ⟨data.cast (by simp [USize.ofNatLT_eq_ofNat]; congr)⟩)
  return ⟨rx, tx⟩

def withMetaKeyFromFile (key : SymmKey τ XSalsa20) (file : System.FilePath)
    (x : {σ : Type} → (τ : Sodium σ) → CryptoM τ α) : CryptoM τ α := do
  let st ← read
  let mkey : SymmKey τ Blake2b ← loadSecret key file (fun data => ⟨data.cast⟩)
  show MetaM α from Meta.withNewMCtxDepth do
    x τ {st with mkey}

end Sodium.Crypto
