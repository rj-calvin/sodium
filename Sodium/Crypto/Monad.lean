import Sodium.Crypto.Types

open Lean Std Sodium

namespace Sodium.Crypto

variable {spec : Spec}

variable {α β σ : Type}

namespace Context

instance : Coe (ByteVector 8) (Context Blake2b) where
  coe x := x.cast

def ofString (x : String) (h : x.utf8ByteSize = 8 := by rfl) : Context Blake2b :=
  let ctx := x.toUTF8
  have : ctx.size = Blake2b[`context] := by
    simp [blake2b_context_eq]
    rw [String.size_toUTF8, h]
    rfl
  ctx.toVector.cast this

inductive Paranoia
  | normal
  | moderate
  | severe
  deriving TypeName, Inhabited, BEq, DecidableEq, Ord, Repr, ToJson, FromJson

def Paranoia.toString : Paranoia → String
  | .normal => "standard"
  | .moderate => "cautious"
  | .severe => "paranoid"

instance : ToString Paranoia := ⟨Paranoia.toString⟩

@[simp]
theorem paranoia_eq : ∀ p : Paranoia, p.toString.utf8ByteSize = 8 := by
  intro _
  simp [Paranoia.toString]
  split <;> rfl

@[coe]
def Paranoia.asContext : Paranoia → Context Blake2b := fun p =>
  Context.ofString p.toString (by simp only [paranoia_eq])

instance : Coe Paranoia (Context Blake2b) := ⟨Paranoia.asContext⟩

instance : Inhabited (Context Blake2b) where
  default := Paranoia.normal

end Context

private structure EntropyState (τ : Sodium σ) where
  entropy : EntropyVector τ
  nonces : NameMap (Σ s, NonceId s) := ∅

structure CryptoContext (τ : Sodium σ) where
  private mk ::
  private mtx : Mutex (EntropyState τ)
  mkey : SymmKey τ Blake2b
  ctx : Context Blake2b

inductive CryptoMessage
  | specViolation (spec : Spec) (kind : Name)
  | insufficientEntropy (bytes : Nat)
  deriving Inhabited

@[coe] def CryptoMessage.toMessageData : CryptoMessage → MessageData
  | .specViolation s k => m!"spec violation: shape of kind {k} not supported by {s.name}"
  | .insufficientEntropy bytes => m!"insufficient entropy (expected at least {bytes} bytes)"

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

namespace CryptoM

register_option crypto.entropyBytes : Nat := {
  defValue := 24 * 256
  descr := "The number of random bytes to allocate for entropy."
}

open FFI KeyDeriv in
def toMetaM (x : {σ : Type} → (τ : Sodium σ) → CryptoM τ α) (ctx : Context Blake2b := default) : MetaM α := do
  let τ ← init Unit
  let entropy ← EntropyVector.new (τ := τ) (crypto.entropyBytes.get (← getOptions)).toUSize
  let mkey ← keygen (τ := τ)
  let mtx ← Mutex.new {entropy}
  x τ {mtx, ctx, mkey := mkey.cast}

def currContext : CryptoM τ (Context Blake2b) := return (← read).ctx
def withContext (x : CryptoM τ α) (ctx : Context Blake2b := default) : CryptoM τ α := do x {← read with ctx}

open Meta in
def withMetaKey (mkey : SymmKey τ Blake2b) (x : CryptoM τ α) : CryptoM τ α := do
  withNewMCtxDepth (x {← read with mkey})

def mkFreshNonce [h : spec.HasValidShape `nonce] : CryptoM τ (Nonce spec) := do
  let mtx := (← read).mtx
  mtx.atomically fun ref => do
    let st ← ref.get
    match st.nonces.find? spec.name with
    | some ⟨spec', stale⟩ =>
      if eq_shape : spec'.shapeOf `nonce = spec[`nonce] then
        haveI : spec'.HasValidShape `nonce := by
          rw [Spec.has_valid_shape_iff, eq_shape]
          exact h.shape_is_valid
        let shape := (stale.get this).succ
        let nonce := shape.cast eq_shape
        let nonces := st.nonces.insert spec.name ⟨spec, ⟨fun _ => nonce⟩⟩
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

    let (nonce, entropy) ← do
      if entropy.size - entropy.off < shape then
        let entropy ← entropy.refresh
      entropy.extract shape

    if size_eq : nonce.size = shape then
      let nonce : Nonce spec := ⟨nonce, size_eq⟩
      let nonces := nonces.insert spec.name ⟨spec, ⟨fun _ => nonce⟩⟩
      return (nonce, {st with nonces, entropy})
    else throwInsufficientEntropy shape

instance : MonadNameGenerator (CryptoM τ) where
  getNGen := do
    let nonce ← mkFreshNonce (spec := UniqId)
    let ctx := (← read).ctx.toArray
    let ctx := match String.fromUTF8? ctx with
      | some name => Name.str UniqId.name name
      | _ => Name.str .anonymous ctx.toBase64
    return {namePrefix := ctx, idx := nonce.cast.toUInt64LE.toNat}
  setNGen _ :=
    return () -- not allowed, so we ignore.

end CryptoM

export CryptoM (mkFreshNonce currContext withContext withMetaKey)

def mkFreshKey {X : {σ : Type} → Sodium σ → (spec : Spec) → [spec.HasValidShape `symmkey] → Type} [spec.HasValidShape `symmkey]
    (lift : SecretVector τ spec[`symmkey] → X τ spec) : CryptoM τ (X τ spec) := do
  let key ← SecretVector.new spec[`symmkey]
  return lift key

open FFI KeyDeriv in
def mkStaleKey {X : {σ : Type} → Sodium σ → (spec : Spec) → [spec.HasValidShape `symmkey] → Type} [spec.HasValidShape `symmkey]
    (lift : SecretVector τ spec[`symmkey] → X τ spec) : CryptoM τ (X τ spec) := do
  let {mkey, ctx, ..} ← read
  let mctx ← getMCtx
  let key ← derive spec[`symmkey] mctx.depth ctx.cast mkey.cast
  return lift key

def withNewMetaKey (x : CryptoM τ α) : CryptoM τ α := do
  withMetaKey (← mkStaleKey (·.cast)) x

open FFI KeyExch in
def mkFreshKeys : CryptoM τ (KeyPair τ Curve25519) := do
  let (pkey, skey) ← keypair
  return ⟨pkey.cast, skey.cast⟩

open FFI KeyExch in
def mkStaleKeys : CryptoM τ (KeyPair τ Curve25519) := do
  let key : SymmKey _ Blake2b ← mkStaleKey (·.cast)
  let (pkey, skey) ← seedKeypair (key.cast (by native_decide))
  return ⟨pkey.cast, skey.cast⟩

open FFI Sign in
def mkFreshSignature : CryptoM τ (KeyPair τ Ed25519) := do
  let (pkey, skey) ← keypair
  return ⟨pkey.cast, skey.cast⟩

open FFI Sign in
def mkStaleSignature : CryptoM τ (KeyPair τ Ed25519) := do
  let key : SymmKey _ Blake2b ← mkStaleKey (·.cast)
  let (pkey, skey) ← seedKeypair (key.cast (by native_decide))
  return ⟨pkey.cast, skey.cast⟩

open FFI Box in
def newSharedKey? (key : PublicKey Curve25519) (keys : Option (KeyPair τ Curve25519) := none) : CryptoM τ (Option (SymmKey τ Curve25519HSalsa20)) := do
  let {skey, ..} ← keys.getDM mkStaleKeys
  let some key ← beforenm key.cast (skey.cast (by simp [USize.ofNatLT_eq_ofNat]; congr))
    | return none
  return some (key.cast (by native_decide))

abbrev withSharedKey (key : SymmKey τ Curve25519HSalsa20) : CryptoM τ α → CryptoM τ α :=
  withMetaKey (key.cast (by native_decide))

open FFI KeyExch in
def newSession? (key : PublicKey Curve25519) (keys : Option (KeyPair τ Curve25519) := none) (client := false) : CryptoM τ (Option (Session τ Curve25519Blake2b)) := do
  let {pkey, skey} ← keys.getDM mkStaleKeys
  let some sess ← (if client then clientSessionKeys else serverSessionKeys) pkey.cast skey.cast key.cast
    | return none
  return some ⟨sess.1.cast (by native_decide), sess.2.cast (by native_decide)⟩

abbrev withSessionKey (key : SymmKey τ Curve25519Blake2b) : CryptoM τ α → CryptoM τ α :=
  withMetaKey (key.cast (by native_decide))

abbrev Session.withReceiver (sess : Session τ Curve25519Blake2b) : CryptoM τ α → CryptoM τ α :=
  withSessionKey sess.rx

abbrev Session.withTransmitter (sess : Session τ Curve25519Blake2b) : CryptoM τ α → CryptoM τ α :=
  withSessionKey sess.tx

open FFI SecretBox in
def encrypt [Encodable α] (msg : α) (key : Option (SymmKey τ XSalsa20) := none) : CryptoM τ (CipherText XSalsa20Poly1305) := do
  let key ← key.getDM (mkStaleKey (·.cast))
  let nonce ← mkFreshNonce (spec := XSalsa20Poly1305)
  let data := encode msg |>.compress.toUTF8.toVector
  let cipher ← easy data nonce.cast key.cast
  return {
    nonce
    size := cipher.size
    data := cipher
    mac_le_size := by
      have : XSalsa20Poly1305.shapeOf `mac = MACBYTES := by native_decide
      simp [getElem]
      rw [this]
      exact Nat.le_add_right MACBYTES _
  }

open FFI SecretBox in
def decrypt? [Encodable α] (cipher : CipherText XSalsa20Poly1305) (key : Option (SymmKey τ XSalsa20) := none) : CryptoM τ (Decrypt α) := do
  have : cipher.size = MACBYTES + (cipher.size - MACBYTES) := by
    have mac_le : XSalsa20Poly1305.shapeOf `mac ≤ cipher.size := cipher.mac_le_size
    have : XSalsa20Poly1305.shapeOf `mac = MACBYTES := by native_decide
    rw [this] at mac_le
    rw [Nat.add_comm, Nat.sub_add_cancel mac_le]

  let key ← key.getDM (mkStaleKey (·.cast))
  let some bytes ← openEasy (cipher.data.cast this) cipher.nonce.cast key.cast
    | return .refused
  let some msg := String.fromUTF8? bytes.toArray
    | return .mangled bytes.toArray
  let .ok json := Json.parse msg
    | return .unknown msg
  let some a := decode? (α := α) json
    | return .almost json
  return .accepted a

open FFI Box in
def encryptTo [Encodable α] (key : SymmKey τ Curve25519HSalsa20) (msg : α) : CryptoM τ (CipherText XSalsa20Poly1305) := do
  let nonce ← mkFreshNonce (spec := XSalsa20Poly1305)
  let data := encode msg |>.compress.toUTF8.toVector
  let cipher ← easyAfternm data nonce.cast (key.cast (by native_decide))
  return {
    nonce
    size := cipher.size
    data := cipher
    mac_le_size := by
      have : XSalsa20Poly1305.shapeOf `mac = MACBYTES := by native_decide
      simp [getElem]
      rw [this]
      exact Nat.le_add_right MACBYTES _
  }

open FFI Box in
def decryptFrom? [Encodable α] (key : SymmKey τ Curve25519HSalsa20) (cipher : CipherText XSalsa20Poly1305) : CryptoM τ (Decrypt α) := do
  have : cipher.size = MACBYTES + (cipher.size - MACBYTES) := by
    have mac_le : XSalsa20Poly1305.shapeOf `mac ≤ cipher.size := cipher.mac_le_size
    have : XSalsa20Poly1305.shapeOf `mac = MACBYTES := by native_decide
    rw [this] at mac_le
    rw [Nat.add_comm, Nat.sub_add_cancel mac_le]

  let some bytes ← openEasyAfternm (cipher.data.cast this) cipher.nonce.cast (key.cast (by native_decide))
    | return .refused
  let some msg := String.fromUTF8? bytes.toArray
    | return .mangled bytes.toArray
  let .ok json := Json.parse msg
    | return .unknown msg
  let some a := decode? (α := α) json
    | return .almost json
  return .accepted a

open FFI Box in
def encryptAnon? [Encodable α] (key : PublicKey Curve25519) (msg : α) : CryptoM τ (Option (SealedCipherText Curve25519XSalsa20Poly1305)) := do
  let nonce ← mkFreshNonce (spec := XSalsa20Poly1305)
  let data := encode msg |>.compress.toUTF8.toVector
  let some cipher ← easyAnonymous (τ := τ) data key.cast | return none
  return some {
    size := cipher.size
    data := cipher.cast (by rfl)
    seal_le_size := by
      have : Curve25519XSalsa20Poly1305.shapeOf `publickey + Curve25519XSalsa20Poly1305.shapeOf `mac = SEALBYTES := by native_decide
      simp [getElem]
      rw [this]
      exact Nat.le_add_right SEALBYTES _
  }

open FFI Box in
def decryptAnon? [Encodable α] (cipher : SealedCipherText Curve25519XSalsa20Poly1305) (keys : Option (KeyPair τ Curve25519) := none) : CryptoM τ (Decrypt α) := do
  have : cipher.size = SEALBYTES + (cipher.size - SEALBYTES) := by
    have seal_le : Curve25519XSalsa20Poly1305.shapeOf `publickey + Curve25519XSalsa20Poly1305.shapeOf `mac ≤ cipher.size := cipher.seal_le_size
    have : Curve25519XSalsa20Poly1305.shapeOf `publickey + Curve25519XSalsa20Poly1305.shapeOf `mac = SEALBYTES := by native_decide
    rw [this] at seal_le
    rw [Nat.add_comm, Nat.sub_add_cancel seal_le]

  let {pkey, skey} ← keys.getDM mkStaleKeys
  let some bytes ← openAnonymous (cipher.data.cast this) pkey.cast (skey.cast (by native_decide))
    | return .refused
  let some msg := String.fromUTF8? bytes.toArray
    | return .mangled bytes.toArray
  let .ok json := Json.parse msg
    | return .unknown msg
  let some a := decode? (α := α) json
    | return .almost json
  return .accepted a

open FFI Aead in
def encryptFst [Encodable α] [ToJson β] (msg : α × β) (key : Option (SymmKey τ XChaCha20) := none) : CryptoM τ (CipherText XChaCha20Poly1305 × Json) := do
  let nonce ← mkFreshNonce (spec := XChaCha20Poly1305)
  let key ← key.getDM (mkStaleKey (·.cast))
  let data := encode msg.1 |>.compress.toUTF8.toVector
  let ad := toJson msg.2
  let cipher ← Aead.encrypt data ad.compress.toUTF8.toVector nonce.cast key.cast
  let cipher := {
    nonce
    size := cipher.size
    data := cipher
    mac_le_size := by
      have : XChaCha20Poly1305.shapeOf `mac = ABYTES := by native_decide
      simp [getElem]
      rw [this]
      exact Nat.le_add_right ABYTES _
  }
  return (cipher, ad)

open FFI Aead in
def decryptFst? [Encodable α] [FromJson β] (cipher : CipherText XChaCha20Poly1305 × Json) (key : Option (SymmKey τ XChaCha20) := none) : CryptoM τ (Decrypt (α × β)) := do
  have : cipher.1.size = ABYTES + (cipher.1.size - ABYTES) := by
    have mac_le : XChaCha20Poly1305.shapeOf `mac ≤ cipher.1.size := cipher.1.mac_le_size
    have : XChaCha20Poly1305.shapeOf `mac = ABYTES := by native_decide
    rw [this] at mac_le
    rw [Nat.add_comm, Nat.sub_add_cancel mac_le]

  let .ok b := fromJson? (α := β) cipher.2
    | return .refused

  let key ← key.getDM (mkStaleKey (·.cast))
  let some bytes ← decrypt (cipher.1.data.cast this) cipher.2.compress.toUTF8.toVector cipher.1.nonce.cast key.cast
    | return .refused
  let some msg := String.fromUTF8? bytes.toArray
    | return .mangled bytes.toArray
  let .ok json := Json.parse msg
    | return .unknown msg
  let some a := decode? (α := α) json
    | return .almost json
  return .accepted (a, b)

open FFI Aead in
def encryptSnd [ToJson α] [Encodable β] (msg : α × β) (key : Option (SymmKey τ XChaCha20) := none) : CryptoM τ (Json × CipherText XChaCha20Poly1305) := do
  let nonce ← mkFreshNonce (spec := XChaCha20Poly1305)
  let key ← key.getDM (mkStaleKey (·.cast))
  let data := encode msg.2 |>.compress.toUTF8.toVector
  let ad := toJson msg.1
  let cipher ← Aead.encrypt data ad.compress.toUTF8.toVector nonce.cast key.cast
  let cipher := {
    nonce
    size := cipher.size
    data := cipher
    mac_le_size := by
      have : XChaCha20Poly1305.shapeOf `mac = ABYTES := by native_decide
      simp [getElem]
      rw [this]
      exact Nat.le_add_right ABYTES _
  }
  return (ad, cipher)

open FFI Aead in
def decryptSnd? [FromJson α] [Encodable β] (cipher : Json × CipherText XChaCha20Poly1305) (key : Option (SymmKey τ XChaCha20) := none) : CryptoM τ (Decrypt (α × β)) := do
  have : cipher.2.size = ABYTES + (cipher.2.size - ABYTES) := by
    have mac_le : XChaCha20Poly1305.shapeOf `mac ≤ cipher.2.size := cipher.2.mac_le_size
    have : XChaCha20Poly1305.shapeOf `mac = ABYTES := by native_decide
    rw [this] at mac_le
    rw [Nat.add_comm, Nat.sub_add_cancel mac_le]

  let .ok a := fromJson? (α := α) cipher.1
    | return .refused

  let key ← key.getDM (mkStaleKey (·.cast))
  let some bytes ← Aead.decrypt (cipher.2.data.cast this) cipher.1.compress.toUTF8.toVector cipher.2.nonce.cast key.cast
    | return .refused
  let some msg := String.fromUTF8? bytes.toArray
    | return .mangled bytes.toArray
  let .ok json := Json.parse msg
    | return .unknown msg
  let some b := decode? (α := β) json
    | return .almost json
  return .accepted (a, b)

open FFI Sign in
def verify [Encodable α] (msg : SignedJson Ed25519) : Decrypt α := Id.run do
  let {json, sig, pkey} := msg
  let bytes := json.compress.toUTF8.toVector
  unless verifyDetached sig.cast bytes pkey.cast do
    return .refused
  let some a := decode? (α := α) json
    | return .almost json
  return .accepted a

structure Verified (α : Type) [Encodable α] extends SignedJson Ed25519 where
  val : α
  verified : verify toSignedJson = .accepted val

attribute [simp] Verified.verified

namespace Verified

variable [Encodable α]

instance : CoeOut (Verified α) α := ⟨Verified.val⟩

instance encodable : Encodable (Verified α) :=
  Encodable.ofLeftInj
    (·.toSignedJson)
    (fun json => match h : verify (α := α) json with | .accepted a => some ⟨json, a, h⟩ | _ => none)
    fun x => by
      obtain ⟨_, _, _⟩ := x
      simp only
      split
      . simp only [Option.some.injEq, mk.injEq, true_and]
        simp_all only [Decrypt.accepted.injEq]
      . rename_i x
        nomatch x _

end Verified

protected def Verified.Id (α : Type) := Σ h, @Verified α h

@[coe] protected def Verified.id {h : Encodable α} (x : @Verified α h) : Verified.Id α := ⟨h, x⟩
@[coe] protected def Verified.Id.out : (h : Verified.Id α) → @Verified α h.fst := Sigma.snd

@[simp] theorem Verified.id_out_eq {h : Encodable α} : ∀ x : @Verified α h, x.id.out = x := fun _ => rfl

open FFI Sign in
def sign [Encodable α] (msg : α) (keys : Option (KeyPair τ Ed25519) := none) : CryptoM τ (Verified α) := do
  let keys ← keys.getDM mkStaleSignature
  let json := encode msg
  let sig ← signDetached json.compress.toUTF8.toVector keys.skey.cast
  let sig := ⟨json, sig.cast, keys.pkey⟩
  match h : verify sig with
  | .accepted a => return ⟨sig, a, h⟩
  | _ => throwSpecViolation Ed25519 `publickey

def loadSecret? {kind : Name} {X : {σ : Type} → Sodium σ → (spec : Spec) → [spec.HasValidShape kind] → Type} [spec.HasValidShape kind]
    (key : SymmKey τ XSalsa20) (file : System.FilePath) (lift : SecretVector τ spec[kind] → X τ spec) : CryptoM τ (Option (X τ spec)) := do
  try
    let data ← SecretVector.ofFile key file spec[kind]
    return some (lift data)
  catch _ => return none

def loadSecretKey? [spec.HasValidShape `secretkey] (file : System.FilePath) : CryptoM τ (Option (SecretKey τ spec)) := do
  let key : SymmKey _ XSalsa20 ← mkStaleKey (·.cast)
  loadSecret? key file (·.cast (by simp only [getElem, USize.ofNatLT_eq_ofNat]; congr))

def loadSymmKey? [spec.HasValidShape `symmkey] (file : System.FilePath) : CryptoM τ (Option (SymmKey τ spec)) := do
  let key : SymmKey _ XSalsa20 ← mkStaleKey (·.cast)
  loadSecret? key file (·.cast (by simp only [getElem, USize.ofNatLT_eq_ofNat]; congr))

def storeSecret {kind : Name} {X : {σ : Type} → Sodium σ → (spec : Spec) → [spec.HasValidShape kind] → Type} [spec.HasValidShape kind]
    (key : SymmKey τ XSalsa20) (file : System.FilePath) (item : X τ spec) (extract : X τ spec → SecretVector τ spec[kind]) : CryptoM τ Unit := do
  let data := extract item
  data.toFile key file

def storeSecretKey [spec.HasValidShape `secretkey] (item : SecretKey τ spec) (file : System.FilePath) : CryptoM τ Unit := do
  let key : SymmKey _ XSalsa20 ← mkStaleKey (·.cast)
  storeSecret key file item (·.cast (by simp only [getElem, USize.ofNatLT_eq_ofNat]; congr))

def storeSymmKey [spec.HasValidShape `symmkey] (item : SymmKey τ spec) (file : System.FilePath) : CryptoM τ Unit := do
  let key : SymmKey _ XSalsa20 ← mkStaleKey (·.cast)
  storeSecret key file item (·.cast (by simp only [getElem, USize.ofNatLT_eq_ofNat]; congr))

unsafe def readSecret {X : {σ : Type} → Sodium σ → (spec : Spec) → [spec.HasValidShape `symmkey] → Type} [spec.HasValidShape `symmkey]
    (lift : SecretVector τ spec[`symmkey] → X τ spec) (prompt := s!"{spec.name}.{spec[`symmkey] }") : CryptoM τ (X τ spec) := do
  let key ← SecretVector.ofStdin prompt spec[`symmkey]
  return lift key

unsafe def withMetaKeyFromInput (x : CryptoM τ α) : CryptoM τ α := do
  withMetaKey (← readSecret (·.cast)) x

end Sodium.Crypto
