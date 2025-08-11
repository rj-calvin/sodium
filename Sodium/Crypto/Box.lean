import Lean.Data.Json
import Sodium.FFI.Box
import Sodium.Crypto.Monad

open Lean

namespace Sodium.Crypto

open FFI Box

def BoxSpec : Spec where
  name := `box.curve25519
  secretKeyBytes := SECRETKEYBYTES
  publicKeyBytes := PUBLICKEYBYTES
  nonceBytes := NONCEBYTES
  macBytes := MACBYTES
  seedBytes := SEEDBYTES
  sharedBytes := SHAREDBYTES
  sealBytes := SEALBYTES

variable {α σ : Type} {τ : Sodium σ}

@[simp]
theorem box_meta_secret_key_compat :
    ∀ key : SecretKey τ MetaSpec, key.bytes.size = BoxSpec.secretKeyBytes := by
  intro k
  exact k.size_eq_secret_key_bytes

@[simp]
theorem box_meta_public_key_compat :
    ∀ key : PublicKey MetaSpec, key.bytes.size = BoxSpec.publicKeyBytes := by
  intro k
  exact k.size_eq_public_key_bytes

@[simp]
theorem box_meta_seed_compat :
    ∀ key : Seed τ MetaSpec, key.bytes.size = BoxSpec.seedBytes := by
  intro k
  exact k.size_eq_seed_bytes

instance : MetaSpecSupport PublicKey BoxSpec where
  withSpec x := ⟨x.bytes, by exact x.size_eq_public_key_bytes⟩
  liftSpec x := ⟨x.bytes, by simp⟩

instance : MetaSpecSupport (SecretKey τ) BoxSpec where
  withSpec x := ⟨x.bytes, by exact x.size_eq_secret_key_bytes⟩
  liftSpec x := ⟨x.bytes, by simp⟩

instance : MetaSpecSupport (KeyPair τ) BoxSpec where
  withSpec x := ⟨withSpec x.public, withSpec x.secret⟩
  liftSpec x := ⟨liftSpec x.public, liftSpec x.secret⟩

instance : MetaSpecSupport (Seed τ) BoxSpec where
  withSpec x := ⟨x.bytes, by exact x.size_eq_seed_bytes⟩
  liftSpec x := ⟨x.bytes, by simp⟩

instance : MetaSpecSupport (SharedSecret τ) BoxSpec where
  withSpec x := ⟨x.bytes, by exact x.size_eq_shared_bytes⟩
  liftSpec x := ⟨x.bytes, by exact x.size_eq_shared_bytes⟩

def newSharedSecret? (keyPair : KeyPair τ BoxSpec) (peer : PeerId BoxSpec) : CryptoM τ (Option (SharedSecret τ BoxSpec)) := do
  let some shared ← beforenm τ peer.pkey.bytes keyPair.secret.bytes
    | return none
  if h : shared.size = BoxSpec.sharedBytes then
    return some ⟨shared, h⟩
  else throwInvariantFailure

def encryptTo? [ToJson α] (keyPair : KeyPair τ BoxSpec) (peer : PeerId BoxSpec) (message : α) : CryptoM τ (Option (CipherText BoxSpec)) := do
  let nonce ← mkFreshNonceId BoxSpec
  let data := toJson message |>.compress.toUTF8
  let some cipher ← easy τ data nonce.bytes peer.pkey.bytes keyPair.secret.bytes
    | return none
  if h : cipher.size ≥ BoxSpec.macBytes then
    return some ⟨cipher, nonce, h⟩
  else throwInvariantFailure

def encryptToShared [ToJson α] (secret : SharedSecret τ BoxSpec) (message : α) : CryptoM τ (CipherText BoxSpec) := do
  let nonce ← mkFreshNonceId BoxSpec
  let data := toJson message |>.compress.toUTF8
  let cipher ← easyAfternm τ data nonce.bytes secret.bytes
  if h : cipher.size ≥ BoxSpec.macBytes then
    return ⟨cipher, nonce, h⟩
  else throwInvariantFailure

def decryptFrom? [FromJson α] (keyPair : KeyPair τ BoxSpec) (peer : PeerId BoxSpec)
    (cipher : CipherText BoxSpec) : CryptoM τ (Except DecryptError α) := do
  let some bytes ← openEasy τ cipher.bytes cipher.nonce.bytes peer.pkey.bytes keyPair.secret.bytes
    | return .error .refused
  let some msg := String.fromUTF8? bytes | return .error (.invalidEncoding bytes)
  let .ok json := Json.parse msg | return .error (.invalidString msg)
  let .ok a := fromJson? json | return .error (.invalidJson json)
  return .ok a

def decryptFromShared? [FromJson α] (secret : SharedSecret τ BoxSpec)
    (cipher : CipherText BoxSpec) : CryptoM τ (Except DecryptError α) := do
  let some bytes ← openEasyAfternm τ cipher.bytes cipher.nonce.bytes secret.bytes
    | return .error .refused
  let some msg := String.fromUTF8? bytes | return .error (.invalidEncoding bytes)
  let .ok json := Json.parse msg | return .error (.invalidString msg)
  let .ok a := fromJson? json | return .error (.invalidJson json)
  return .ok a

def encryptDetachedTo? [ToJson α] (keyPair : KeyPair τ BoxSpec) (peer : PeerId BoxSpec)
    (message : α) : CryptoM τ (Option (DetachedCipherText BoxSpec)) := do
  let nonce ← mkFreshNonceId BoxSpec
  let data := toJson message |>.compress.toUTF8
  let some (cipher, mac) ← detached τ data nonce.bytes peer.pkey.bytes keyPair.secret.bytes
    | return .none
  if h : mac.size = BoxSpec.macBytes then
    return .some {bytes := cipher, mac := ⟨mac, h⟩, nonce}
  else throwInvariantFailure

namespace Detached

def decryptFrom? [FromJson α] (keyPair : KeyPair τ BoxSpec) (peer : PeerId BoxSpec)
    (cipher : DetachedCipherText BoxSpec) : CryptoM τ (Except DecryptError α) := do
  let some bytes ← openDetached τ cipher.bytes cipher.mac.bytes cipher.nonce.bytes peer.pkey.bytes keyPair.secret.bytes
    | return .error .refused
  let some msg := String.fromUTF8? bytes | return .error (.invalidEncoding bytes)
  let .ok json := Json.parse msg | return .error (.invalidString msg)
  let .ok a := fromJson? json | return .error (.invalidJson json)
  return .ok a

def encryptToShared [ToJson α] (secret : SharedSecret τ BoxSpec) (message : α) : CryptoM τ (DetachedCipherText BoxSpec) := do
  let nonce ← mkFreshNonceId BoxSpec
  let data := toJson message |>.compress.toUTF8
  let (cipher, mac) ← detachedAfternm τ data nonce.bytes secret.bytes
  if h : mac.size = BoxSpec.macBytes then
    return {bytes := cipher, mac := ⟨mac, h⟩, nonce}
  else throwInvariantFailure

def decryptFromShared? [FromJson α] (secret : SharedSecret τ BoxSpec)
    (cipher : DetachedCipherText BoxSpec) : CryptoM τ (Except DecryptError α) := do
  let some bytes ← openDetachedAfternm τ cipher.bytes cipher.mac.bytes cipher.nonce.bytes secret.bytes
    | return .error .refused
  let some msg := String.fromUTF8? bytes | return .error (.invalidEncoding bytes)
  let .ok json := Json.parse msg | return .error (.invalidString msg)
  let .ok a := fromJson? json | return .error (.invalidJson json)
  return .ok a

end Detached

def sealTo? [ToJson α] (peer : PeerId BoxSpec) (message : α) : CryptoM τ (Option (SealedCipherText BoxSpec)) := do
  let data := toJson message |>.compress.toUTF8
  let some sealed ← «seal» τ data peer.pkey.bytes
    | return none
  if h : sealed.size ≥ BoxSpec.sealBytes then
    return some ⟨sealed, h⟩
  else throwInvariantFailure

def unseal? [FromJson α] (keyPair : KeyPair τ BoxSpec) (sealed : SealedCipherText BoxSpec) : CryptoM τ (Except DecryptError α) := do
  let some bytes ← sealOpen τ sealed.bytes keyPair.public.bytes keyPair.secret.bytes
    | return .error .refused
  let some msg := String.fromUTF8? bytes | return .error (.invalidEncoding bytes)
  let .ok json := Json.parse msg | return .error (.invalidString msg)
  let .ok a := fromJson? json | return .error (.invalidJson json)
  return .ok a

end Sodium.Crypto
