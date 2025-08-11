import Sodium.FFI.SecretBox
import Sodium.Crypto.Monad

open Lean

namespace Sodium.Crypto

open FFI SecretBox

def SecretBoxSpec : Spec where
  name := `xsalsa20poly1305
  secretKeyBytes := KEYBYTES
  nonceBytes := NONCEBYTES
  macBytes := MACBYTES

variable {α σ : Type} {τ : Sodium σ}

def encrypt [ToJson α] (secretKey : SecretKey τ SecretBoxSpec) (message : α) : CryptoM τ (CipherText SecretBoxSpec) := do
  let nonce ← mkFreshNonceId SecretBoxSpec
  let data := toJson message |>.compress.toUTF8
  let cipher ← easy τ data nonce.bytes secretKey.bytes
  if h : cipher.size ≥ SecretBoxSpec.macBytes then
    return ⟨cipher, nonce, h⟩
  else throwInvariantFailure

def decrypt? [FromJson α] (secretKey : SecretKey τ SecretBoxSpec)
    (cipher : CipherText SecretBoxSpec) : CryptoM τ (Except DecryptError α) := do
  let some bytes ← openEasy τ cipher.bytes cipher.nonce.bytes secretKey.bytes
    | return .error .refused
  let some msg := String.fromUTF8? bytes | return .error (.invalidEncoding bytes)
  let .ok json := Json.parse msg | return .error (.invalidString msg)
  let .ok a := fromJson? json | return .error (.invalidJson json)
  return .ok a

namespace Detached

def encrypt [ToJson α] (secretKey : SecretKey τ SecretBoxSpec)
    (message : α) : CryptoM τ (DetachedCipherText SecretBoxSpec) := do
  let nonce ← mkFreshNonceId SecretBoxSpec
  let data := toJson message |>.compress.toUTF8
  let (cipher, mac) ← detached τ data nonce.bytes secretKey.bytes
  if h : mac.size = SecretBoxSpec.macBytes then
    return {bytes := cipher, mac := ⟨mac, h⟩, nonce}
  else throwInvariantFailure

def decrypt? [FromJson α] (secretKey : SecretKey τ SecretBoxSpec)
    (cipher : DetachedCipherText SecretBoxSpec) : CryptoM τ (Except DecryptError α) := do
  let some bytes ← openDetached τ cipher.bytes cipher.mac.bytes cipher.nonce.bytes secretKey.bytes
    | return .error .refused
  let some msg := String.fromUTF8? bytes | return .error (.invalidEncoding bytes)
  let .ok json := Json.parse msg | return .error (.invalidString msg)
  let .ok a := fromJson? json | return .error (.invalidJson json)
  return .ok a

end Detached

end Sodium.Crypto
