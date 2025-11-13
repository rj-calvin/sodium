import Sodium.Data.Chunk
import Sodium.Crypto.Monad

open Lean Sodium FFI SecretStream

namespace Sodium.Crypto

deriving instance ToJson, FromJson for Tag

variable {α ε σ : Type} {τ : Sodium σ}

structure SecretEncoder (τ : Sodium σ) where
  private mk ::
  header : Header XChaCha20Poly1305
  stream : SecretStream τ

namespace SecretEncoder

def new (key : Option (SymmKey τ XChaCha20) := none) : CryptoM τ (SecretEncoder τ) := do
  let key ← key.getDM (mkStaleKey (.up ·.cast))
  let (stream, header) ← streamInitPush (key.cast (by simp [USize.ofNatLT_eq_ofNat]; congr))
  return {stream, header := header.cast}

def push [ToChunks α] (encoder : SecretEncoder τ) (x : α) (final := false) : CryptoM τ (List (CipherChunk XChaCha20Poly1305)) := do
  have : XChaCha20Poly1305.shapeOf `mac = ABYTES := by native_decide
  let chunks := toChunks x |>.map (String.toUTF8 ∘ Json.compress)
  let some last := chunks.getLast?
    | return ∅
  let messages ← chunks.dropLast.mapM fun chunk => do
    let cipher ← streamPush encoder.stream chunk.toVector .empty .message
    return ⟨cipher.size, cipher, by simp [this]⟩
  let terminal ← streamPush encoder.stream last.toVector .empty (if final then .final else .push)
  return messages ++ [⟨terminal.size, terminal, by simp [this]⟩]

def rekey (encoder : SecretEncoder τ) : CryptoM τ (List (CipherChunk XChaCha20Poly1305)) := do
  have : XChaCha20Poly1305.shapeOf `mac = ABYTES := by native_decide
  let cipher ← streamPush encoder.stream (json% null).compress.toUTF8.toVector .empty .rekey
  streamRekey encoder.stream
  return [⟨cipher.size, cipher, by simp [this]⟩]

end SecretEncoder

structure SecretDecoder (τ : Sodium σ) where
  private mk ::
  buffer : IO.Ref (Array Json)
  stream : SecretStream τ

namespace SecretDecoder

def new (header : Header XChaCha20Poly1305) (key : Option (SymmKey τ XChaCha20) := none) : CryptoM τ (SecretDecoder τ) := do
  let key ← key.getDM (mkStaleKey (.up ·.cast))
  let stream ← streamInitPull header.cast (key.cast (by simp [USize.ofNatLT_eq_ofNat]; congr))
  let buffer ← IO.mkRef #[]
  return {stream, buffer}

def pull [FromChunks α] (decoder : SecretDecoder τ) (src : List (CipherChunk XChaCha20Poly1305)) : CryptoM τ (Array α × Option DecryptError) := do
  let mut results : Array α := #[]
  let mut error : Option DecryptError := none

  for chunk in src do
    if error.isSome then break

    have : chunk.size = ABYTES + (chunk.size - ABYTES) := by
      have mac_le : XChaCha20Poly1305.shapeOf `mac ≤ chunk.size := chunk.mac_le_size
      have : XChaCha20Poly1305.shapeOf `mac = ABYTES := by native_decide
      rw [this] at mac_le
      rw [Nat.add_comm, Nat.sub_add_cancel mac_le]

    let some (bytes, tag) ← streamPull decoder.stream (chunk.data.cast this) .empty
      | error := some .refused
        break

    let some msg := String.fromUTF8? bytes.toArray
      | error := some (.invalidEncoding bytes.toArray)
        break

    let .ok json := Json.parse msg
      | error := some (.invalidString msg)
        break

    match tag with
    | .rekey => streamRekey decoder.stream
    | .message => decoder.buffer.modify (·.push json)
    | .push | .final =>
      let acc := (← decoder.buffer.swap #[]).push json
      match fromChunks? acc.toList with
      | some item => results := results.push item
      | _ => error := some (.invalidJson (Json.arr acc))

    if tag = .final then break

  return (results, error)

end SecretDecoder

end Sodium.Crypto
