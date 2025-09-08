import Sodium.Data.AsyncList
import Sodium.Data.Chunk
import Sodium.Crypto.Monad

open Lean Sodium FFI SecretStream

namespace Sodium.Crypto

deriving instance ToJson, FromJson for Tag

variable {α ε σ : Type} {τ : Sodium σ}

structure SecretEncoder (τ : Sodium σ) where
  private mk ::
  closed : IO.Ref Bool
  header : Header XChaCha20Poly1305
  stream : SecureStream τ

namespace SecretEncoder

def new : CryptoM τ (SecretEncoder τ) := do
  let key : SymmKey τ XChaCha20 ← mkFreshKey (·.cast)
  let (stream, header) ← streamInitPush (key.cast (by simp [USize.ofNatLT_eq_ofNat]; congr))
  let closed ← IO.mkRef false
  return {stream, header := header.cast, closed}

def isClosed (encoder : SecretEncoder τ) : CryptoM τ Bool :=
  encoder.closed.get

def close (encoder : SecretEncoder τ) : CryptoM τ Unit :=
  encoder.closed.set true

def push [ToChunks α] (encoder : SecretEncoder τ) (x : α) (prio : Task.Priority := .dedicated) (final := false) : CryptoM τ (IO.AsyncList IO.Error (CipherChunk XChaCha20Poly1305)) := do
  have : XChaCha20Poly1305.shapeOf `mac = ABYTES := by native_decide
  if ← encoder.closed.get then return ∅
  let chunks := toChunks x |>.map (String.toUTF8 ∘ Json.compress)
  let some last := chunks.getLast?
    | return ∅
  let messages ← chunks.dropLast.foldIO (prio := prio) fun chunk => do
    let cipher ← streamPush encoder.stream chunk.toVector .empty .message
    return ⟨cipher.size, cipher, by simp [this]⟩
  let terminal ← Server.ServerTask.IO.asTask <| do
    let cipher ← streamPush encoder.stream last.toVector .empty (if final then .final else .push)
    return ⟨cipher.size, cipher, by simp [this]⟩
  if final then encoder.closed.set true
  return messages.append <| .delayed <| terminal.mapCheap (·.map pure)

def rekey (encoder : SecretEncoder τ) : CryptoM τ (IO.AsyncList IO.Error (CipherChunk XChaCha20Poly1305)) := do
  have : XChaCha20Poly1305.shapeOf `mac = ABYTES := by native_decide
  if ← encoder.closed.get then return ∅
  let cipher ← streamPush encoder.stream (json% null).compress.toUTF8.toVector .empty .rekey
  streamRekey encoder.stream
  return .ofList [⟨cipher.size, cipher, by simp [this]⟩]

end SecretEncoder

structure SecretDecoder (τ : Sodium σ) where
  private mk ::
  closed : IO.Ref Bool
  buffer : IO.Ref (List Json)
  stream : SecureStream τ

namespace SecretDecoder

def new (header : Header XChaCha20Poly1305) : CryptoM τ (SecretDecoder τ) := do
  let key : SymmKey τ XChaCha20 ← mkFreshKey (·.cast)
  let stream ← streamInitPull header.cast (key.cast (by simp [USize.ofNatLT_eq_ofNat]; congr))
  let buffer ← IO.mkRef []
  let closed ← IO.mkRef false
  return {stream, buffer, closed}

def isClosed (decoder : SecretDecoder τ) : CryptoM τ Bool :=
  decoder.closed.get

def close (decoder : SecretDecoder τ) : CryptoM τ Unit :=
  decoder.closed.set true

def pull [FromChunks α] (decoder : SecretDecoder τ) (src : List (CipherChunk XChaCha20Poly1305)) : CryptoM τ (List α × Option DecryptError) := do
  if ← decoder.closed.get then return ([], some .refused)
  let mut results : List α := []
  let mut error : Option DecryptError := none

  for chunk in src do
    if ← decoder.closed.get then break
    if error.isSome then break

    have : chunk.size = ABYTES + (chunk.size - ABYTES) := by
      have mac_le : XChaCha20Poly1305.shapeOf `mac ≤ chunk.size := chunk.shapeOf_mac_le_size
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
    | .rekey =>
      streamRekey decoder.stream
    | .message => decoder.buffer.modify fun acc => acc ++ [json]
    | .push =>
      let acc := (← decoder.buffer.swap []) ++ [json]
      match fromChunks? acc with
      | .ok item => results := results ++ [item]
      | .error msg => error := some (.invalidJson (Json.arr acc.toArray) msg)
    | .final =>
      decoder.closed.set true
      let acc := (← decoder.buffer.swap []) ++ [json]
      match fromChunks? acc with
      | .ok item => results := results ++ [item]
      | .error msg => error := some (.invalidJson (Json.arr acc.toArray) msg)

  return (results, error)

end SecretDecoder

end Sodium.Crypto
