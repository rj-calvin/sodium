/-
Type-safe SecretStream cryptography operations using the CryptoM monad.

This module provides high-level abstractions that combine Lean's Stream interface
with LibSodium's secret stream AEAD operations, ensuring proper state management
and type safety.
-/
import Batteries.Data.ByteArray
import Init.Data.Stream
import Sodium.FFI.SecretStream
import Sodium.Crypto.Monad
import Sodium.Crypto.Types
import Sodium.Crypto.Utils

open Lean

namespace Sodium.Crypto.SecretStream

open Utils

abbrev SecretStreamSecretKey := SecretKey SecretStreamSpec
abbrev SecretStreamMac := Mac SecretStreamSpec
abbrev SecretStreamAuthTag := AuthTag SecretStreamSpec
abbrev SecretStreamHeader := StreamHeader SecretStreamSpec
abbrev SecretStreamTaggedCipherText := TaggedCipherText SecretStreamSpec
abbrev SecretStreamMessage := StreamMessage SecretStreamSpec

inductive Direction where
  | push : Direction
  | pull : Direction
  deriving BEq, Inhabited, DecidableEq

inductive MessageTag where
  | message : MessageTag
  | push : MessageTag
  | rekey : MessageTag
  | final : MessageTag
  deriving BEq, Inhabited, DecidableEq

def MessageTag.toUInt8 : MessageTag → UInt8
  | .message => FFI.SECRETSTREAM_XCHACHA20POLY1305_TAG_MESSAGE
  | .push => FFI.SECRETSTREAM_XCHACHA20POLY1305_TAG_PUSH
  | .rekey => FFI.SECRETSTREAM_XCHACHA20POLY1305_TAG_REKEY
  | .final => FFI.SECRETSTREAM_XCHACHA20POLY1305_TAG_FINAL

def MessageTag.fromUInt8 : UInt8 → Option MessageTag
  | x =>
    if x = FFI.SECRETSTREAM_XCHACHA20POLY1305_TAG_MESSAGE then some .message
    else if x = FFI.SECRETSTREAM_XCHACHA20POLY1305_TAG_PUSH then some .push
    else if x = FFI.SECRETSTREAM_XCHACHA20POLY1305_TAG_REKEY then some .rekey
    else if x = FFI.SECRETSTREAM_XCHACHA20POLY1305_TAG_FINAL then some .final
    else none

structure SecretStreamState (dir : Direction) where
  state : match dir with
    | .push => FFI.PushState
    | .pull => FFI.PullState

abbrev PushState := SecretStreamState .push
abbrev PullState := SecretStreamState .pull

variable {α : Type}

def genKey : CryptoM SecretStreamSecretKey := do
  let keyBytes ← FFI.keygen
  if h : keyBytes.size = SecretStreamSpec.secretKeyBytes then
    return ⟨keyBytes, h⟩
  else
    throwMessage m!"invariant failed in {decl_name%}"

def initPush (key : SecretStreamSecretKey) : CryptoM (PushState × SecretStreamHeader) := do
  let (state, headerBytes) ← FFI.initPush key
  if h : headerBytes.size = SecretStreamSpec.headerBytes then
    let header := ⟨headerBytes, h⟩
    return (⟨state⟩, header)
  else
    throwMessage m!"invariant failed in {decl_name%}"

def initPull (key : SecretStreamSecretKey) (header : SecretStreamHeader) : CryptoM PullState := do
  let state ← FFI.initPull key header
  return ⟨state⟩

def push (state : PushState) (message : SecretStreamMessage) (additionalData : Option ByteArray := none) (tag : MessageTag := .message) : CryptoM SecretStreamTaggedCipherText := do
  let cipherBytes ← FFI.push state.state message additionalData tag.toUInt8

  if h : cipherBytes.size = message.bytes.size + SecretStreamSpec.tagBytes then
    return ⟨cipherBytes, by omega⟩
  else
    throwMessage m!"invariant failed in {decl_name%}: unexpected ciphertext size"

def pull (state : PullState) (ciphertext : SecretStreamTaggedCipherText) (additionalData : Option ByteArray := none) : CryptoM (ByteArray × MessageTag) := do
  let (plaintext, tagByte) ← FFI.pull state.state ciphertext.bytes additionalData
  match MessageTag.fromUInt8 tagByte with
  | some tag => return (plaintext, tag)
  | none => throwMessage m!"invalid tag received: {tagByte}"

def rekey (state : PushState) : CryptoM Unit := do
  FFI.rekey state.state

structure StreamEncoder where
  state : PushState
  header : SecretStreamHeader

structure StreamDecoder where
  state : PullState

namespace StreamEncoder

def new (key : SecretStreamSecretKey) : CryptoM StreamEncoder := do
  let (state, header) ← initPush key
  return ⟨state, header⟩

private partial def chunk (data : ByteArray) : List SecretStreamMessage :=
  if h : data.size ≤ SecretStreamSpec.messageMaxBytes then [⟨data, h⟩]
  else
    let hd := data.extract 0 SecretStreamSpec.messageMaxBytes
    let rest := data.extract SecretStreamSpec.messageMaxBytes data.size
    ⟨hd, by simp only [hd, ByteArray.size_extract]; omega⟩ :: chunk rest

def next (encoder : StreamEncoder) (chunk : SecretStreamMessage) (tag : MessageTag := .message) (additionalData : Option ByteArray := none) : CryptoM SecretStreamTaggedCipherText := do
  push encoder.state chunk additionalData tag

def encrypt (encoder : StreamEncoder) (data : ByteArray) (finalTag : MessageTag := .final) (additionalData : Option ByteArray := none) : CryptoM (List SecretStreamTaggedCipherText) := do
  if data.isEmpty then return []
  let chunks := chunk data
  chunks.mapIdxM fun i data => do
    let tag := if i = chunks.length - 1 then finalTag else .message
    encoder.next data tag additionalData

end StreamEncoder

namespace StreamDecoder

def new (key : SecretStreamSecretKey) (header : SecretStreamHeader) : CryptoM StreamDecoder := do
  let state ← initPull key header
  return ⟨state⟩

def next (decoder : StreamDecoder) (ciphertext : SecretStreamTaggedCipherText) (additionalData : Option ByteArray := none) : CryptoM (ByteArray × MessageTag) := do
  pull decoder.state ciphertext additionalData

def decrypt (decoder : StreamDecoder) (ciphertexts : List SecretStreamTaggedCipherText) (additionalData : Option ByteArray := none) : CryptoM (Except Exception ByteArray) := do
  let mut result := ByteArray.empty
  let mut finalTag : Option MessageTag := none

  for ciphertext in ciphertexts do
    try
      let (plaintext, tag) ← decoder.next ciphertext additionalData
      result := result ++ plaintext
      finalTag := some tag
      if tag = .final then break
    catch e =>
      return .error e

  return .ok result

end StreamDecoder

instance [ToJson α] : ToStream α ByteArray := ⟨(toJson · |>.compress.toUTF8)⟩

def encrypt [ToStream α ByteArray] (encoder : StreamEncoder) (data : α) (finalTag : MessageTag := .final) (additionalData : Option ByteArray := none) : CryptoM (List SecretStreamTaggedCipherText) :=
  encoder.encrypt (toStream data) finalTag additionalData

def decrypt (decoder : StreamDecoder) (ciphertexts : List SecretStreamTaggedCipherText) (additionalData : Option ByteArray := none) : CryptoM (Except Exception ByteArray) :=
  decoder.decrypt ciphertexts additionalData

structure DecryptingStream where
  decoder : StreamDecoder
  ciphertexts : List SecretStreamTaggedCipherText
  additionalData : Option ByteArray := none

instance : ForIn CryptoM DecryptingStream (ByteArray × MessageTag) where
  forIn stream init f := do
    let mut acc := init
    for ciphertext in stream.ciphertexts do
      try
        let (plaintext, tag) ← stream.decoder.next ciphertext stream.additionalData
        match ← f (plaintext, tag) acc with
        | .done a => return a
        | .yield a =>
          acc := a
          if tag = .final then return acc
      catch _ =>
        return acc
    return acc

def stream (decoder : StreamDecoder) (ciphertexts : List SecretStreamTaggedCipherText) (additionalData : Option ByteArray := none) : DecryptingStream :=
  ⟨decoder, ciphertexts, additionalData⟩

end Sodium.Crypto.SecretStream
