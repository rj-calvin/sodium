import Lean.Data.Json
import Sodium.Data.ByteArray

universe u

open Lean

variable {α : Type u}

class ToChunks (α : Type u) where
  toChunks : α → List Json

export ToChunks (toChunks)

instance [ToJson α] : ToChunks (List α) where
  toChunks xs := xs.map toJson

instance [ToJson α] : ToChunks (Array α) := ⟨toChunks ∘ Array.toList⟩

class FromChunks (α : Type u) where
  fromChunks? : List Json → Except String α

export FromChunks (fromChunks?)

class LawfulChunks (α : Type u) [ToChunks α] [FromChunks α] where
  chunksk : ∀ a, fromChunks? (α := α) (toChunks a) = .ok a

instance [FromJson α] : FromChunks (List α) where
  fromChunks?
    | [] => .ok []
    | chunks => chunks.mapM fromJson?

instance [FromJson α] : FromChunks (Array α) := ⟨fun xs => fromChunks? xs |>.map List.toArray⟩

namespace ByteArray

instance : ToChunks ByteArray where
  toChunks x := Id.run do
    if x.size ≤ 12288 then return [toJson x]
    let mut chunks : Array Json := #[]
    let mut cursor : ByteArray.Iterator := x.iter
    while !cursor.atEnd do
      let len := min 12288 cursor.remainingBytes
      let buf := cursor.array.extract cursor.pos (cursor.pos + len)
      chunks := chunks.push (toJson buf)
      cursor := cursor.forward len
    return chunks.toList

instance : FromChunks ByteArray where
  fromChunks?
    | [] => .ok .empty
    | chunks => do
      let capacity := chunks.length * 12288
      let mut buf := ByteArray.emptyWithCapacity capacity
      let mut idx := 0
      for chunk in chunks do
        match fromJson? (α := ByteArray) chunk with
        | .error e => throw e
        | .ok bytes =>
          buf := bytes.copySlice
            (srcOff := 0)
            (dest := buf)
            (destOff := idx)
            (len := bytes.size)
            (exact := idx + bytes.size ≤ capacity)
          idx := idx + bytes.size
      return buf

end ByteArray
