import Lean.Server.AsyncList

open Lean Server

universe u v

namespace IO.AsyncList

variable {ε δ : Type u} {α β γ : Type v}

partial def mapCheap (f : α → β) : AsyncList ε α → AsyncList ε β
  | nil => nil
  | cons hd tl => cons (f hd) (tl.mapCheap f)
  | delayed tl => delayed <| tl.mapCheap fun
    | .ok tl => .ok (tl.mapCheap f)
    | .error e => .error e

partial def mapCostly (f : α → β) : AsyncList ε α → AsyncList ε β
  | nil => nil
  | cons hd tl => cons (f hd) (tl.mapCostly f)
  | delayed tl => delayed <| tl.mapCostly fun
    | .ok tl => .ok (tl.mapCostly f)
    | .error e => .error e

partial def mapError (f : ε → δ) : AsyncList ε α → AsyncList δ α
  | nil => nil
  | cons hd tl => cons hd (tl.mapError f)
  | delayed tl => delayed <| tl.mapCheap fun
    | .ok tl => .ok (tl.mapError f)
    | .error e => .error (f e)

partial def filter (p : α → Bool) : AsyncList ε α → AsyncList ε α
  | nil => nil
  | cons hd tl =>
      if p hd then
        cons hd (tl.filter p)
      else
        tl.filter p
  | delayed tl => delayed <| tl.mapCheap fun
    | .ok tl => .ok (tl.filter p)
    | .error e => .error e

partial def take (n : Nat) : AsyncList ε α → AsyncList ε α
  | nil => nil
  | cons hd tl =>
      if n = 0 then
        nil
      else
        cons hd (tl.take (n - 1))
  | delayed tl =>
      if n = 0 then
        nil
      else
        delayed <| tl.mapCheap fun
          | .ok tl => .ok (tl.take n)
          | .error e => .error e

partial def drop (n : Nat) : AsyncList ε α → AsyncList ε α
  | nil => nil
  | cons hd tl =>
      if n = 0 then
        cons hd tl
      else
        tl.drop (n - 1)
  | delayed tl =>
      if n = 0 then
        delayed tl
      else
        delayed <| tl.mapCheap fun
          | .ok tl => .ok (tl.drop n)
          | .error e => .error e

partial def append : AsyncList ε α → AsyncList ε α → AsyncList ε α
  | nil, ys => ys
  | cons hd tl, ys => cons hd (tl.append ys)
  | delayed tl, ys => delayed <| tl.mapCheap fun
    | .ok tl => .ok (tl.append ys)
    | .error e => .error e

partial def flatMap (f : α → AsyncList ε β) : AsyncList ε α → AsyncList ε β
  | nil => nil
  | cons hd tl => (f hd).append (tl.flatMap f)
  | delayed tl => delayed <| tl.mapCheap fun
    | .ok tl => .ok (tl.flatMap f)
    | .error e => .error e

partial def zipWith (f : α → β → γ) : AsyncList ε α → AsyncList ε β → AsyncList ε γ
  | nil, _ => nil
  | _, nil => nil
  | cons hd₁ tl₁, cons hd₂ tl₂ => cons (f hd₁ hd₂) (tl₁.zipWith f tl₂)
  | delayed tl₁, xs => delayed <| tl₁.mapCheap fun
    | .ok tl₁ => .ok (tl₁.zipWith f xs)
    | .error e => .error e
  | xs, delayed tl₂ => delayed <| tl₂.mapCheap fun
    | .ok tl₂ => .ok (xs.zipWith f tl₂)
    | .error e => .error e

partial def foldCheap (f : β → α → ServerTask β) (init : β) : AsyncList ε α → ServerTask (Except ε β)
  | nil => .pure (.ok init)
  | cons hd tl => (f init hd).bindCheap (tl.foldCheap f)
  | delayed tl => tl.bindCheap fun
    | .ok tl => tl.foldCheap f init
    | .error e => .pure (.error e)

partial def foldCostly (f : β → α → ServerTask β) (init : β) : AsyncList ε α → ServerTask (Except ε β)
  | nil => .pure (.ok init)
  | cons hd tl => (f init hd).bindCostly (tl.foldCostly f)
  | delayed tl => tl.bindCostly fun
    | .ok tl => tl.foldCostly f init
    | .error e => .pure (.error e)

def addTask {α : Type} (tl : AsyncList IO.Error α) (x : IO α) (prio : Task.Priority := default) : BaseIO (AsyncList IO.Error α) :=
  return .delayed <| Task.asServerTask <| ← IO.asTask (prio := prio) <| return .cons (← x) tl

protected def pure (a : α) : AsyncList ε α := cons a nil
protected def bind (x : AsyncList ε α) (f : α → AsyncList ε β) : AsyncList ε β := flatMap f x

instance : Inhabited (AsyncList ε α) := ⟨nil⟩

instance : Coe (List α) (AsyncList ε α) := ⟨ofList⟩

instance : EmptyCollection (AsyncList ε α) := ⟨nil⟩

instance : Append (AsyncList ε α) := ⟨append⟩

instance : Functor (AsyncList ε) where
  map := mapCheap

instance : Pure (AsyncList ε) := ⟨AsyncList.pure⟩
instance : Bind (AsyncList ε) := ⟨AsyncList.bind⟩

instance : Monad (AsyncList ε) where
  pure := pure
  bind := bind

end IO.AsyncList

namespace List

def foldIO {α : Type v} {β : Type} (f : α → IO β) (xs : List α) (prio : Task.Priority := default) : BaseIO (IO.AsyncList IO.Error β) :=
  xs.foldrM (init := ∅) fun a tl => tl.addTask (f a) prio

end List
