import Sodium.Crypto.Monad
import Sodium.Data.PFunctor
import Sodium.Lean.Syntax

open Lean Sodium Crypto

variable {σ : Type} {τ : Sodium σ}

namespace Sodium

abbrev MachineId := Verified (PublicKey Curve25519)

abbrev AgentId := Verified (PublicKey Ed25519)

structure PeerId extends AgentId where
  self_signed : pkey = val

namespace PeerId

def new (keys : Option (KeyPair τ Ed25519) := none) : CryptoM τ PeerId := do
  let keys ← keys.getDM mkStaleSignature
  let sig ← sign keys.pkey keys
  if h : sig.pkey = sig.val then return ⟨sig, h⟩
  throwSpecViolation Ed25519 decl_name%

instance encodable : Encodable PeerId :=
  Encodable.ofEquiv {x : AgentId // x.pkey = x.val} {
    push := fun ⟨x, h⟩ => ⟨x, h⟩
    pull := fun ⟨x, h⟩ => ⟨x, h⟩
  }

class Signed {α : Type} [Encodable α] (p : PeerId) (x : Verified α) : Prop where
  signed : p.pkey = x.pkey

end PeerId

structure FriendId (τ : Sodium σ) extends AgentId where
  keys : KeyPair τ Ed25519
  peer : PeerId
  peer_rfl : peer.pkey = val
  signed_with_held_secret : keys.pkey = pkey

namespace FriendId

def new (peer : PeerId) (keys : Option (KeyPair τ Ed25519) := none) : CryptoM τ (FriendId τ) := do
  let keys ← keys.getDM mkStaleSignature
  let sig ← sign peer.pkey keys
  if h : keys.pkey = sig.pkey ∧ peer.pkey = sig.val then return ⟨sig, keys, peer, h.2, h.1⟩
  throwSpecViolation Ed25519 decl_name%

class Signed {α : Type} [Encodable α] (f : FriendId τ) (x : Verified α) : Prop where
  signed : f.pkey = x.pkey

end FriendId

structure MetaId (τ : Sodium σ) extends PeerId, FriendId τ

namespace MetaId

def new (keys : Option (KeyPair τ Ed25519) := none) : CryptoM τ (MetaId τ) := do
  let keys ← keys.getDM mkStaleSignature
  let peer ← PeerId.new keys
  if h : keys.pkey = peer.pkey then return ⟨peer, keys, peer, peer.self_signed, h⟩
  throwSpecViolation Ed25519 decl_name%

class Signed {α : Type} [Encodable α] (m : MetaId τ) (x : Verified α) : Prop where
  signed : m.pkey = x.pkey

end MetaId

inductive MessageName
  | terminal
  | anonymous
  | addressed
  | «partial»
  | ephemeral
  deriving Inhabited, BEq, DecidableEq, Repr, TypeName, ToJson, FromJson

namespace MessageName

def ofFin : Fin 5 → MessageName
  | 0 => .terminal
  | 1 => .anonymous
  | 2 => .addressed
  | 3 => .partial
  | 4 => .ephemeral

@[coe] def toFin : MessageName → Fin 5
  | .terminal => 0
  | .anonymous => 1
  | .addressed => 2
  | .partial => 3
  | .ephemeral => 4

@[simp] theorem ofFin_toFin_eq : ∀ k, ofFin (toFin k) = k := by intro k; cases k <;> rfl

instance : Coe MessageName (Fin 5) := ⟨toFin⟩

instance encodable : Encodable MessageName :=
  Encodable.ofEquiv _ {
    push := toFin
    pull := ofFin
    push_pull_eq k := ofFin_toFin_eq k
  }

end MessageName

inductive MessageKind where
  | terminal : MessageKind
  | anonymous : MessageKind
  | ephemeral : MessageKind
  | addressed : MessageKind
  | «partial» : PublicKey Curve25519 → Header XChaCha20Poly1305 → MessageKind
  deriving DecidableEq

namespace MessageKind

def name : MessageKind → MessageName
  | .terminal => .terminal
  | .anonymous => .anonymous
  | .ephemeral => .ephemeral
  | .addressed => .addressed
  | .partial _ _ => .partial

def Shape := Fin 4 ⊕ PublicKey Curve25519 × Header XChaCha20Poly1305

def toShape : MessageKind → Shape
  | .terminal => .inl 0
  | .anonymous => .inl 1
  | .ephemeral => .inl 2
  | .addressed => .inl 3
  | .partial x y => .inr (x, y)

def ofShape : Shape → MessageKind
  | .inl 0 => .terminal
  | .inl 1 => .anonymous
  | .inl 2 => .ephemeral
  | .inl 3 => .addressed
  | .inr (x, y) => .partial x y

instance Shape.encodable : Encodable Shape := by unfold Shape; infer_instance

instance encodable : Encodable MessageKind :=
  Encodable.ofEquiv _ { push := toShape, pull := ofShape }

end MessageKind

def Message : PFunctor where
  A := MessageKind
  B | .terminal => Empty
    | .anonymous => SealedCipherText Curve25519XSalsa20Poly1305
    | .addressed => CipherText XSalsa20Poly1305
    | .partial _ _ => List (CipherChunk XChaCha20Poly1305)
    | .ephemeral => Unit

namespace Message

instance : Coe Message.A MessageKind := ⟨id⟩
instance : DecidableEq Message.A := by unfold Message; infer_instance

instance {α} : Inhabited (Message α) := ⟨⟨.terminal, Empty.elim⟩⟩
instance : Inhabited Message.Id := ⟨⟨.ephemeral, ()⟩⟩

instance encodable : Encodable Message.A := by unfold Message; infer_instance

instance : IsEmpty (Message.B .terminal) := by unfold Message; infer_instance

instance : ∀ a, HEq (Message.B a) (Message.B a) := fun _ => by simp only [heq_eq_eq]

instance encodable_pi : ∀ a, Encodable (Message.B a) := fun a => by
  have : Encodable Empty := Empty.encodable
  cases a <;> unfold Message <;> simp only <;> infer_instance

instance encodable_id : Encodable Message.Id := by infer_instance

end Sodium.Message
