import Sodium.Server.Types

open Lean Sodium Crypto

namespace Sodium.Server

export Lean.Server (ServerTask)

variable {α β σ : Type} {τ : Sodium σ} {m : {σ : Type} → Sodium σ → Type → Type}

def Server (α : Type) := Message (BaseIO (ServerTask α))

namespace Server

def ephemeral (x : BaseIO (ServerTask α)) : Server α :=
  ⟨.ephemeral, fun _ => x⟩

def addressed (x : Message.B .addressed → BaseIO (ServerTask α)) : Server α :=
  ⟨.addressed, x⟩

def anonymous (x : Message.B .anonymous → BaseIO (ServerTask α)) : Server α :=
  ⟨.anonymous, x⟩

end Server

def ServerT (τ : Sodium σ) (m : {σ : Type} → Sodium σ → Type → Type) (α : Type) :=
  Message (m τ α)

namespace ServerT

instance : Inhabited (ServerT τ m α) := by unfold ServerT; infer_instance

def ephemeral (x : m τ α) : ServerT τ m α :=
  ⟨.ephemeral, fun _ => x⟩

def anonymous (x : Message.B .anonymous → m τ α) : ServerT τ m α :=
  ⟨.anonymous, x⟩

def addressed (x : Message.B .addressed → m τ α) : ServerT τ m α :=
  ⟨.addressed, x⟩

protected def pure [Pure (m τ)] (a : α) : ServerT τ m α :=
  ephemeral (Pure.pure a)

protected def map [Functor (m τ)] (f : α → β) : ServerT τ m α → ServerT τ m β :=
  Message.map (Functor.map f)

protected def bind [h : Monad (m τ)] [MonadError (m τ)] (st : ServerT τ m α) (f : α → ServerT τ m β) : ServerT τ m β :=
  match st with | ⟨ka, k⟩ => by refine ⟨ka, ?_⟩; exact fun x => do
    bind (k x) fun a => match f a with
      | ⟨.ephemeral, k⟩ => k ()
      | ⟨msg, k⟩ =>
        if h : msg = ka then k (h ▸ x)
        else throwError toMessageData (@toJson MessageKind _ msg)

instance [Functor (m τ)] : Functor (ServerT τ m) where map := ServerT.map

instance [Monad (m τ)] [MonadError (m τ)] : Monad (ServerT τ m) where
  pure := ServerT.pure
  bind := ServerT.bind

variable [Monad (m τ)] [MonadError (m τ)]

def run (x : Message.Id) : ServerT τ m α → m τ α
  | ⟨.ephemeral, k⟩ => k ()
  | ⟨a, k⟩ =>
    if h : a = x.1 then k (h ▸ x.2)
    else throwError toMessageData (@toJson MessageKind _ a)

end ServerT

structure ServerContext (τ : Sodium σ) where
  session : Option (Session τ Curve25519Blake2b) := none

abbrev ServerM (τ : Sodium σ) := ReaderT (ServerContext τ) (ServerT τ CryptoM)

namespace ServerM

def toCryptoM (msg : Message.Id) (x : ServerM τ α) (session : Option (Session τ Curve25519Blake2b) := none) : CryptoM τ α :=
  ServerT.run msg (x {session})

def recv? (α : Type) [Encodable α] : ServerM τ (Decrypt (Verified α))
  | { session := none } => ServerT.anonymous fun x => do decryptAnon? x
  | { session := some session } => ServerT.addressed fun x =>
    session.withReceiver do
      match ← decrypt? x with
      | .accepted a => return .accepted (← sign a)
      | .almost json => return .almost json
      | .unknown str => return .unknown str
      | .mangled bytes => return .mangled bytes
      | .refused => return .refused

def recv! (α : Type) [Encodable α] : ServerM τ (Verified α) := do
  let .accepted x ← recv? α | default
  return x

def recvFrom? (α : Type) [Encodable α] (pkey : MachineId) : ServerM τ (Decrypt (Verified α))
  | { session := none } => ServerT.anonymous fun x => do
    let some key ← newSharedKey? pkey | throwSpecViolation Curve25519 `publickey
    withSharedKey key do decryptAnon? x
  | { session := some session } => ServerT.addressed fun x => do
    session.withReceiver do
      let some key ← newSharedKey? pkey | throwSpecViolation Curve25519 `publickey
      match ← decryptFrom? key x with
      | .accepted a => return .accepted (← sign a)
      | .almost json => return .almost json
      | .unknown str => return .unknown str
      | .mangled bytes => return .mangled bytes
      | .refused => return .refused

def recvFrom! (α : Type) [Encodable α] (pkey : MachineId) : ServerM τ (Verified α) := do
  let .accepted x ← recvFrom? α pkey | default
  return x

def send {α : Type} [Encodable α] (a : α) : Server β → ServerM τ (ServerTask β)
  | ⟨.ephemeral, k⟩, _ => ServerT.ephemeral do k ()
  | ⟨.addressed, k⟩, {session} => ServerT.ephemeral do (session.map (·.withTransmitter)).getD id do k (← encrypt a)
  | _, _ => default

def sendTo {α : Type} [Encodable α] (pkey : MachineId) (a : α) : Server β → ServerM τ (ServerTask β)
  | ⟨.ephemeral, k⟩, _ => ServerT.ephemeral do k ()
  | ⟨.anonymous, k⟩, {session} => ServerT.ephemeral do (session.map (·.withTransmitter)).getD id do
    let some msg ← encryptAnon? pkey a | throwSpecViolation Curve25519 `publickey
    k msg
  | ⟨.addressed, k⟩, {session} => ServerT.ephemeral do (session.map (·.withTransmitter)).getD id do
    let some key ← newSharedKey? pkey | throwSpecViolation Curve25519 `publickey
    k (← encryptTo key a)
  | _, _ => default

end ServerM

end Sodium.Server
