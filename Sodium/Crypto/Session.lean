import Sodium.Crypto.Monad

open Lean

namespace Sodium.Crypto

open FFI KeyExch

def SessionSpec : Spec where
  name := `session.curve25519
  seedBytes := SEEDBYTES
  publicKeyBytes := PUBLICKEYBYTES
  secretKeyBytes := SECRETKEYBYTES
  sessionKeyBytes := SESSIONKEYBYTES

variable {σ : Type} {τ : Sodium σ}

@[simp]
theorem session_meta_secret_key_compat :
    ∀ key : SecretKey τ MetaSpec, key.bytes.size = SessionSpec.secretKeyBytes := by
  intro k
  exact k.size_eq_secret_key_bytes

@[simp]
theorem session_meta_public_key_compat :
    ∀ key : PublicKey MetaSpec, key.bytes.size = SessionSpec.publicKeyBytes := by
  intro k
  exact k.size_eq_public_key_bytes

@[simp]
theorem session_meta_session_key_compat :
    ∀ key : SessionKey τ MetaSpec, key.bytes.size = SessionSpec.sessionKeyBytes := by
  intro k
  exact k.size_eq_session_key_bytes

@[simp]
theorem session_meta_seed_compat :
    ∀ key : Seed τ MetaSpec, key.bytes.size = SessionSpec.seedBytes := by
  intro k
  exact k.size_eq_seed_bytes

instance : MetaSpecSupport PublicKey SessionSpec where
  withSpec x := ⟨x.bytes, by exact x.size_eq_public_key_bytes⟩
  liftSpec x := ⟨x.bytes, by simp⟩

instance : MetaSpecSupport (SecretKey τ) SessionSpec where
  withSpec x := ⟨x.bytes, by exact x.size_eq_secret_key_bytes⟩
  liftSpec x := ⟨x.bytes, by simp⟩

instance : MetaSpecSupport (KeyPair τ) SessionSpec where
  withSpec x := ⟨withSpec x.public, withSpec x.secret⟩
  liftSpec x := ⟨liftSpec x.public, liftSpec x.secret⟩

instance : MetaSpecSupport (SessionKey τ) SessionSpec where
  withSpec x := ⟨x.bytes, by exact x.size_eq_session_key_bytes⟩
  liftSpec x := ⟨x.bytes, by simp⟩

instance : MetaSpecSupport (Session τ) SessionSpec where
  withSpec x := ⟨withSpec x.rx, withSpec x.tx⟩
  liftSpec x := ⟨liftSpec x.rx, liftSpec x.tx⟩

instance : MetaSpecSupport (Seed τ) SessionSpec where
  withSpec x := ⟨x.bytes, by exact x.size_eq_seed_bytes⟩
  liftSpec x := ⟨x.bytes, by simp⟩

def mkFreshKeyPair : CryptoM τ (KeyPair τ SessionSpec) := do
  let (pub, sec) ← keypair τ
  if h : pub.size = SessionSpec.publicKeyBytes ∧ sec.size = SessionSpec.secretKeyBytes then
    return ⟨⟨pub, h.1⟩, ⟨sec, h.2⟩⟩
  else throwInvariantFailure

def mkStaleKeyPair (seed : Seed τ SessionSpec) : CryptoM τ (KeyPair τ SessionSpec) := do
  let (pub, sec) ← seedKeypair τ seed.bytes
  if h : pub.size = SessionSpec.publicKeyBytes ∧ sec.size = SessionSpec.secretKeyBytes then
    return ⟨⟨pub, h.1⟩, ⟨sec, h.2⟩⟩
  else throwInvariantFailure

def newServerSession? (keys : KeyPair τ SessionSpec) (client : PeerId SessionSpec) : CryptoM τ (Option (Session τ SessionSpec)) := do
  let some (rx, tx) ← serverSessionKeys τ keys.public.bytes keys.secret.bytes client.pkey.bytes
    | return none
  if h : rx.size = SessionSpec.sessionKeyBytes ∧ tx.size = SessionSpec.sessionKeyBytes then
    return some ⟨⟨rx, h.1⟩, ⟨tx, h.2⟩⟩
  else throwInvariantFailure

def newClientSession? (keys : KeyPair τ SessionSpec) (server : PeerId SessionSpec) : CryptoM τ (Option (Session τ SessionSpec)) := do
  let some (rx, tx) ← clientSessionKeys τ keys.public.bytes keys.secret.bytes server.pkey.bytes
    | return none
  if h : rx.size = SessionSpec.sessionKeyBytes ∧ tx.size = SessionSpec.sessionKeyBytes then
    return some ⟨⟨rx, h.1⟩, ⟨tx, h.2⟩⟩
  else throwInvariantFailure

end Sodium.Crypto
