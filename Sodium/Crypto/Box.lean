import Sodium.Theory.Curve25519
import Sodium.Data.Aead
import Sodium.Data.Core

namespace Sodium.Crypto

open Theory

def xsalsa20poly1305 : Aead where
  name := `xsalsa20poly1305
  keyBytes := 32
  nonceBytes := 24
  tagBytes := 16
  encrypt := XSalsa20Poly1305.encrypt
  decrypt? := XSalsa20Poly1305.decrypt?

def xchacha20poly1305 : Aead where
  name := `xchacha20poly1305
  keyBytes := 32
  nonceBytes := 24
  tagBytes := 16
  encrypt := XChaCha20Poly1305.encrypt
  decrypt? := XChaCha20Poly1305.decrypt?

def aegis256 : Aead where
  name := `aegis256
  keyBytes := 32
  nonceBytes := 32
  tagBytes := 32
  encrypt := Aegis256.encrypt
  decrypt? := Aegis256.decrypt?

def box : Box := dhBox Curve25519.spec xsalsa20poly1305 hsalsa20
def boxXchacha20poly1305 : Box := dhBox Curve25519.spec xchacha20poly1305 hchacha20
def boxRistretto255 : Box := dhBox Ristretto.spec.toDhFunction xchacha20poly1305 blake2b32

end Sodium.Crypto
