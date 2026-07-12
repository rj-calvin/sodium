import Sodium.Theory.Basic
import Sodium.Data.Aead
import Sodium.Data.Curve25519
import Sodium.Data.Ristretto255
import Sodium.Data.Core

namespace Sodium.Crypto

open Sodium.Theory

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

def curve25519 : DhFunction where
  name := `curve25519
  scalarBytes := 32
  pointBytes := 32
  mulBase := Curve25519.mulBase
  mul := Curve25519.mul

def ristretto255Order : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

def ristretto255 : PrimeOrderGroup where
  name := `ristretto255
  scalarBytes := 32
  pointBytes := 32
  uniformBytes := 64
  nonReducedBytes := 64
  mulBase := Ristretto255.mulBase
  mul := Ristretto255.mul
  add := Ristretto255.add
  sub := Ristretto255.sub
  fromUniform := Ristretto255.fromHash
  validPoint := Ristretto255.isValidPoint
  scalarReduced s :=
    decide (s.toByteArray.toList.foldr (fun b acc => b.toNat + 256 * acc) 0 < ristretto255Order)
  scalarReduce := Ristretto255.scalarReduce
  scalarAdd := Ristretto255.scalarAdd
  scalarMul := Ristretto255.scalarMul
  scalarNeg := Ristretto255.scalarNeg

theorem curve25519_lawful : curve25519.Lawful := sorry
theorem ristretto255_lawful : ristretto255.Lawful := sorry
theorem xsalsa20poly1305_lawful : xsalsa20poly1305.Lawful := sorry

def box : Box := dhBox curve25519 xsalsa20poly1305 hsalsa20
def boxXchacha20poly1305 : Box := dhBox curve25519 xchacha20poly1305 hchacha20
def boxRistretto255 : Box := dhBox ristretto255.toDhFunction xchacha20poly1305 blake2b32

theorem box_lawful : box.Lawful :=
  dhBox_lawful curve25519 xsalsa20poly1305 hsalsa20 curve25519_lawful xsalsa20poly1305_lawful

end Sodium.Crypto
