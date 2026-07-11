import Sodium.Data.ByteVector

namespace Sodium

namespace XSalsa20Poly1305

@[extern "lean_sodium_aead_xsalsa20poly1305_encrypt"]
opaque encrypt (key : @& ByteVector 32) (nonce : @& ByteVector 24) (ad msg : @& ByteArray) : ByteArray

@[extern "lean_sodium_aead_xsalsa20poly1305_decrypt"]
opaque decrypt? (key : @& ByteVector 32) (nonce : @& ByteVector 24) (ad ct : @& ByteArray) : Option ByteArray

end XSalsa20Poly1305

namespace XChaCha20Poly1305

@[extern "lean_sodium_aead_xchacha20poly1305_encrypt"]
opaque encrypt (key : @& ByteVector 32) (nonce : @& ByteVector 24) (ad msg : @& ByteArray) : ByteArray

@[extern "lean_sodium_aead_xchacha20poly1305_decrypt"]
opaque decrypt? (key : @& ByteVector 32) (nonce : @& ByteVector 24) (ad ct : @& ByteArray) : Option ByteArray

end XChaCha20Poly1305

namespace Aegis256

@[extern "lean_sodium_aead_aegis256_encrypt"]
opaque encrypt (key : @& ByteVector 32) (nonce : @& ByteVector 32) (ad msg : @& ByteArray) : ByteArray

@[extern "lean_sodium_aead_aegis256_decrypt"]
opaque decrypt? (key : @& ByteVector 32) (nonce : @& ByteVector 32) (ad ct : @& ByteArray) : Option ByteArray

end Aegis256

end Sodium
