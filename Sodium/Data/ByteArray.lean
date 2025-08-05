import Sodium.FFI.Utils

open Sodium FFI

open scoped Alloy.C

alloy c include <lean/lean.h> <string.h>

namespace ByteArray

def succ! : ByteArray → ByteArray := sodiumIncrement

def toBase64 : ByteArray → String := sodiumBin2Base64
def ofBase64 : String → ByteArray := sodiumBase642Bin
def toBase64Url : ByteArray → String := sodiumBin2Base64Url
def ofBase64Url : String → ByteArray := sodiumBase642BinUrl

end ByteArray
