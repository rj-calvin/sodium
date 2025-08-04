import «Sodium».Tests.Auth
import «Sodium».Tests.Basic
import «Sodium».Tests.Box
import «Sodium».Tests.GenericHash
import «Sodium».Tests.KeyDeriv
import «Sodium».Tests.KeyExch
import «Sodium».Tests.PwHash
import «Sodium».Tests.SecretBox
import «Sodium».Tests.SecretStream
import «Sodium».Tests.ShortHash
import «Sodium».Tests.Sign
import «Sodium».Tests.Stream

def main : IO UInt32 := do
  Sodium.Tests.KeyDeriv.runAllTests
  Sodium.Tests.KeyExch.runAllTests
  Sodium.Tests.ShortHash.runAllTests
  Sodium.Tests.Auth.runAllTests
  Sodium.Tests.Stream.runAllTests
  pure 0
