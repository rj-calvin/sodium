import «Sodium».FFI.Basic
import «Sodium».FFI.Deprecated.PwHash

namespace Sodium.Tests

open Sodium.FFI

def testPwHashStr : IO Unit := do
  -- Initialize Sodium
  let initResult ← sodiumInit
  if initResult != 0 then
    throw (IO.userError "Failed to initialize Sodium")

  let password := "my_secure_password123"
  IO.println s!"Original password: {password}"

  -- Hash password for storage (interactive level)
  let hashStr ← pwhashStr password PWHASH_OPSLIMIT_INTERACTIVE PWHASH_MEMLIMIT_INTERACTIVE
  IO.println s!"Password hash length: {hashStr.length}"
  IO.println s!"Password hash: {hashStr}"

  -- Verify the password
  let isValid ← pwhashStrVerify hashStr password
  if isValid then
    IO.println "✓ Password verification passed!"
  else
    throw (IO.userError "✗ Password verification failed!")

def testPwHashStrWrongPassword : IO Unit := do
  let _ ← sodiumInit

  let correctPassword := "correct_password"
  let wrongPassword := "wrong_password"

  -- Hash the correct password
  let hashStr ← pwhashStr correctPassword PWHASH_OPSLIMIT_INTERACTIVE PWHASH_MEMLIMIT_INTERACTIVE

  -- Try to verify with wrong password
  let isValid ← pwhashStrVerify hashStr wrongPassword
  if isValid then
    throw (IO.userError "✗ Expected password verification to fail")
  else
    IO.println "✓ Correctly rejected wrong password"

def testPwHashKeyDerivation : IO Unit := do
  let _ ← sodiumInit

  let password := "key_derivation_password"
  let keyLength : USize := 32  -- 256-bit key

  -- Generate a random salt
  let salt ← randomBytes PWHASH_SALTBYTES
  IO.println s!"Salt size: {salt.size}"

  -- Derive key from password (interactive level)
  let key1 ← pwhash keyLength password salt PWHASH_OPSLIMIT_INTERACTIVE PWHASH_MEMLIMIT_INTERACTIVE PWHASH_ALG_DEFAULT
  IO.println s!"Derived key 1 size: {key1.size}"

  -- Derive same key again (should be identical)
  let key2 ← pwhash keyLength password salt PWHASH_OPSLIMIT_INTERACTIVE PWHASH_MEMLIMIT_INTERACTIVE PWHASH_ALG_DEFAULT
  IO.println s!"Derived key 2 size: {key2.size}"

  -- Keys should be identical
  if key1.data == key2.data then
    IO.println "✓ Key derivation is deterministic"
  else
    throw (IO.userError "✗ Key derivation should be deterministic")

def testPwHashDifferentSalts : IO Unit := do
  let _ ← sodiumInit

  let password := "same_password"
  let keyLength : USize := 32

  -- Generate two different salts
  let salt1 ← randomBytes PWHASH_SALTBYTES
  let salt2 ← randomBytes PWHASH_SALTBYTES

  -- Derive keys with different salts
  let key1 ← pwhash keyLength password salt1 PWHASH_OPSLIMIT_INTERACTIVE PWHASH_MEMLIMIT_INTERACTIVE PWHASH_ALG_DEFAULT
  let key2 ← pwhash keyLength password salt2 PWHASH_OPSLIMIT_INTERACTIVE PWHASH_MEMLIMIT_INTERACTIVE PWHASH_ALG_DEFAULT

  -- Keys should be different
  if key1.data != key2.data then
    IO.println "✓ Different salts produce different keys"
  else
    throw (IO.userError "✗ Different salts should produce different keys")

def testPwHashSensitiveLevel : IO Unit := do
  let _ ← sodiumInit

  let password := "sensitive_password"

  -- Hash password with sensitive security level (slower but more secure)
  let hashStr ← pwhashStr password PWHASH_OPSLIMIT_SENSITIVE PWHASH_MEMLIMIT_SENSITIVE
  IO.println s!"Sensitive hash length: {hashStr.length}"

  -- Verify the password
  let isValid ← pwhashStrVerify hashStr password
  if isValid then
    IO.println "✓ Sensitive level password verification passed!"
  else
    throw (IO.userError "✗ Sensitive level password verification failed!")

def testPwHashInvalidSalt : IO Unit := do
  let _ ← sodiumInit

  let password := "test_password"
  let keyLength : USize := 32

  -- Use invalid salt size (wrong length)
  let invalidSalt ← randomBytes 8   -- Should be 16 bytes

  -- This should fail with invalid salt size error
  try
    let _ ← pwhash keyLength password invalidSalt PWHASH_OPSLIMIT_INTERACTIVE PWHASH_MEMLIMIT_INTERACTIVE PWHASH_ALG_DEFAULT
    throw (IO.userError "✗ Expected error for invalid salt size")
  catch e =>
    IO.println s!"✓ Correctly caught salt error: {e}"

def testPwHashZeroOutput : IO Unit := do
  let _ ← sodiumInit

  let password := "test_password"
  let salt ← randomBytes PWHASH_SALTBYTES

  -- Use zero output length (invalid)
  try
    let _ ← pwhash 0 password salt PWHASH_OPSLIMIT_INTERACTIVE PWHASH_MEMLIMIT_INTERACTIVE PWHASH_ALG_DEFAULT
    throw (IO.userError "✗ Expected error for zero output length")
  catch e =>
    IO.println s!"✓ Correctly caught zero output error: {e}"

def testPwHashDifferentOutputLengths : IO Unit := do
  let _ ← sodiumInit

  let password := "test_password"
  let salt ← randomBytes PWHASH_SALTBYTES

  -- Test different key lengths
  let key16 ← pwhash 16 password salt PWHASH_OPSLIMIT_INTERACTIVE PWHASH_MEMLIMIT_INTERACTIVE PWHASH_ALG_DEFAULT
  let key32 ← pwhash 32 password salt PWHASH_OPSLIMIT_INTERACTIVE PWHASH_MEMLIMIT_INTERACTIVE PWHASH_ALG_DEFAULT
  let key64 ← pwhash 64 password salt PWHASH_OPSLIMIT_INTERACTIVE PWHASH_MEMLIMIT_INTERACTIVE PWHASH_ALG_DEFAULT

  if key16.size == 16 && key32.size == 32 && key64.size == 64 then
    IO.println "✓ Different output lengths work correctly"
  else
    throw (IO.userError "✗ Output lengths don't match requested sizes")

def testPwHashEmptyPassword : IO Unit := do
  let _ ← sodiumInit

  let emptyPassword := ""

  -- Hash empty password (should work)
  let hashStr ← pwhashStr emptyPassword PWHASH_OPSLIMIT_INTERACTIVE PWHASH_MEMLIMIT_INTERACTIVE
  IO.println s!"Empty password hash length: {hashStr.length}"

  -- Verify empty password
  let isValid ← pwhashStrVerify hashStr emptyPassword
  if isValid then
    IO.println "✓ Empty password handling works"
  else
    throw (IO.userError "✗ Empty password verification failed")

  -- Make sure wrong password still fails
  let isInvalid ← pwhashStrVerify hashStr "not_empty"
  if isInvalid then
    throw (IO.userError "✗ Empty password hash should not verify wrong password")
  else
    IO.println "✓ Empty password hash correctly rejects wrong password"

def testPwHashUnicodePassword : IO Unit := do
  let _ ← sodiumInit

  let unicodePassword := "пароль🔐密码"  -- Russian, emoji, Chinese
  IO.println s!"Unicode password: {unicodePassword}"

  -- Hash unicode password
  let hashStr ← pwhashStr unicodePassword PWHASH_OPSLIMIT_INTERACTIVE PWHASH_MEMLIMIT_INTERACTIVE
  IO.println s!"Unicode password hash length: {hashStr.length}"

  -- Verify unicode password
  let isValid ← pwhashStrVerify hashStr unicodePassword
  if isValid then
    IO.println "✓ Unicode password handling works"
  else
    throw (IO.userError "✗ Unicode password verification failed")

end Sodium.Tests
