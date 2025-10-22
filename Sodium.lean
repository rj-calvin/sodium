import «Sodium».Crypto.Monad
import «Sodium».Data.Digest
import «Sodium».Lean.Syntax

open Lean Sodium Crypto

#eval show MetaM Format from CryptoM.toMetaM fun _ => do
  let stx ← TSyntax.encodable.syntax `tactic
  let x ← encrypt stx
  let .accepted y ← decrypt? (α := TSyntax ``Lean.Parser.Tactic.tacticSeq) x
    | return default
  return y.raw.prettyPrint
