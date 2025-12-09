import Sodium.Shell.Terminal
import Sodium.Typo.Latin

open Lean Server Sodium Crypto Ethos Typo

declare_aesop_rule_sets [«temporal»] (default := false)

def shell : List String := [
  "import «Sodium»",
  "open Lean Ethos Typo",
  "declare_syntax_cat shell",
  "example : Universal Universal.Destruct.{0} := by",
  "  aesop (rule_sets := [«standard», «cautious», «external», «temporal»])",
]

def run (uri : System.FilePath) (args : List String) (latency : Nat := 29) (delay : Nat := 31) : IO Unit := do
  let tid ← IO.getTID
  let shell := uri / "Shell.lean"
  let workspace := {uri := uri.toString, name := "«shell»" : Lsp.WorkspaceFolder}

  IO.FS.createDirAll uri
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.searchPathRef.modify (uri :: ·)

  let doc := {
    uri := shell.toString
    mod := `«Shell»
    version := 1
    text := FileMap.ofString <| String.intercalate "\n" args ++ "\n\n"
    dependencyBuildMode := .once
    : DocumentMeta
  }

  let _ ← FileWorker.setupFile doc #[] default

  let config := {
    processId? := some (Int.ofNat tid.toNat)
    clientInfo? := some {name := "«Shell»"}
    rootUri? := uri.toString
    workspaceFolders? := #[workspace]
    initializationOptions? := some {
      editDelay? := some delay
      hasWidgets? := true
    }
    capabilities := {
      window? := some {showDocument? := some {support := false}}
      workspace? := some {
        applyEdit? := true
        workspaceEdit? := some {
          documentChanges? := true
          changeAnnotationSupport? := some {groupsOnLabel? := true}
          resourceOperations? := some #["create", "rename", "delete"]
        }
      }
      textDocument? := some {
        completion? := some {completionItem? := some {insertReplaceSupport? := true}}
        inlayHint? := some {dynamicRegistration? := true, resolveSupport? := some {properties := #[]}}
        codeAction? := none
      }
      lean? := some {silentDiagnosticSupport? := false}
    }
  }

  let (ctx, st) ← FileWorker.initializeWorker doc (← IO.getStdout) (← IO.getStderr) config default

  StateRefT'.run' (s := st) <| ReaderT.run (r := ctx) <| show FileWorker.WorkerM Unit from do
    let hLog := (← read).hLog

    let bridge : Syntax.Tactic → MetaM _
    | `(tactic|aesop $config*) => Emulator.bridge (σ := Universal.Destruct.{0}) hLog config
    | _ => Elab.throwUnsupportedSyntax

    repeat match ← (← get).doc.cmdSnaps.getFinishedPrefixWithConsistentLatency latency with
    | (snap :: _, _, false) =>
      discard <| EIO.toBaseIO <| snap.runTermElabM (← get).doc.meta do
        bridge <| ← `(tactic|aesop (rule_sets := [«external»]))
    | (_, some e, _) => throw e
    | (_, _, _) => continue

def main (args : List String) : IO UInt32 := do
  /- enableRawMode -/
  let uri := (← IO.appDir) / ".." / ".."
  try run uri <| if args.length > 0 ∧ args.tail.length > 0 then args.tail else shell
  finally disableRawMode
  return 0
