import Sodium.Typography.Emulator

open Lean Meta Typography Server Sodium Crypto

def shell : List String := [
  "import «Sodium».«Typography».«Frontend».«Qwerty»",
  "open Lean Elab Meta Tactic Sodium Crypto Ethos Typography",
  "declare_syntax_cat shell",
  "@[reducible] def Shell := MetaM (ULift String)",
  "elab \"#shell \" γ:term : command => do discard <| Lean.Elab.Command.elabRunMeta <| ← `(command|#eval show Shell.{1} from by exact ⟨$γ⟩)",
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
  IO.FS.writeFile shell doc.text.source

  StateRefT'.run' (s := st) <| ReaderT.run (r := ctx) <| show FileWorker.WorkerM Unit from do
    let doc := (← get).doc
    let hLog := (← read).hLog

    let bridge : Syntax.Tactic → MetaM _
    | `(tactic|aesop $config*) => Emulator.bridge (σ := by simp only [Encodable.encodek, implies_true, and_self]) hLog
    | _ => Elab.throwUnsupportedSyntax

    repeat match ← doc.cmdSnaps.getFinishedPrefixWithConsistentLatency latency with
    | (snap :: _, _, true) => discard <| EIO.toBaseIO <| snap.runTermElabM doc.meta do bridge <| ← `(tactic|aesop (rule_sets := [«cautious»]))
    | (_, some e, _) => throw e
    | ([], _, _) | (_, _, false) => continue

def main (args : List String) : IO UInt32 := do
  let uri := (← IO.appDir) / ".." / ".."
  run uri <| if args.length > 0 ∧ args.tail.length > 0 then args.tail else shell
  return 0
