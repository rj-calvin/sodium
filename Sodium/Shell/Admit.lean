import Sodium.Typo.Emulator
import Sodium.Shell.Terminal

open Lean Elab Term Meta Server Sodium Ethos Typo

syntax (name := «admit%») "admit% " term : term

@[term_elab «admit%»]
unsafe def elabAdmit : TermElab
| `(term|admit% $x) => fun type => do
  let γ ← instantiateMVars <| ← elabTermAndSynthesize x type
  let γ ← mkAppM ``Lean.toExpr #[γ]
  evalExpr Expr (mkConst ``Expr) γ (safety := .unsafe)
| _ => fun _ => throwUnsupportedSyntax

def runAdmitAt (uri : System.FilePath) (code : List String) (name : Name) (latency : Nat := 29) (delay : Nat := 31) : IO Unit := do
  let tid ← IO.getTID
  let shell := uri / name.toStringWithSep "/" true default |>.addExtension "lean"
  let workspace := {uri := uri.toString, name := "«shell»" : Lsp.WorkspaceFolder}

  IO.FS.createDirAll uri
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.searchPathRef.modify (uri :: ·)

  let doc := {
    uri := shell.toString
    mod := `«Shell»
    version := 1
    text := FileMap.ofString <| String.intercalate "\n" code ++ "\n\n"
    dependencyBuildMode := .once
    : DocumentMeta
  }

  let _ ← FileWorker.setupFile doc #[{module := `«Sodium», importAll := true}] default

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
    | `(tactic|aesop $config*) => Emulator.bridge (σ := Universal.Destruct) hLog config
    | _ => Elab.throwUnsupportedSyntax

    repeat match ← (← get).doc.cmdSnaps.getFinishedPrefixWithConsistentLatency (23 * latency) with
    | (_, some e, _) => throw e
    | (snap :: _, _, false) =>
      discard <| EIO.toBaseIO <| snap.runTermElabM (← get).doc.meta do
        bridge <| ← `(tactic|aesop (rule_sets := [«external», «temporal»]))
    | (_, _, true) => IO.FS.writeFile shell (← get).doc.meta.text.source
    | (_, _, _) => continue

protected def Admit.core (name : Name) (code : List String) (scope : ScopeName := .local) : MetaM Unit :=
  Meta.withNewMCtxDepth do
    if scope = .global then
      try enableRawMode; runAdmitAt ((← IO.appDir) / ".." / "..") code name
      finally disableRawMode
    else runAdmitAt ((← IO.appDir) / ".." / "..") code name
