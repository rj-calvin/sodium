import Sodium.Ethos.Frontend
import Lean.Server.Requests

universe u

open Lean Sodium Server Crypto

namespace Ethos.Server

deriving instance TypeName for Meta.SavedState

structure EthosRequest where
  text : Lsp.TextDocumentIdentifier
  position : Lsp.Position
  cert : Observable

instance : Lsp.FileSource EthosRequest where
  fileSource p := p.text.uri

instance _root_.Lsp.TextDocumentIdentifier.encodable : Encodable Lsp.TextDocumentIdentifier :=
  Encodable.ofEquiv _ {
    push x := x.uri
    pull x := ⟨x⟩
  }

instance _root_.Lsp.Position.encodable : Encodable Lsp.Position :=
  Encodable.ofEquiv (Nat × Nat) {
    push | ⟨x, y⟩ => ⟨x, y⟩
    pull | ⟨x, y⟩ => ⟨x, y⟩
  }

def EthosRequest.Shape :=
  Lsp.TextDocumentIdentifier
  × Lsp.Position
  × Observable

instance EthosRequest.Shape.encodable : Encodable EthosRequest.Shape := by unfold Shape; infer_instance

instance EthosRequest.encodable : Encodable EthosRequest :=
  Encodable.ofEquiv Shape {
    push | ⟨x₁, x₂, x₃⟩ => ⟨x₁, x₂, x₃⟩
    pull | ⟨x₁, x₂, x₃⟩ => ⟨x₁, x₂, x₃⟩
  }

instance : ToJson Observable := ⟨encode⟩
instance : FromJson EthosRequest := ⟨fun x => match decode? x with | some x => .ok x | _ => .error s!"{decl_name%}"⟩

protected def main (p : EthosRequest) (ctx : Meta.SavedState) : RequestM (LspResponse Observable × Meta.SavedState) := do
  let ε : {σ : Type} → (τ : Sodium σ) → EthosM τ Observable := fun τ => by
    ethos addressed (prompt := default) (add norm unfold Ethos.Universal.prompt) fun msg => do
      unless this.phase = .safe do default
      let .accepted o ← decrypt? (α := Observable) msg | default
      o.quantize

  let main : MetaM Observable := do
    let δ ← mkFreshDelta
    let o? ← Ethos.main ε δ.mvarId!
    return o?.get

  let o? ← RequestM.withWaitFindSnapAtPos p.position fun snap => do RequestM.runCoreM snap fun _ => do
    let ⟨⟨o, stale⟩, fresh⟩ ← ctx.runMetaM main |>.run
    return ⟨⟨o, true⟩, {stale with meta := fresh}⟩

  return match o?.get with
  | .ok x => x
  | .error s => ⟨⟨p.cert, false⟩, ctx⟩

protected def turn (e : Lsp.DidChangeTextDocumentParams) : StateT Meta.SavedState RequestM Unit := do
  default

initialize do
  registerPartialStatefulLspRequestHandler
    (method := "$/lean/ethos/observe")
    (refreshMethod := "$/lean/ethos/renew")
    (refreshIntervalMs := 1000)
    (paramType := EthosRequest)
    (respType := Observable)
    (stateType := Meta.SavedState)
    (initState := {core := {env := ← mkEmptyEnvironment, passedHeartbeats := ← IO.getNumHeartbeats}, meta := {}})
    Ethos.Server.main
    Ethos.Server.turn

end Ethos.Server
