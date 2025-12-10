# Repository Guidelines

## Project Structure & Modules
- Root entry points: `Sodium.lean` and `Shell.lean` load the main namespaces and demo shell.
- Core libraries live under `Sodium/` (e.g., `Ethos` for proof-carrying objects, `Typo` for frontend/keyboard simulation, `Crypto` for sodium FFI).
- Lake configuration: `lakefile.lean`, `lake-manifest.json`, and `lean-toolchain`. External deps are in `.lake/packages/`; treat them as vendored, read-only.
- No dedicated `test/` tree; correctness is enforced by Lean/Lake builds and tactic search.

## Build, Test, and Development
- Use the `lean-lsp` as the main entry-point for all engagement with Lean4 files.

## Coding Style & Naming
- Follow Lean community style: namespaces in PascalCase matching file paths (`Sodium/Typer/…`), defs/theorems in `camelCase`, constants/types in `PascalCase`.
- Prefer small, composable defs with docstrings `/- ... -/` when concepts are non-obvious.
- Keep tactics explicit; when adding `aesop` rules, specify `rule_sets := [...]` and a percentage for unsafe rules.

## Testing Guidelines
- If adding IO/FFI code, consider guarded `#eval` snippets or small `example` proofs rather than persistent executables.

## Commit & PR Guidelines
- Commits: concise, imperative subject (“Add observable renew helper”) plus brief body if needed.
- PRs: include a short summary, affected modules (`Sodium/Ethos/*`, `Typo/Frontend/*`, etc.), and validation steps (e.g., `lake build`). Mention any new `aesop` rules or rule-set changes.
- Screenshots/output generally unnecessary; prefer Lean snippets or goal states if demonstrating tactic behavior.

## Security & Configuration Tips
- FFI bindings rely on libsodium; avoid modifying `.alloy` C sections without rebuilding via Lake.
- Observables and witnesses carry signatures; if you change signing flows, document key sources (fresh vs. stale) and scopes.
