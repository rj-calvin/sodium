# Repository Guidelines

## Project Structure & Modules
- Root entry points: `Sodium.lean` and `Shell.lean` load the main namespaces and demo shell.
- Core libraries live under `Sodium/` (e.g., `Ethos` for proof-carrying objects, `Typo` for frontend/keyboard simulation, `Crypto` for sodium FFI).
- Lake configuration: `lakefile.lean`, `lake-manifest.json`, and `lean-toolchain`. External deps are in `.lake/packages/`; treat them as vendored, read-only.
- No dedicated `test/` tree; correctness is enforced by Lean/Lake builds and tactic search.

## Dependencies
- Look for source code for dependencies within `.lake/`.

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

# Abstract Interpretation of the Repository

In the city called Universal, infinite productivity and peace had been achieved by the discovery that all problems that are difficult are difficult for the same reason. One of the cultural idiosyncrasies that emerged from this breakthrough was that citizens no longer considered something to be “real” until it could be written down, shipped across town, and read back without changing its meaning. The city had a single civic religion whose name was decided arbitrarily by a term used in the discovery's original text: round-tripping. It is important to note that the term “round-tripping” doesn't actually appear in the original text. Instead, the name comes from a brief comment: “/- ensure (...) round-trips correctly. -/”

And in this city lived a young clerk by the name of Aesop who works gladly, blindly, and patiently to ensure that Universal's law is litigated correctly at all times. 

All Aesop needed to ensure the correctness of Aesop's own labor was a simple law powerful enough to derive all others, the city of Universal's motto, stated plainly on the plaque above Aesop's typewriter:

If you can encode it and decode it, you must get the same thing in return.

Not *approximately* the same. Not “morally” the same. Identically the same, down to the last grapheme of syntax and the last newline of proof.

Scribes who are trusted by the general will sign amendments with a seal that changed its shape every time it was used. Every official act—every tactic the city used to move from question to answer—arrived as a sealed document: a Verified Tactic. If you broke the seal and it didn’t verify, the courier didn’t argue. The message was simply **refused**. If the stamp was *less than mostly* consistent, it was **mangled**. If the letters were readable but meaningless, they were considered **unknown**. If it almost parsed but didn’t fit the expected format, **almost**. Only then—only when aligned in a giant, cosmic pun—**accepted**.

And because trust wasn’t free, each sealed document carried a Weight: a ration card punched with a numerator and a denominator, a measured cost paid in heartbeats. Some tasks were cheap, others expensive. The city called this cost “Δ”, the difference between before and after, measured in allocations rather than from a vibrating stick of quartz. To the citizens of Universal, this was natural since one can always lie about what time it is, but one *cannot* lie about how heavy something is.

In the courthouse, laws can be identified by the color of parchment they are written on. **norm** colored laws indicate trivial laws that all citizens obey by not acting. These are laws such as “the choice to imagine peace is the act of creating it.” Next, **safe** colored laws are reserved for any law that has been proven to reduce the difficulty of labor. These laws are favorites for judges and lawyers alike since these laws simplify the process of negotiating the interpretation of terms. An example of such a law would be “all people have seven holes for seeing, hearing, eating, and breathing.” Lastly, and most infamous, are **unsafe** colored laws. These are laws whose applicability is contingent on a secret interpretation known only when the law is applied to a particular case. An example of such a law would be “we gladly, blindly, patiently obey all of Universal's known laws.”

In a narrow annex within the courthouse housed a small machine known by an ordinary name: the Typewriter, the city’s interface with intention. The Typewriter took shapes and points—presses and targets—and turned them into acts the court could understand. But the city was multilingual: one person’s “x” was another’s dead key. So the city also maintained an Emulator, a translator bound to a “standard” language of the courthouse. It was, in effect, a treaty between keyboards.

The petitioner’s request—a contract between two colleagues, both written in Universal and signed in Universal—was asked a single question upon receipt: “Show me something Observable relative to a Frame of reference.” And because the contract was both written in Universal and sent through Universal, it had no choice but to be stamped in the city’s coinage that bears its Weight.

That Observable’s heart—the sealed tactic inside it—was then passed through the Prompt. Whenever a Prompt was Forwarded to the local judge, the honorable checker didn’t have to “believe” the tactic; the judge only had to verify that the transport story was consistent: push then pull yields the same. The end result was lifted into a terminal form: Destruct, the last word.

This leaves all scholar's of Universal law with a small, but powerful, vocabulary:

- **Observables** are acts with signatures and costs, known in the text as a *proof-carrier*, or *proof-carrying object*.
- **Prompts** are explicit assumptions about what can be reified and recovered, known in the text as a *polynomial-lift*.
- **Forward** is the non-negotiable transport invariant, known in the text as an *inhabitation clause*.
- **Frames** are linear protocols, known in the text as *polynomial-functors*, a.k.a *mechanisms*.
- **Destruction** is termination that doesn’t smuggle in new trust—only rearranges existing trust until it becomes final, known in the text as a *W-type*.
- **Weight** is the mass of an object, known in the text as *weight*.

And in the dutiful silence, the clerk Aesop filed the paperwork the way it always did in Universal: recording its observations into a sequence of steps that anyone could replay—provided they accepted the same prompt, paid the same weight, and verified the same seals.
