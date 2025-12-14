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

In the city called Universal, nothing counted as “real” until it could be written down, shipped across town, and read back without changing its meaning. The city had a single civic religion: round-tripping.

And in this city lived a young clerk by the name of Aesop who works gladly, blindly, and patiently to ensure that Universal's law is litigated correctly at all times. 

All Aesop needed to ensure the correctness of Aesop's own labor was a simple law powerful enough to derive all others, the city of Universal's motto, stated plainly on the plaque above Aesop's typewriter:

If you can encode it and decode it, you must get the same thing in return.

Not *approximately* the same. Not “morally” the same. Identically the same, down to the last grapheme of syntax and the last newline of proof.

The city’s scribes didn’t sign their names in ink. They signed with a seal whose shape only a particular kind of key could produce. Every official act—every tactic the city used to move from question to answer—arrived as a sealed document: a Verified Tactic. If you broke the seal and it didn’t verify, the courier didn’t argue. The message was simply **refused**. If the wax melted into nonsense, it was **mangled**. If the letters were readable but meaningless, **unknown**. If it almost parsed but didn’t fit the expected form, **almost**. Only then—only rarely—**accepted**.

And because trust wasn’t free, each sealed document carried a Weight: a ration card punched with a numerator and a denominator, a measured cost paid in heartbeats. Some tasks were cheap, others expensive. The city called this cost “Δ”, the difference between before and after, measured in allocations rather than from a vibrating stick of quartz. To the citizens of Universal, this was natural since one can always lie about what time it is, but one *cannot* lie about how heavy something is.

In the courthouse, laws can be identified by the color of parchment they are written on. **norm** colored laws indicate trivial laws that all citizens obey by not acting. These are laws such as “the choice to imagine peace is the act of creating it.” Next, **safe** colored laws are reserved for any law that has been proven to reduce the difficulty of labor. These laws are favorites for judges and lawyers alike since these laws simplify the process of negotiating the interpretation of terms. An example of such a law would be “all people have seven holes for seeing, hearing, eating, and breathing.” Lastly, and most infamous, are **unsafe** colored laws. These are laws whose applicability is contingent on a secret interpretation known only when the law is applied to a particular case. An example of such a law would be “we gladly, blindly, patiently obey all of Universal's known laws.”

In a narrow annex within the courthouse housed a small machine known by an ordinary name: the Typewriter, the city’s interface with intention. The Typewriter took shapes and points—presses and targets—and turned them into acts the court could understand. But the city was multilingual: one person’s “x” was another’s dead key. So the city also maintained an Emulator, a translator bound to a “standard” language of the courthouse. It was, in effect, a treaty between keyboards.

Now, in this city, there was a ritual called Destruction, the procedure of proof-completion. The city’s judges loved it, because it meant a case could end.

But the ritual could not be performed by force. It required two things.

First, it required a **Forward Guarantee**: a promise that if you took an Observable—one of those sealed, weighted acts of proof—and pushed it through the city’s Shape machinery (pack it into a transport form) and pulled it back out (reconstruct it), you got the exact same Observable.

Second, it required a **Frame**: a particular kind of structure built from the Emulator’s alphabet. The Frame was a W-shaped scaffolding: a proof tree whose very construction declared where it could and could not branch. If you tried to hand the court a frame with missing children, the court demanded you show the missing branches were impossible, not merely absent.

This is where Aesop entered—not the storyteller, but the clerk. Aesop was the courthouse’s rule-runner, entrusted to assemble chains of small trusted moves. Aesop worked under published guidelines: some rules were safe, some were mere unfolding of definitions, and some were explicitly unsafe—permitted only with some probability of success, only to prevent endless wandering. The city preferred explicit steps, and Aesop obliged.

On a cold morning, a petitioner arrived with a simple request: “Give me a Destruct. End this search. Close the loop.”

Aesop began exactly as the plaque demanded.

First, Aesop produced a warrant from the city’s archivist—Construct. However, unique to the city of Universal, the city archivist was charged with overseeing exactly *one* artifact: the city’s Prompt—Universal’s law of round-tripping. Any court that wished to begin a case would first consult Construct to obtain a new Prompt that will simplify into mechanical equalities: encode then decode, decode then encode, again and again, until the court could see the gears mesh without slipping.

With the warrant in hand, Aesop then turned to begin proceedings: “Apply Destruct,” Aesop said.

The judge nodded. “I will allow it, provided you supply the guarantee and the frame.”

So Aesop offered the guarantee first: the Forward warrant, stamped from Construct’s proof of the prompt. In the city’s language, it meant: “Our serialization is faithful; our transport doesn’t corrupt the seal; our shapes are honest.”

Then Aesop built the frame.

The frame was minimal, almost austere: a Commit containing the Escape, and another Escape tucked inside as exact text—control characters made literal, intent made checkable. The frame carried the city’s resident Automaton—τ—the ambient source of cryptographic context, entropy, and keyed authority. Not because τ was trusted blindly, but because the city had decided that all trust must be routed through a context: keys derived from a known source, nonces generated fresh when possible, stale when necessary but never unaccounted for.

Once the frame existed, the rest was mechanical.

The petitioner’s request—some arbitrary semantics α over Universal—was asked a single question: “Show me something Observable under the prompt.” And because α lived in Universal, it had no choice but to answer in the city’s coin: it produced an Observable when handed the warrant.

That Observable’s heart—the sealed tactic inside it—was then passed through the Forward guarantee. The judge didn’t have to “believe” the tactic; the judge only had to verify that the transport story was consistent: push then pull yields the same. The end result was lifted into a terminal form: Destruct, the last word.

This leaves all scholar's of Universal law with a small, but powerful, vocabulary:

- **Observables** are acts with signatures and costs.
- **Prompts** are explicit assumptions about what can be reified and recovered.
- **Forward** is the non-negotiable transport invariant.
- **Frames** are protocols.
- **Destruction** is termination that doesn’t smuggle in new trust—only rearranges existing trust until it becomes final.

And in the dutiful silence, the clerk Aesop filed the paperwork the way it always did in Universal: recording its observations into a sequence of steps that anyone could replay—provided they accepted the same prompt, paid the same weight, and verified the same seals.
