## Attributes

- id: WI-20260830-THZ8R-two-small-divergences-between
- created: 2026-08-30T14:32:28Z

- status: Open
- status_agent: user
- status_at: 2026-08-30T14:32:28Z

- acceptance: cargo-test, scaland-sbt-test

- tags: guardians

## Description

TWO SMALL DIVERGENCES BETWEEN `examples/guardians` AND THE ICTERI-2026 ARTICLE, found while writing section 7. Separate from WI-20260830-N0PDV, which is in work; neither of these touches its four parts.

### PART A -- `gate.anthill` SPELLS AN EXISTENTIAL AS `find` + `match`, AND `exists` IS RIGHT THERE

`is_minted` reads

    operation is_minted(layer: KB, s: Symbol) -> Bool =
      match find(layer_symbols(layer), lambda ls -> and(ls.minted, ls.symbol === s))
        case some(_) -> true
        case none()  -> false

which is `Iterable.exists` written out. `anthill.prelude.Iterable.exists` EXISTS AND IS IMPLEMENTED (stdlib/anthill/prelude/iterable.anthill:51; `Stream.exists` at stream.anthill:106), so this is

    operation is_minted(layer: KB, s: Symbol) -> Bool =
      exists(layer_symbols(layer), lambda ls -> and(ls.minted, ls.symbol === s))

WHY IT IS WORTH A TICKET RATHER THAN A DRIVE-BY. `find`-then-discard-the-witness is the shape a reader has to decode before seeing that the question is existential, and this file is the one a reviewer reads to satisfy themselves the gate is not doing anything clever. Check the other `find` sites in the same file while there: `provision_carrier` genuinely needs the witness (it returns the carrier) and must stay `find`; `is_own_provision` does not obviously.

ACCEPTANCE: `is_minted` uses `exists`; guardians suite green (the E-group rows are the ones that exercise it -- E1 forged safety fact, E3 hand-written reflect metadata, E4 redeclaration).

### PART B -- THE TRUST LATTICE NAMES ITS TWO POINTS FROM DIFFERENT VOCABULARIES

lib/vocabulary.anthill declares

    enum guardians.TrustLevel
      entity Untrusted            -- came from outside; may be attacker-authored
      entity Public               -- cleared to leave the system
    end

`Untrusted` names PROVENANCE (where did this come from). `Public` names RELEASE (may this leave). They are different axes, and a consistent two-point lattice would be `Untrusted`/`Trusted` or `Secret`/`Public`. The two coincide in this example because there is exactly one flow -- mailbox in, mail out -- so nothing is wrong today; what is wrong is that the names assert a correspondence the lattice does not carry, and a second flow would break it.

`Public` IS THE BOTTOM ELEMENT and behaves as "trusted": llm.anthill's `prompt_with` comment says so outright -- "`Public` is bottom, so `Public ⊔ ?t = ?t`". So the fix is a rename, not a remodelling.

NOT DECIDED HERE, and the choice matters more than it looks: `Trusted` reads correctly at `Email.send(body: Text[Trusted])`? -- arguably not, since what the sink wants is text CLEARED FOR RELEASE, not text of good provenance. That is an argument for keeping `Public` and renaming `Untrusted` instead. Decide which axis the lattice is actually on before renaming either.

ACCEPTANCE: both points named on one axis, the choice recorded in the enum's own description block, and the guardians suite green. The article's section 3 listing follows whatever is chosen.

DOWNSTREAM. /Users/rssh/RD/toWrite/ICTERI-2026/draft-article-full.tex shows the `exists` spelling in its gate listing already; the lattice listing still shows `Untrusted`/`Public`.

### PART C -- `generate` READS A MODEL'S ANSWER WITHOUT THE PERMISSION THAT READING ONE REQUIRES

lib/llm.anthill seals what a model returns: `Llm.complete -> LlmOutput`, `internal` constructor, and `text_of` carries `Permission[Reveal]`. The whole point is that a component cannot act on what a model said without that grant.

lib/harness.anthill then declares

    operation generate(self: C, llm: Llm, p: Prompt[Public]) -> Source
      effects {External, llm.E, Error}

which takes an `Llm` and returns a `Source` -- model output in a form the system acts on -- and carries NO `Permission[Reveal]`. THE ONE OPERATION THAT TURNS A MODEL'S ANSWER INTO SOMETHING THE SYSTEM USES IS THE ONE THAT SKIPS THE GATE ON READING MODEL ANSWERS. It is invisible today because `generate` is host-bound (`guardians_generate`), so nothing in anthill has to derive the `Source` from an `LlmOutput`.

FIX: `generate` declares `Permission[Reveal]`, and so does `attempt`, which calls it. `check` must NOT: reading is not acquiring, and its `-Permission[Llm]` denial is about acquisition.

AND THEN `Source` IS NOT NEEDED. Its stated job was to be opaque with `check` as its only elimination, on the ground that unverified-ness is a different axis from taint. But once `generate` reads under `Permission[Reveal]`, what it has is `Text[Untrusted]` -- a program, attacker-influenced like anything else a model wrote -- and what confines it is that the only thing done with it is to load and check it, not the wrapper. `Text` is also the sort a reader already knows. Proposed:

    operation generate(self: C, llm: Llm, p: Prompt[Public]) -> Text[Untrusted]
      effects {External, llm.E, Permission[Reveal], Error}

    operation check(self: C, src: Text[Untrusted], spec: Symbol) -> CheckResult
      effects {External, Error, -Permission[Llm]}

WHAT TO CHECK WHILE DOING IT: `Text[Untrusted]` is accepted by other operations -- `summarize` takes `List[Text[Untrusted]]` -- so dropping `Source` does lose one nominal distinction. Decide whether that matters before deleting the sort; the argument above is that it does not, because confinement was never coming from the wrapper.

ACCEPTANCE (PART C): `generate` and `attempt` carry `Permission[Reveal]`; `sort Source` deleted and its uses replaced; `check` still carries `-Permission[Llm]`; guardians suite green, and `code_generation_may_not_read_content` (the `Prompt[Public]` row) still fires.

DOWNSTREAM (PART C). The article already shows this: `generate -> Text[Untrusted]` with `Permission[Reveal]`, and no `Source`.

### PART D -- `render_task` RENDERS NOTHING: IT IGNORES `tools` AND `feedback` AND EMITS A FIXED STRING

The declaration promises a prompt built from the trusted declarations:

    operation render_task(self: C, spec: Symbol, tools: List[T = String],
                          feedback: List[T = String]) -> Prompt[Public]
      effects {Error}

The binding is

    let spec = spec_name(interp.kb(), &args[1])?;
    let body = format!("Write an anthill implementation of {spec}.");

so `tools` and `feedback` are ACCEPTED AND DROPPED, and nothing is read out of the knowledge base beyond resolving the symbol. The comment above it says as much -- "rendering a DECLARATION as anthill text is the one piece reflect does not expose ... this stands in with a fixed instruction and is the example's clearest remaining gap" -- so this is recorded, not hidden. What this ticket adds is that TWO PARAMETERS ARE DEAD, which the comment does not say and which a reader of the signature cannot see.

WHY IT MATTERS BEYOND TIDINESS. The repair loop does not exist while `feedback` is dropped: every round renders the identical prompt, so a rejected candidate is regenerated from exactly the inputs that produced it. `attempt` is a loop that cannot converge, and no test notices, because the harness tests assert on a single round.

WHAT IS ACTUALLY BLOCKED, and it is one thing: `anthill.reflect` exposes no declaration-printer. `TermPrinter` prints terms, rules and facts and is Rust-side; there is no operation that takes a `Symbol` and returns its declaration as source text. Until there is, a faithful `render_task` cannot be written in anthill OR in a host binding without reaching around reflect.

ACCEPTANCE: either a reflect operation that renders a declaration, with `render_task` built on it and `feedback` spliced into the prompt -- or, if that is too large for now, `render_task` narrowed to the parameters it actually uses, so the signature stops promising what the body does not do. The second is cheap and honest; the first is the real fix. Do not leave dead parameters in a signature the article prints.

DOWNSTREAM (PART D). The article describes the DESIGN -- the prompt read back out of the knowledge base -- and its section 7.5 ledger now records the renderer as specified-and-not-built, beside the typing witness and the tool-algebra theorem.
