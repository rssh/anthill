## Attributes

- id: WI-20261025-27050-provision-lookup-and-type
- created: 2026-10-25T12:11:25Z

- status: Open
- status_agent: claude
- status_at: 2026-10-25T12:11:25Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

PROVISION LOOKUP AND TYPE PATTERNS ANSWER "MAY A STAND WHERE B IS EXPECTED" WITH THE TYPER'S RELATION, WHERE THE SPEC GIVES THEM THE SAME ONE — the subtype relation has three implementations (the typer's `types_compatible`, provision lookup's `match_candidate_against_goal`, the type pattern's `type_pattern_admits`), and the compatibility matrix (docs/design/compatibility-question-map.md, 153 programs, measured 2026-10-25 on d6a28558 and unchanged on 1373e04f) has the typer's six positions agreeing on every pair while the other two disagree with it in rows of their own. (C2 — a provision at a spec over a parameter answering its provider — was the third, and left this ticket on 2026-10-25: it is the rule WI-20261025-053QV gives the typing positions.)

  C6 — a `requires` refinement with written arguments is not climbed. With `sort Dog { requires Wide[W = Int64]; entity rex }`, a provision at `Wide[W = Int64]` does not answer `Desc.d(rex)` ("Dog provides no Desc"), while one at bare `Wide` does (and one at a parameterless `Animal` for `Dog requires Animal`). The typer admits a `Dog` at `Wide[W = Int64]` in every position; the clause's arguments are dropped on the way up (WI-20261020-G37HS is the same drop on the typer's side, the other way: it admits `Wide[W = String]`).
  C5 — a type pattern has no provider leg, and exists at no spec (user, 2026-10-25: "If we want catch Stream … we should catch List"; "TypePattern should be available for all"; "Bk provides Tagger[Bk], so it should be catch by Tagger[Bk]"). `type_admits(Stream[T = Int64, E = {}], List[T = Int64])` is false, and `Error.reify[T1 = Stream[T = Int64, E = {}]](lambda () -> boom())` over `boom() effects {Error[List[T = Int64]]}` is refused at load (the label discharge: "the closed row does not admit Error[T = List[T = Int64]]"); at `T1 = List[T = Int64]` it catches (7). §8.2: "a `List` is a `Stream`". `type_pattern.rs`'s header records the leg as left out because "the run-time boundary never read it" — that reason is retired by this decision. Three things change: `TypePattern` answers at every sort, a spec included — today `Error.reify[T1 = Stream[T = Int64, E = {}]](lambda () -> 1)` is refused "no row of anthill.reflect.TypePattern answers here, and none may be written: its one row is TypeValuePattern's, which answers wherever the type has a TypeValue, one derived for a sort that is no spec" — so its one row is no longer conditioned on a `TypeValue` (proposals 065 §2 and 071 §1.2 amended, and the spec sentence with them, worded with the user); the label discharge at load; and the boundary's `TypePattern.admits` at run time.

THE RELATION TO HOLD (user, 2026-10-25): a pattern at `X` admits `t` when `t` is a subtype of an instance of `X` (`List` at `Stream`) or `t`'s own sort provides an instance of `X` (`Bk` at `Tagger[C = Bk]`, and at `Tagger`, an open slot admitting every type) — the relation WI-20261025-053QV gives the typing positions, so a boundary and a parameter written alike answer alike. A provision another sort writes for the carrier counts for neither yet ("in future"). A pattern at a tuple or an arrow is WI-20261021-VF8GT's. Where the spec gives provision lookup a rule of its own it keeps it: a tuple or an arrow binding is compared by its parts (§5.2, "a tuple with a component more is another binding … though it conforms to it as a type"), and variance in a provision head is WI-20261017-DYX5E's question. Type arguments in a provision head are WI-20260929-05ZQE's.

WHAT. Provision lookup's head match and `type_pattern_admits`' head and argument legs ask the typer's relation for a sort-headed type — one predicate, carrier-neutral, that the typer's positions already agree on — and the type pattern keeps what it was built for (pure, bounded, an error for what it does not judge). Not by adding a provider leg to each reader: by each reading the one the typer reads.

ACCEPTANCE: the generated family `g-compatibility` (rustland/anthill-core/tests/families/compatibility.rs): the exceptions it lists under this ticket cleared — C6's provision answering where the typed positions admit, C5's `type_admits` answering what they answer — and no other verdict moved; the `Stream` boundary above catches a raised `List` and an `Error.reify[T1 = Tagger[C = Bk]]` boundary a raised `bk(k: 1)` (rows, both at load and at run time); the full gate green; the families green on both carriers.

## Changes

### 2026-10-25T13:05:31Z — feedback — claude

DECIDED WITH THE USER (2026-10-25): "TypePattern should be available for all." Measured first, on 1373e04f: a boundary at any spec cannot be written today — `Error.reify[T1 = Stream[T = Int64, E = {}]](lambda () -> 1)` is refused "no row of anthill.reflect.TypePattern answers here, and none may be written: its one row is TypeValuePattern's, which answers wherever the type has a TypeValue, one derived for a sort that is no spec", and so is `T1 = Tagger[C = Bk]`. So C5 has a third part beside the label discharge and type_admits: TypePattern answers at every type, a spec included, and its one row is no longer conditioned on a TypeValue (proposal 065 §2 and 071 §1.2 amended, and the spec sentence with them — to be worded with the user). Still open, asked the same day: whether a boundary at a spec over a parameter (`Tagger[C = Bk]`) catches a raised `Bk` — this ticket's reading is no, the typer's answer (`direct(bk(k: 0))` is refused, `type_admits(Tagger[C = Bk], Bk)` answers no) — and whether "all" takes in tuples and arrows, which 071 refuses as a payload and type_admits leaves unjudged.

### 2026-10-25T13:55:42Z — feedback — claude

DECIDED WITH THE USER (2026-10-25), the question left open in the note above: "Bk provides Tagger[Bk], so it should be catch by Tagger[Bk]." A type pattern admits a provider: `Error.reify[T1 = Tagger[C = Bk]]` catches a raised `bk(k: 1)`, and `type_admits(Tagger[C = Bk], Bk)` answers yes — the pattern's relation is "is a subtype of an instance of X, or provides an instance of X". This ticket's reading, asked the same day and not yet confirmed: the typing positions keep kernel-language §8.2 (`direct(bk(k: 0))` over `direct(w: Tagger[C = Bk])` stays refused, and C2 — a member typed `Tagger` handed a `Bk` by provision lookup — stays a defect), so the type pattern is no longer one more spelling of the typer's relation for a spec over a parameter; and whether a provision another sort writes for the carrier (`sort W provides Tagger[C = Bk]`) makes a `Bk` caught too.

### 2026-10-25T13:57:02Z — feedback — claude

DECIDED WITH THE USER (2026-10-25), the two points the note above left: (1) only the carrier's own provision makes it caught for now — a provision another sort writes for the carrier (`sort W provides Tagger[C = Bk]`) is for later ("in future, now we just don't want complexity"); (2) a type pattern at a tuple or an arrow is not this ticket's: it goes with the ticket for a structural former read as a sort is, WI-20261021-VF8GT ("TypePattern will go there"). The typing positions are unchanged here (kernel-language §8.2: `direct(bk(k: 0))` stays refused).

### 2026-10-25T16:28:10Z — feedback — claude

Scope rewritten to the decisions of 2026-10-25 recorded in the notes above: C2 leaves this ticket for WI-20261025-053QV (a position typed at a spec over a parameter admits a value whose own sort provides an instance of it, so a provision at `Tagger` handing a `Bk` to `d(x: Tagger)` is correct), and C5 states the relation the pattern and the typing positions now share.

