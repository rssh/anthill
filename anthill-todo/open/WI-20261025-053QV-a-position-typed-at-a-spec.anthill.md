## Attributes

- id: WI-20261025-053QV-a-position-typed-at-a-spec
- created: 2026-10-25T16:27:40Z

- status: Open
- status_agent: claude
- status_at: 2026-10-25T16:27:40Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A POSITION TYPED AT A SPEC OVER A PARAMETER ADMITS A VALUE WHOSE SORT PROVIDES AN INSTANCE OF IT — kernel-language §8.2's call side reversed, its body side kept (user, 2026-10-25). Decided in discussion over WI-20261005-KSSA4's own example: "Tagger[C = Bk] from one side, Tagger = Tagger[C = ?] from other, Bk unified with ? — should work"; "previously we write (x: Tagger) instead (x: Tagger[C]) when C does not provide Tagger. It was incorrect. But if C provides Tagger, then situation is other"; and, of `viaBodyless(w: Tagger) = Tagger.probe(w)`: "why you think that w.C is B? Should be refused."

THE RULE. With `sort Tagger { sort C = ?; … }` and `B provides Tagger[C = B]`: a value of `B` is admitted where `Tagger` (`Tagger[C = ?]`, the slot unified with `B`) or `Tagger[C = B]` is written, at every typing position (an operation's argument, an annotated `let`, a return, an entity field, a list element, a lambda's argument). Admitted there, it is a value of the spec's type, not of the carrier: in the body `w.C` is unknown — and with `C = B` written, `w` is still no `B`, since another sort may provide `Tagger[C = B]` — so an operation receiving on `C` refuses it, as today. Where nothing provides the instance it stays refused: `Tagger[C = Int64]` takes no `B`, and `Tagger` takes no `Int64`. Only the value's own sort's provision counts for now; a provision another sort writes for it (`sort W provides Tagger[C = B]`) is for later (user: "in future, now we just don't want complexity"). A spec whose operations receive on itself is unchanged: a `List` is a `Stream`.

THE ROWS (KSSA4's declarations — `Tag`, `Tagger requires Tag[T = C]` with `probe(x: C)` and the default `tagIn(x: C) = Tag.tagOf(x)`, `B` providing both, `Box requires Tag[T = T]` — each operation called with `b(k: 0)` unless said; "call" and "body" are the two refusals today's tree prints, `expected Tagger, got B — … does not make the value a Tagger` at the call and `expected Tagger.C, got Tagger[C = w.C] — … a value typed at it is not a value of a sort that provides it` in the body; MEASURED on 1373e04f):
  1 viaBodyless(w: Tagger) = Tagger.probe(w) — today call + body; after: body.
  2 viaDefaulted(w: Tagger) = Tagger.tagIn(w) — today call + body; after: body.
  3 viaOtherSort(w: Tagger) = Box.tagOf(w) — today call + body; after: body.
  4 projDefaulted(w: Tagger) requires Tag[T = w.C] = Tagger.tagIn(w) — today call + body; after: body.
  5–8 memberDefaulted / memberOtherSort (w: Tagger.C), boundDefaulted / boundOtherSort [P](w: P) requires Tagger[C = P] — 2 each, today and after.
  9 writtenDefaulted(w: Tagger[C = B]) = Tagger.tagIn(w) — today call + body; after: body.
  10 keep(w: Tagger) = 1 — today call; after: 1.
  11 keepWritten(w: Tagger[C = B]) = 1 — today call; after: 1.
  12 keepOther(w: Tagger[C = Int64]) = 1 — today call; after: call.
  13 keep(w: Tagger) = 1 called keep(5) — today call; after: call.
No message is reworded: a program loses the call refusal where its call becomes legal and keeps the body refusal word for word.

DRAFT §8.2 WORDING — for the user to review before it is applied, nothing written to the spec yet:
  (a) "Providing `F[X]` lets the operations of `F` be used on a value of `X`; it does not make a value of `X` a value of `F`." → "Providing `F[X]` lets the operations of `F` be used on a value of `X`, and admits the value where `F` is written at an instance the provision gives; admitted there it is a value of `F`, not of `X`."
  (b) "A sort that provides such a spec is that parameter of it, not the spec. So a position typed at the spec takes no value of a provider's sort, and a value typed at the spec is refused where the parameter is expected:" → "A sort that provides such a spec is that parameter of it, not the spec. A position typed at the spec takes a value of a sort whose own provision gives an instance of it, the instance unified with the type the position writes; the value is then of the spec's type, and is refused where the parameter is expected:"
  (c) the example: `direct(w: Tagger) = Tagger.probe(w) -- refused: w is no Tagger.C` kept; `go() = direct(b(k: 0)) -- refused: a B is no Tagger` replaced by `keep(w: Tagger) -> Int64 = 1`, `go() -> Int64 = keep(b(k: 0)) -- a B provides Tagger[C = B]` and `other(w: Tagger[C = Int64]) -> Int64 = 1`, `no() -> Int64 = other(b(k: 0)) -- refused: B provides no Tagger[C = Int64]`.
  (d) "The position that takes any provider is typed by the provider's sort" → "The position that takes any provider and uses it as the parameter is typed by the provider's sort"; "Both refusals name this spelling." → "The refusal of `direct` names this spelling."

WHAT FOLLOWS. WI-20261025-27050's C2 is no defect: a provision at `Tagger` handing a `Bk` to its member `d(x: Tagger) = 1` is this rule, and leaves that ticket. The typing positions and the type pattern answer one relation again — a subtype of an instance, or the value's own sort provides an instance (27050's C5, user, 2026-10-25) — so the compatibility family's `param-spec` row is one verdict once both land. KSSA4's rows that pin the call-side refusal turn around (grep `is no Tagger`, `does not make the value a`). NOT DECIDED HERE: the rule language — a rule variable `?x: Summable` (WI-20261006-8DXVK's present reading) — and §5.1's admissibility paragraphs; each is asked before it moves.

ACCEPTANCE: rows 1–13 as listed, each driven in a test; in the family `g-compatibility` the `param-spec` row's six typing positions run 1 — its six exceptions under this ticket come off with 27050's `type_admits` one, since P4 calls an exception live while any spelling of the row still differs; §8.2 reworded as reviewed with the user; the full gate green; the families green on both carriers.

## Changes

### 2026-11-06T11:43:46Z — feedback — claude

ROW ADDED WITH THE USER 2026-11-06, moved from WI-20261105-C6GK8: THE SPEC-OPERATION DISPATCH READS THIS RULE, AND WI-496'S DEFERRAL GOES. Over `sort Tagger { sort C = ?  operation tag(c: C) -> Int64 }`, `sort Desc { sort T = ?  operation d(x: T) -> Int64 }`, `sort W { provides Desc[T = Tagger]  operation d(x: Tagger) -> Int64 = 100 }` and `sort Bk { entity bk(k: Int64)  provides Tagger[C = Bk]  operation tag(c: Bk) -> Int64 = match c case bk(k) -> k }`, `operation probe() -> Int64 = Desc.d(bk(k: 0))` answers 100 on a88ec85b, by eval's value-directed dispatch (step 3b): the dispatch reads a `Bk` as no `Tagger` and finds no candidate, and the call is left unstamped by WI-496's deferral, which C6GK8 kept for this case alone (kb/typing/apply.rs, after the chain step; `wi_c6gk8_known_type_call_test::a_provision_at_a_spec_over_a_parameter_still_answers_its_providers_value`). With the deferral removed the program is refused at load: "requirement `Desc[T = Bk]` cannot be supplied for call to `Desc.d`; `Bk` provides no `Desc`". It is this rule at a provision: `W`'s member takes `x: Tagger`, and `Bk`'s own provision gives `Tagger[C = Bk]`. ROW: the dispatch finds `W` for `Desc.d(bk(k: 0))`, the call is decided at load (the stamp `W.d`, which the C6GK8 row asserts as `None` today), the deferral is deleted, and the family row `g-compatibility pair=param-spec,position=provision` keeps `runs 1`.

### 2026-11-13T04:50:10Z — feedback — claude

CORRECTS the 2026-11-06 row (decided with the user 2026-11-13, under WI-20261105-P0QGF). The bare call `Desc.d(bk(k: 0))` is a call at `T = Bk` — the argument fixes `T` — and no provision answers there: `W provides Desc[T = Tagger]` is a provision at `Tagger`, and this ticket's rule is about a value admitted at a position written at a spec over a parameter, not about which provision a call at `Bk` finds. P0QGF deletes WI-496's deferral and the run time's dispatch on the value that answered 100, and the program is refused at load: "requirement `Desc[T = Bk]` cannot be supplied for call to `Desc.d`; `Bk` provides no `Desc`" (`wi_c6gk8_known_type_call_test::a_provision_at_a_spec_over_a_parameter_is_no_provider_of_its_argument`, beside its twin, `Bk provides Desc[T = Bk]`, answering 7). What stays this ticket's are the spellings that fix the call at `Tagger`: `Desc.d[T = Tagger](bk(k: 0))`, refused at the argument ("expected Tagger[C = ?C], got Bk") on the tree before and after, and the witness `Desc.d[Desc = W](bk(k: 0))`, refused at load as `Desc.d[Desc = W](5)` over a `W` providing `Desc[T = String]` is on both trees (a selection is checked against the goal its arguments give). `W` is a sort: a `namespace W` holding the `provides` is refused at load on both trees ("a `provides` clause needs a type at its address"). The family row `g-compatibility pair=param-spec,position=provision` moves `runs 1` -> `loads; drive refused NotAdmitted`, so every spelling of the pair is refused on this tree, and the six P4 exceptions listed for this ticket, with 27050's `type-admits` one, are off the family. NOT DECIDED, for this ticket: whether the provision spelling is still a spelling of the question once a `Bk` is admitted at `Tagger`. For the `self-carrier` pair it is: a provision at `Stream[T = Int64, E = {}]` answers `Desc.d` of a `List` (`runs 1`).

