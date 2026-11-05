## Attributes

- id: WI-20261105-CBRD2-proposal-073-stage-4-no-typed
- created: 2026-11-05T22:18:18Z

- status: Open
- status_agent: claude
- status_at: 2026-11-05T22:18:18Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261105-P0QGF-proposal-073-stage-3-a-value

- tags: proposal-073

## Description

PROPOSAL 073 STAGE 4 — NO TYPED CALLER (docs/proposals/073-abstract-values-are-instances.md §6.1, §6.2): a query, a host call and a rule variable no head column reaches read a requirement no caller passes from the value at the requirement's sort — the dictionary of the sort that built the value — and from nothing else. PROGRAM (§6.2): `sort Marker { sort T = ?  operation tag(x: T) -> Int64 }`, `fact src(1)`, `fact src(true)`, `rule keep[A](?x: A, ?t) :- src(?x), Marker[A], Marker.tag(?x, ?t)`, `rule answer(?t) :- keep(?x, ?t)`, with `Int64` providing `Marker` at `tag = 1` and `Bool` at `tag = 2`: `answer(?t)` answers 1 and 2, `keep(1, ?t)` 1, `keep(true, ?t)` 2 (measured on 62882ef0), and keeps them. DECIDED with the user 2026-11-05: that is no choice among providers — the instance is the value's own sort, and kernel-language §8.7's order answers at it as at load; 060.1 §4 and §8.8 stay in these words. A value gives no type argument it does not hold: `has(s, "a")` with `s` built at `O = ByInner[OI = Flat]` needs `O`, which the `MySet` value does not hold, so the caller passes it or the call is refused naming `s.O`; nothing is built because only one provider exists, and nothing is ranked (WI-20260923-DK0QJ's half (a), the nested slot `resolve_inner` ranks on the host route). HOST ENTRY (§6.1): a dictionary the host passes is a run-time `Dictionary` value (docs/design/requirement-dictionaries.md §1–§2, `alloc_dictionary`) and is used as given; one it does not pass is the value's: `interp.call("gen", &[leaf])` over `operation gen[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)` reads `Leaf`'s `Desc` and answers 7. The three entries `call`, `call_with_witnesses` and `call_with_requirements` become one: a witness named by its sort is that sort's dictionary, and an operation's own `requires`, which `call_with_requirements` has no spelling for today (WI-822), is passed the same way. `resolve_bridge_requirements` goes with its last caller. kernel-language §5.3's sentence on a requirement no caller passes is replaced by 073 §5's, agreed with the user first. Relates to WI-20261015-ZPETZ (the host entry and the in-body dispatch are two copies of one call). ACCEPTANCE: the §6.1 and §6.2 programs driven to their values; DK0QJ's nested-slot fixture (a set built at the generic witness beside a more specific rival, fixture landmines in that ticket) refused at the entry naming the slot, or answering what the typed route answers, never with the rival's dictionary; full workspace green via rustland/scripts/test.sh; families green on both carriers.

## Changes

### 2026-11-05T23:30:37Z — feedback — claude

Acceptance addition (073 review, 2026-11-05; 073 §6.2): a call with no typed caller over a CONDITIONAL provision composes its dictionary as 058 §3.9, 060's rule and 060.1 §4 already decide — the generated goal, anchored by the head column (060 §3), reads the value's carried type when it runs and fetches from the entries load selected, the type arguments flowing to the condition's sub-fetch. Program: `sort Show { sort T = ?  operation show(x: T) -> Int64 }`, `sort ListShow { sort E = ?  requires Show[T = E]  provides Show[T = List[T = E]]  operation show(x: List[T = E]) -> Int64 = match x case nil -> 100 case cons(h, t) -> Show.show(h) + 10 }`, `Int64` providing `Show` at 1, `fact src([1, 2])`, `fact src([])`, `rule keep[A](?x: A, ?t) :- src(?x), Show[A], Show.show(?x, ?t)`, `rule answer(?t) :- keep(?x, ?t)`. MEASURED on e4442b16: `answer(?t)` answers 11 alone — the `[]` row FAILS IN SILENCE — and `keep([], ?t)` answers nothing, while `Show.show([], ?t)` answers 100 through value-direction (the unread `Show[T = E]` slot never asked). WANTED: the `[1, 2]` row 11 through the composed `ListShow` + `Int64` dictionary; the `[]` row, carried at `List[T = ?]`, UNDECIDED (an unreadable carried type delays, requirement-channel.md §4), never failed. Open, in 073 §6.2's last paragraph, to decide with the user: 060 calls the carried type a stored term while `value_type_term` computes it from the value's parts — stored where the value is made, a `[]` built at `List[T = Int64]` would answer 100 and a `MySet` built at `O = ByInner[OI = Flat]` would carry `O`.

### 2026-11-05T23:44:33Z — feedback — claude

Decided with the user 2026-11-05, replacing the previous note's WANTED for the empty list and its open question: no type is stored with a value. 060.1 forbids making an untyped value typed without a dictionary, so over the ListShow program `fact src([])` — `List[T = ?]` where the fact is written — read by `keep[A](?x: A, ?t) :- src(?x), Show[A], …` is REFUSED AT LOAD, naming `E` (as a free type variable a requirement is owed at is), not left undecided; it answers 100 once the `[]` is written with its element type or the citation passes the dictionary, `keep[A = List[T = Int64]](?x, ?t)`. The `[1, 2]` row keeps 11 (its type is complete where the fact is written). A `[]` built at `List[T = Int64]` that passes through a column nothing types brings its dictionary with it — nothing recovers `Int64` from the value later — and DK0QJ's `s.O` is passed by the host or the call is refused naming it (073 §6.1, §6.2).

