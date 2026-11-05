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

