## Attributes

- id: WI-20261017-1Y96B-an-eponymous-sort-s-bare-name
- created: 2026-10-17T05:33:15Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-01T17:58:59Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-055

## Description

AN EPONYMOUS SORT'S BARE NAME IS A TYPE VALUE BUT NOT A RECEIVER THAT DENOTES ITS SORT — `(Ep).em()` and `let t = Ep` + `t.em()` are refused where the same spellings over an ordinary sort call the companion. Measured 2026-10-17 on 145c4624.

THE ROWS. `sort Bx { entity bx(v: Int64); operation tag() -> Int64 = 3 }` beside `sort Ep { entity Ep(name: String); operation em() -> Int64 = 8 }`:
  spelling                   Bx                          Ep
  bare name, `-> Type = X`   loads (a type value)        loads (a type value; `-> Ep = Ep` is "expected Ep, got Type (Ep)")
  written `X.m()`            loads                       loads
  `(X).m()`                  answers 3                   REFUSED "type mismatch in anthill.prelude.Type.em: expected operation declared on the receiver's sort, got no such member (dot dispatch)"
  `let t = X` then `t.m()`   answers 3                   REFUSED, the same
A fieldless eponymous `sort Fl { entity Fl }` is a type value bare too. Asked by the user (2026-10-17): why not `Ep.em()`? Nothing found against it.

WHY. §5.4 (WI-20260824-PAPX0): a receiver that denotes a sort — a written type, or a name a `let` bound to one — takes the dot as the written companion call; a `Type` value that denotes no sort KNOWN AT THE DOT (a parameter, a call's result) is a value, and its dot is `Type`'s. §6.3: a bare eponymous name "still denotes the type". So bare `Ep` denotes its sort statically, and the companion reading is the spec's. What is missing is the RECORD the dot frame reads that from: `Expr::TypeValue`. `Ep`'s bare name is classified by symbol in `check_bare_ref`'s free-standing-entity arm (`is_free_standing_entity` answers `true` for an eponymous sort) and left a plain reference — `Loader::bare_name_denotes_type` excludes `is_entity_constructor` (WI-20260824-WAHB6: the constructor registry is incomplete mid-load), and `Loader::written_type_receiver_occurrence` hands a PATH to an eponymous sort back as an `Expr::Ref` ("as its bare name is none"). So the dot sees a `Type` of no known sort.

MEASURED IN WI-20260824-JM6ZW: rewriting that arm's node into `Expr::TypeValue { head: Ep }` made `(Ep).em()` load as the companion call; the one row that moved in the focused set was `wi_rxt6s_dotted_sort_type_value_test::an_eponymous_sort_by_a_path_is_refused_as_its_bare_name_is`, which pins the refusal as "refused today". Not kept there: it settles the language, which was not that ticket's to do.

TWO NOTES TO VERIFY, not assume. (1) WAHB6's note that "a bare reference to [an eponymous sort] means CONSTRUCTION today" is contradicted by the rows above (`-> Ep = Ep` is `got Type (Ep)`); find whether any spelling still constructs. (2) An eponymous sort and a free-standing entity both carry the `Sort` kind (WI-925's category set) and a sort-nested constructor (`Option.none`) does not, so the record may be makeable AT LOAD from `has_kind(Sort)` without the constructor registry WAHB6 could not ask; if not, the typer's arm is the point that can answer it.

WHAT. Record a bare eponymous sort (and a free-standing entity, the same arm) as the `Expr::TypeValue` a sort's bare name is, in both bodies and for the path spelling, so `(Ep).em()`, `let t = Ep` + `t.em()` and `(ns.Ep).em()` are the companion call `Ep.em()`. Then: retire `denoted_type_value`'s free-standing-entity arm (JM6ZW's; the `TypeValue` arm covers it), correct `bare_name_denotes_type`'s and `written_type_receiver_occurrence`'s docs, turn the RXT6S pin, and state eponymous / free-standing receivers in kernel-language.md §5.4. A rule body refuses a CONSTRUCTOR reached through a type receiver (WI-20261008-A3FY2) — check `(Ep).em()` and `(Ep).Ep(…)` there. Proposal 055's dot split (PAPX0) is where this sits, beside WI-20261008-R653S / 7B15V.

CONTROL. Each spelling above, in an operation body and a rule body. A forgotten-parentheses construction still names the type (`expected Ep, got Type (Ep)`). A member taking the value (`operation greet(self: Ep)`) reached as `(Ep).greet()` — state what it is refused as, and that the refusal says something useful. `Ep(name: "x").em()`, a dot on a CONSTRUCTED value, keeps the reading it has. Say at the test site which rows fail with the change backed out.

DONE WHEN: the eponymous receiver spellings give the companion verdict the ordinary sort's do, in both bodies; §5.4 says so; the gate is green.

## Changes

### 2026-11-01T17:58:57Z — feedback — claude

DELIVERED as closed by WI-20260902-JB6RS step 5 (user's go, 2026-11-01; rows in 8c96c440). The premise moved under the ticket: since JB6RS a constructor's bare name in a body is its INSTANCE and its type is written with the bracket, `Ep[]` (kernel-language §4.4). So bare `Ep` is no type value: `(Ep).em()` and `let t = Ep` + `t.em()` are refused as a construction without its field `name`, advising `Ep[]`; and every spelling of the type is the receiver that denotes the sort, which §5.4's "a written type" already covers, so no spec text is added. In an operation body `Ep.em()`, `Ep[].em()`, `(Ep[]).em()`, `(test.….Ep[]).em()` and `let t = Ep[]` + `t.em()` answer 8; in a rule body `(Ep[]).em()` and its path spelling bind 8; a fieldless `(Fl[]).em()` answers 9, and `(Fl).em()` is a dot on the value `Fl`, an arity error. THE TWO NOTES: (1) a bare reference constructs (JB6RS); (2) moot, the record is the bracket's `Expr::TypeValue`. THE WHAT LIST: `denoted_type_value` has no free-standing-entity arm (its doc corrected in 8c96c440); the RXT6S pin is turned to the instance reading; a constructor reached through the receiver is looked up by its written name, so `(Ep[]).Ep(name: "x")` is refused as `Ep[].Ep(name: "x")` is, where it constructed (PAPX0, 8c96c440). CONTROLS: `(Ep[]).greet()` over `greet(self: Ep)` is the call with no argument for `self`, refused naming it; `Ep(name: "x").greet()` answers 5 and `Ep(name: "x").em()` is an arity error, the dot passing the value as before. Rows: wi_1y96b_eponymous_type_receiver_test (3), controls only: nothing here changed the reading, so no back-out fails them; the `Ep` spellings answered the same on 6fcc35a5. Full workspace 11,401 passed; scaland 1 + 51 + 793.

