## Attributes

- id: WI-20260922-QHDGC-require-spec-t-t-is-refused
- created: 2026-09-22T07:55:46Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-22T09:39:42Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

`require[Spec[T = ?t]]` is refused although a logical variable IS a type everywhere else

DECIDED BY THE USER, 2026-09-22, during WI-20260921-3G1YT: there should be no
difference between a type parameter and a logical variable in type position, so this
is a BUG rather than a namespace distinction.

MEASURED — four spellings over one fixture (a `Desc` spec, `Leaf`/`Twig` carriers,
`fact item(leaf())` / `fact item(twig())`), on this tree:

  Desc[?t]                  in a bounding guard            LOADS
  ?x: ?t                    as a head parameter type       LOADS
  require[Desc[T = A]]      rule type param, guarded       LOADS
  require[Desc[T = ?t]]     logical variable               REFUSED

The refusal reads "`Desc`'s type parameter list takes sorts and its own type parameter
names; this argument is neither" — the same message a literal `require[Desc[T = 3]]`
gets.

ONE SITE IS OUT OF STEP, and the table is what says so: if a logical variable were
genuinely a category error in type position, the guard and the head parameter would
refuse it too. They do not. The kernel premise (CLAUDE.md, first paragraph) is that
logical variables appear in types as in logical terms and types unify; two of the three
type positions already honour it.

THE FIX IS LOCAL. `report_dropped_spec_binding` (kb/load.rs) exempts a binding that
names a SORT or the spec's OWN declared parameter; it must also exempt a logical
variable. The four other carriers WI-20260909-51W18 made loud — a literal, an entity
constructor, a rule name, a tuple type — stay refused, and each needs its own row so
the widening is attributable.

WHY THE CENSUS THAT CHOSE THE NARROW RULE DOES NOT DECIDE IT. Its justification reads
"every free-name binding in the corpus spells the spec's own declared parameter — Eq[T]
x24, Desc[T] x23 ... Anything else was already a mistake; it just could not say so."
That establishes nobody WROTE `?v` there, not that writing it is meaningless — the same
"unread does not imply unowed" inference WI-20260921-3G1YT was filed to reject, one
channel over.

ACCEPTANCE
 - `require[Spec[T = ?t]]` loads AND BINDS — a DRIVEN row in which the dictionary is
   selected per solution and answers at TWO different carriers, not a row that only
   asserts a clean load;
 - the four other invalid carriers stay refused, each with its own row, so the
   widening is attributable rather than "the check got looser";
 - the guard (`Desc[?t]`) and head-parameter (`?x: ?t`) spellings are named as the
   controls that ALREADY pass, per CLAUDE.md's control discipline;
 - the `require[Desc[T = A]]` rule-type-parameter spelling keeps working.

## Changes

### 2026-09-22T09:39:30Z — feedback — user

DELIVERED. One rung in `require_spec_binding_occurrence` (kb/load.rs): a `Term::Var` binding routes through `build_body_atom_occurrence`, the owner of the parse-var -> KB-var `var_map` mint. The four other carriers stay refused, one driven row each.

WHAT 'BINDS' TURNED OUT TO MEAN — the acceptance's first item, answered precisely, because the honest answer is narrower than the phrasing.

THE VARIABLE IS THE CLAUSE'S OWN. The stored find_dictionary goal carries the SAME De Bruijn index as a sibling body goal's `?t`. That is the sharp row and the only one in the file that fails under the obvious wrong implementation: a local `kb.fresh_var` at the binding site loads clean, retains a `Var`, passes the other thirteen rows, and mints a SECOND index — a variable nothing in the clause binds. MEASURED by making that mutation.

IT IS NOT BOUND BY SELECTION, and it must not be. A logical variable reads as the ABSTRACT case the spec already defines — 'an element it leaves unwritten is matched abstractly and does not discriminate' (kernel-language.md, WI-20260913-J38VE). MEASURED on a two-parameter spec, where the bracket is load-bearing:

  Sp[C = Red, P = Int64]   -> 7, DEFINITE
  Sp[C = Red, P = ?p]      -> residual     a variable does NOT select
  Sp[C = Red]              -> residual     and this is the spelling it matches

A FIRST READING OF THIS WAS WRONG AND IS RECORDED SO IT IS NOT REDERIVED. Measured on a ONE-PARAMETER fixture, the conclusion was 'nothing reads the bracket at all' — every spelling, concrete `Desc[T = Leaf]` included, answered both carriers. The fixture was the fault: a spec operation names its CARRIER, so on a one-parameter spec the anchor pins the sole element and the bracket has nothing to add. J38VE's mechanism is only visible where the spec has an element no call can name.

THE ACCEPTANCE ROW, on a fixture that can express it: `require[Sp[C = ?c, P = Int64]]` over two carriers answers 7 AND 9, both DEFINITE — the dictionary selected per solution with a variable at C — and its control `Sp[C = ?c]` residualizes at both. So the row measures the bracket doing work rather than the fixture answering on its own.

THE HAZARD THAT DID NOT MATERIALIZE, checked rather than assumed: a variable reaching `written_element` as a concrete term would be REFUSED against every provider row, turning a load error into a permanent silent delay. `written_element` declines anything that is not a SortRef/Parameterized, so the variable falls to X9PB4's wildcard — and at a genuine provider TIE it DELAYS rather than firing `debug_assert!(false, "two providers answer")`. Driven.

ALSO DRIVEN: the three other variable surfaces (`T = ?`, positional `[?t]`, `[?]`) all land on the declared T slot; all four TERM surfaces (constraint, ensures, aggregation, direct-bind) load; nested `Box[E = ?t]` loads; and the arity/param-name checks still fire, so a variable cannot hide an over-application, a bogus name, or a duplicate slot.

CONTROLS NAMED, per CLAUDE.md: the guard (`Desc[?t]`) and head-parameter (`?x: ?t`) spellings pass on BOTH trees — they are the evidence this site was the one out of step — and `require[Desc[T = A]]` keeps threading at both carriers.

SPEC UPDATED (kernel-language.md, the require-bracket section) and the stale doc on report_dropped_spec_binding corrected: five carriers, now four.

/code-review, two findings, both fixed: a tie assertion that passed vacuously on an empty solution set, and report_dropped_spec_binding's None arm, which lost its only reachable carrier (the variable was it). The None arm is ANNOTATED, NOT DELETED — 'I found no carrier' is not 'no carrier exists', which is this ticket family's own rejected inference.

SCALAND: nothing to port. It has no require[] dictionary channel at all; a requires there only links a parent scope. Suite green (578+35+1, exit 0).

cargo-test: 4882 passed in the main binary, 36 binaries, 0 failed.

