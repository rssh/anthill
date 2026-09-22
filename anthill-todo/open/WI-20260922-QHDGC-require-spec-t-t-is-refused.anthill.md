## Attributes

- id: WI-20260922-QHDGC-require-spec-t-t-is-refused
- created: 2026-09-22T07:55:46Z

- status: Open
- status_agent: user
- status_at: 2026-09-22T07:55:46Z

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

