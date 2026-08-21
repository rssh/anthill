## Attributes

- id: WI-20260821-FQC85-implement-proposal-061-a
- created: 2026-08-21T14:23:09Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T14:23:09Z

- acceptance: cargo-test, scaland-sbt-test

## Description

IMPLEMENT PROPOSAL 061 — a logical rule's head names a DECLARED predicate.

A predicate is the only name in the language with no declaration: four core constructs,
and only `rule` brings a name into existence as a side effect of using it. That is the
whole of WI-980 — the head's name is created during the pass that decides it, so WHEN the
ladder is asked was load-bearing. Every other name kind is immune because pass 1 defines
all of them first (WI-321).

THE RULE (061): a rule head is always a clause OF something. A predicate whose heads are
all in ONE file is auto-declared, in the scope §WI-896's ladder already picks; one with
heads in MORE THAN ONE file must be declared explicitly, or the load is refused naming the
files. The file is the unit for 059 §Definitions' own reason -- it is the smallest place
where "two parties" is real, and it is the unit `import` already uses.

CENSUS, MEASURED over stdlib + anthill-stl + examples/github-todo: 102 predicates carry
rule heads and EVERY ONE has its heads in exactly one file; zero span more than one. So
the multi-file requirement refuses nothing that exists, and the 43 distinct
rule-introduced names are all auto-declared.

WHAT IT REMOVES from the loader, all of it cross-FILE and therefore exactly on the
auto-declaration boundary (each measured under WI-980):
 * a sibling file's head MOVED another file's clause -- `zlib.q` 2->1 and `zdemo.q` 0->2,
   with the first file unedited;
 * a mutual-import cycle picked its owner by FILE ORDER;
 * the same pair at one address, split across files, gave two different programs;
 * ownership had to be keyed per `(scope, name, FILE)` because two heads of one predicate
   can sit in files with different imports (WI-995).
What remains is the single-file case, decided by §WI-896's ladder as today.

EQUATIONAL RULES ARE OUT OF SCOPE. `lhs <=> rhs` extends UNIFICATION; its clauses index
under the connective, not under its subject (WI-898), so the subject owns no clauses and
there is no predicate to declare. The two shapes already earn different symbol kinds for
that reason. `[simp]`'s enablement is untouched.

DECIDE BEFORE IMPLEMENTING -- 061 lists five, and the first is on the critical path:
 1. SPELLING. A body-less head is today an ordinary FACT (`rule parent("alice","bob")`),
    so a declaration must be distinguishable from a ground fact whose arguments happen to
    be variables -- `rule p(?x, ?x)` is a legitimate clause. All-variable form, a keyword,
    or an arity-only form.
 2. Does the declaration fix ARITY? Clauses may differ in arity today.
 3. A single-file mutual cycle is auto-declared with no outermost scope to pick, so
    WI-980's cycle handling survives for it. State it; do not assume it away.
 4. A declaration must NOT join the dispatch surface (059: the surface is exactly the
    operations), while 052 OQ2 wants `Sort.rule` citable as a `Relation[T]` -- the two
    proposals must agree on what a declaration makes citable.
 5. The multi-file rule is a WHOLE-PROGRAM property: adding a second file can require a
    declaration elsewhere. Same discomfort 059 records for secondary entries; record it.

ACCEPTANCE: drive it. The four cross-file shapes above must each be a located load error
naming the files, or load with the declaration present and the clauses on ONE predicate --
assert the clause counts and the answers, not that it loads. Single-file shapes keep
today's behaviour (control: WI-980's own suite stays green). An equational head is
untouched in both spellings (control). Say at each site which rows fail on a back-out.
cargo-test green via rustland/scripts/test.sh.

