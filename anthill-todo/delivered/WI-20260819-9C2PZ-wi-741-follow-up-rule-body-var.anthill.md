## Attributes

- id: WI-20260819-9C2PZ-wi-741-follow-up-rule-body-var
- created: 2026-08-19T06:15:07Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-19T10:07:35Z

- acceptance: cargo-test

## Description

WI-741 follow-up (rule-body var typing): collect_rule_var_types never INSTANTIATES a callee's type parameters, so every call to a spec op in the whole KB records the SAME parameter symbol for variables of unrelated types. `eq(?x, "root")` records ?x at `anthill.prelude.PartialEq.T`. WI-741 made that survivable -- a bare parameter no longer displaces or contradicts a concrete type (constrain_vid), and relation_clause_columns normalizes it to a var keyed BY THE PARAMETER SYMBOL so column correlation survives -- but the conflation itself is untouched. THREE consequences remain, each measured live (2026-08-19): (1) TWO INDEPENDENT CALLS ARE TREATED AS ONE. `rule twoeq(?x, ?n) :- gen(?x, ?n), eq(?x, "a"), eq(?n, 1)` records BOTH ?x and ?n at the one PartialEq.T, so the relation's two columns share one var and the CORRECT citation `twoeq("a", 1)` is REFUSED: 'argument binding column `n` has an incompatible type'. Verified pre-existing -- the identical refusal reproduces with WI-741 backed out, so this is the conflation, not the WI-741 repair. (2) A VARIABLE FORCED EQUAL TO A CONCRETE ONE DOES NOT INHERIT ITS TYPE. `rule r(?x, ?y) :- eq(?x, ?y), parent(of: ?x, is: ?)` types ?x String and leaves ?y at the parameter, though `eq` forces them equal and the information is in the call. (3) WHICH CORRELATION CLASS A VAR JOINS is decided by whichever parameter reached it FIRST (WI-741 made a parameter never displace a recorded entry, so it is at least stable): a var constrained by `eq` then `div` keeps PartialEq.T and never joins Div.T's class, though the real constraint links all three variables. FIX DIRECTION: instantiate the callee's own type parameters with FRESH vars PER APPLICATION, in constrain_application / collect_term_type_constraints. Then `eq(?x, ?y)` gives both args one fresh var (correlated), a second `eq` gets a different one (independent), and unify_types against a concrete type binds THAT per-call var instead of the one global alias. With per-call freshening in place, WI-741's originally-hypothesized 'resolve var_types through the substitution collect_rule_var_types drops' becomes SOUND and delivers (2) as well -- it is unsound TODAY precisely because that substitution binds the single shared alias (WI-741 measured it binding PartialEq.T's alias to String in a rule whose other eq call was over Int64, which would have typed the Int64 variable String; and for `eq(?x, "root")` the substitution is EMPTY, because a literal argument is not a var and so constrains nothing at all). BLAST RADIUS -- var_types has THREE readers: the contradiction report, the dot / spec-op dispatch receiver types, and the WI-603 occurrence stamps. Measured proxy for how load-bearing they are: DROPPING the parameter entry entirely (a cruder change than freshening) fails 57 of the 74 WI-714 tests, most of them on 'ambiguous dispatch of anthill.prelude.PartialEq.eq: 53 instances provide PartialEq and the call selects none'. So this reaches dispatch across the whole stdlib and needs its own tests. Note also that WI-741 showed the corpus contains programs whose type errors are MASKED by the conflation: lifting one false contradiction surfaced a genuine Int64/Float division in examples/webots-modelling/lf1/safety_gps.anthill (repaired under WI-741) -- expect this change to surface more, and treat each as a real find rather than as fallout. ACCEPTANCE: `twoeq("a", 1)` above LOADS and drains 1 row while `twoeq(1, "a")` stays a loud refusal (independence, both polarities); `rule r(?x, ?y) :- eq(?x, ?y), parent(of: ?x, is: ?)` types BOTH columns String, driven through a citation that an Int64 column would refuse; the WI-714 correlation pins (wi714_applied_correlated_columns_reject_contradiction, wi714_applied_unconstrained_column_accepts_and_narrows) still pass UNCHANGED; cargo-test green via scripts/test.sh.

## Changes

### 2026-08-19T09:50:33Z — feedback — claude

IMPLEMENTED (not yet committed). The ticket's fix direction held up under instrumentation,
and it needed a third half the ticket did not name — plus a fourth thing /code-review found
that the first cut got badly wrong.

WHAT SHIPPED, in rustland/anthill-core/src/kb/typing.rs:

1. PER-APPLICATION INSTANTIATION. `instantiate_declared_type` rebuilds a callee's declared
   param / field type with every type parameter it mentions replaced by a fresh variable
   minted for THIS application (`ParamInstantiation`, one map per call, so one call's
   arguments stay correlated and the next call's do not). Both collector twins use it —
   `constrain_application` (body occurrences) and `collect_term_type_constraints` (the head
   term) — and both the op-param and the entity-field branch of each.

   WHICH OCCURRENCES COUNT is derived from the mechanism rather than guessed:
   `declared_type_param_var` answers for exactly what `walk_type` collapses into one
   canonical variable, i.e. what actually conflates — a `Var::Global` (an operation's
   bracket parameter, WI-1082's elaborated self slot) or a parameter NAME the WI-954
   canonical map answers for. A name with no canonical variable is a rigid abstract type and
   is deliberately left alone. The two channels' agreement is MEASURED, not argued:
   instrumented across the whole wi_tests corpus, ZERO names diverged.

2. THE LITERAL CHANNEL. A literal argument was not a variable, so it constrained nothing at
   all — which is why the ticket's own acceptance could not be met by freshening alone.
   Without it `twoeq("a", 1)` and `twoeq(1, "a")` are BOTH accepted (two independent but
   UNTYPED columns). `constrain_literal_arg` pins the parameter to the literal's own sort,
   gated on the parameter having been instantiated by THIS application.

3. RESOLVE THROUGH THE SUBSTITUTION. `collect_rule_var_types` now walks its finished
   `var_types` through the substitution it used to build and drop. This is the step WI-741
   declared unsound, and it WAS unsound then for the reason WI-741 gave; per-application
   instantiation is exactly what makes each binding local to the call that made it.

4. WHO OWNS A DISAGREEMENT (the /code-review repair, see below). `var_types` answers "what
   do this variable's own positions say"; a per-call parameter says nothing and is recorded
   only as a placeholder. So a DECLARED position takes over from a placeholder, and a
   disagreement involving a placeholder is an ARGUMENT error at that call — never
   `subst.contradiction`. Only two DECLARED positions of one variable disagreeing set the
   flag, which is the shape nothing else reports.

ACCEPTANCE, all measured:
 * `twoeq("a", 1)` loads and drains its 1 row; `twoeq(1, "a")` is a loud refusal naming
   column `x`. Both polarities.
 * a variable `eq` links to a concretely-typed one inherits the type, and it reaches the
   PUBLISHED SCHEMA — a two-clause fixture makes the lub report column `y` disjoint, which
   it can only do if the eq clause published String.
 * consequence (3) is repaired transitively: `eq(?x, ?y)` beside `gt(?y, ?z)` now puts all
   three in one class, so `chain(2, 2, "x")` is refused on column `z` while `chain(2, 2, 1)`
   loads and drains.
 * the WI-714 correlation pins pass UNCHANGED (all 74).
 * full workspace green via scripts/test.sh: 29 binaries, 5262 tests, 0 failures.

CONTROLS. Each half was backed out IN PLACE (mutated to a no-op, not deleted, so every
fixture still loads) and the per-row result is a table in the new test file's header. Two
rows pass under every back-out and say so at their sites — they are the value arms, the only
evidence in the file that the relations still RUN, since every measuring row is a refusal.

WHAT /code-review CAUGHT, and it was right. The first cut set `subst.contradiction` on every
disagreement. That flag makes `type_rule_bodies` skip the rule — no dispatch, no WI-603
stamping, and for a namespace-level rule no report at all — which SUPPRESSES the located
error the ordinary call check raises. Three shapes went silent, verified against HEAD:

  row(a: ?a, s: ?s), eq(?a, ?s)   HEAD: eq.b (op-arg): expected Int64, got String -> LOADS CLEAN
  holder(f: ?f), eq(?f, 0)        HEAD: eq.b (op-arg): expected Float, got Int64  -> LOADS CLEAN
  eq(?x, "s"), scored(pts: ?x)    HEAD: eq.b (op-arg): expected Int64, got String -> LOADS CLEAN

The third is mine, not the review's, and it is the one that decided the shape of the repair:
the test has to be on the RECORD's provenance, not only on this call's, because the literal
pins the placeholder first and it is the LATER declared position that must take over. All
five shapes now match HEAD byte for byte, spans included, and are pinned as four permanent
tests. That directly inverted the ticket's instruction ("expect this change to surface more
masked type errors") — the first cut masked three instead.

The review's other three findings, each resolved by measurement rather than by argument:
 * `relation_clause_columns` discarded the contradiction flag that decided whether
   `var_types` had been resolved, so one clause of a relation could publish RAW column types
   while its siblings published resolved ones. Now resolved UNCONDITIONALLY: a failed
   unification records no binding, so there was nothing the guard protected.
 * a higher-kinded parameter in FUNCTOR position (`M[T = A]`, delay.anthill) is not reached.
   Traced: `Term::Fn`'s functor is a `Symbol`, not a child term, so no variable is
   representable there, and `walk_type` does not collapse it either — the position never
   conflates. Recorded at the site as a representation bound.
 * "nothing bounds how many other requirement guards flip from no-answer to indefinite
   residual" — censused. With `guard_over_arg_types` instrumented on both trees, every
   guard verdict in the whole corpus is identical except ONE fixture: WI-1040's own
   `delay` shape, whose single `DontFire` became a `Suspend`.

ONE BOUNDARY TEST MOVED, in the direction its own contract asks for.
`wi1040…an_unbound_carrier_…` used to answer NOTHING; it now answers one INDEFINITE
residual. Traced, not read: `?x`'s only typing source is `Desc.describe(x: T)`, the typer
recorded it at the bare `Desc.T`, WI-603 stamped that onto the variable occurrence, and
`witness_arg_types` read it back as the runtime carried type — a perfectly readable nominal
head that provides nothing, so the guard decided DontFire. That is a requirement decided
FALSE off an under-determined binding, which FindDictOutcome's own doc forbids ("never
NAF-decide, WI-519 / WI-067"). The fresh variable is headless, so the guard now suspends as
designed. Acceptance (d) is still NOT delivered — a definite `7` needs the clause-level
re-fire — and the test is renamed and now pins "exactly one answer, and it is indefinite".

RETIRED, on measurement rather than on reasoning: WI-741's two `constrain_vid` arms (a bare
parameter never displaces / never contradicts) and `relation_clause_columns`'
parameter-symbol-keyed variable mint, plus the two predicates that backed them. With the arms
instrumented, the whole wi_tests corpus reached them ZERO times once instantiation ran ahead
of them. The WI-741 test file's docs are updated to the new mechanism with RE-MEASURED
controls (the old ones named deleted code); its seven tests all still pass.

ONE ARM IS UNEXERCISED and says so at its site: the `Value::Node` carrier path in
`instantiate_declared_type` is reached exactly TWICE in the whole corpus, both times with
zero variables, so its freshening has never run. It also reaches the VARIABLE spelling only.
Both bounds go live together when the WI-342 P4 producers start handing this collector
Node-carried parameterized types.

BLAST RADIUS, measured rather than predicted: the ticket expected more masked type errors to
surface. NONE did — no example, stdlib file or smt-gen proof changed behaviour. No
measurable cost either: wi_tests 3151 passed in 197.26s against a 3147-in-196.16s baseline.

kernel-language.md 5.3 gains one paragraph, "What types a rule's variables", stating the
per-call rule and its observable consequences with the examples above.

