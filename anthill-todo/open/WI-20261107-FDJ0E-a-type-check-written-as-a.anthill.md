## Attributes

- id: WI-20261107-FDJ0E-a-type-check-written-as-a
- created: 2026-11-07T09:38:41Z

- status: Open
- status_agent: claude
- status_at: 2026-11-07T09:38:41Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A TYPE CHECK WRITTEN AS A QUERY OR A RULE-BODY GOAL IS ANSWERED AS TYPE CHECKING ANSWERS IT (user, 2026-11-07, from WI-20261021-Z2P21: 'rules should match typing', from the beginning — a defect, not a new design; proposal 058 §2: every `provides` is a row of one relation, an unconditional provision a fact and a conditional one a rule, and instance resolution is the language's own relational search over it). TODAY (measured on c80394e1): a bracket on a sort written as a goal or a query is the atom `WeakOrd(T: Int64)`, matched only against clauses headed by the sort — a written `fact WeakOrd[T = Int64]` — and never against the provision rows (`SortProvidesInfo`, which `anthill.reflect.provides(Int64, ?s)` lists, `WeakOrd`, `PartialOrd`, `Ord` among 11) or the conversions in the requires chain (`Ord`'s `provides WeakOrd[T = T]`, prelude/ordered.anthill). Over `namespace z.q1 import anthill.prelude.{Int64, String, Float, WeakOrd, Ord, Pair}`, `anthill query -i anthill.prelude.* '…'` answers no solutions for each of `WeakOrd[T = Int64]`, `Ord[T = Int64]`, `WeakOrd[T = String]`, `WeakOrd[T = Pair[A = Int64, B = Int64]]` (Pair's conditional `provides WeakOrd[Self] :- WeakOrd[A], WeakOrd[B]`), `WeakOrd[T = Float]` and `WeakOrd[T = ?t]`; and in a rule, `rule guarded(?c) :- WeakOrd[T = Int64], WeakOrd.compare(1, 5, ?c)` answers nothing where `WeakOrd.compare(1, 5, ?c)` alone gives -1 and the guard at a declared parameter, `rule cmp[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], WeakOrd.compare(?a, ?b, ?c)` cited as `cmp(1, 5, ?c)`, reads the provisions (stored `find_dictionary(WeakOrd[T = ?#1], …)`) and gives -1. WANTED: the goal and the query hold where type checking finds the instance — a written fact, a provision, a conversion, a conditional provision whose condition holds — so the first four answer true, `WeakOrd[T = Float]` fails (Float provides no WeakOrd), `guarded` gives -1; a written `fact Pair[U = String, T = Int64]` still answers `:- Pair[T = Int64, U = String]` (WI-20261022-7EXEY's, WI-20260902-JB6RS's and WI-20261019-TCSGT's rows keep their answers). A guard written with no introducer is then not refused (user: the keyword form's refusal is for consistency with `require`, 'we can allow both'); 060.1 Q6's 'refused with require[X] gone' is superseded. TO DECIDE when scoping: `WeakOrd[T = ?t]` with the carrier unbound — every type that provides it, or waiting until bound (type checking has no single answer there); one answer or two where a fact and a provision both hold. The 9SNR2 addendum on Z2P21 is answered by this: `Store[State = Buf[T = String]]` before `Store.peek(buf(v: 1), ?r)` is a check that fails, nothing providing it.

