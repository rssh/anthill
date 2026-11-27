## Attributes

- id: WI-20261127-V69PS-proposal-077-a-spec-s-rule
- created: 2026-11-27T22:40:56Z

- status: Open
- status_agent: user
- status_at: 2026-11-27T22:40:56Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261127-AGR9S-resolver-the-continuation-is, WI-20261127-DAPCN-proposal-060-1-9-a-rule-s

- tags: proposal-077, typing

## Description

Proposal 077: a spec's rule member is implemented by a provision, and a sort's domain is an ordinary SortDomain provision -- stages S1-S5, S1 first
WHAT. docs/proposals/077-rule-members-and-domain-provisions.md (draft with the user 2026-11-27; its open questions decided 2026-11-27/28, commit 553b4523b). A spec may declare a RULE member and a provision implements it with clauses written in its where block, conditional or not; a provision is an anonymous sort and its rules are that sort's (section 2). A goal at a spec's rule member through a dictionary is dispatched by the resolver to the provider's clauses, in place (section 3; apply_domain generalised). A sort's domain is then an ordinary provision the loader derives and an author could write (List provides SortDomain[T = List[T = T]] :- SortDomain[T = T] where rule fill(nil) :- true ... end), a typed column is a requirement (section 4), and the per-sort table goes (section 6: sort_domains, SortDomainEntry, fill_derive::FINITE_PRIMITIVES, __domain_sub, domain_evidence_of_type). SortDomain gains the member check beside fill (section 9), and anthill.kernel.domain stops being a name a program writes.

WHY (077's measured rows, 2026-11-27). The table and the provision rows disagree where a provision is written (1 / 3 / none on three paths); the general path refuses its own form (rule declaredSD[A](?w: List[T = A]) :- SortDomain[T = A], ...); a hand-written domain cannot read its element's domain; anthill.kernel.domain is shallow and carries no instance (Wrap[T = Bool].isT(true) answers nothing).

DECIDED, AND BINDING ON THE STAGES. Question 8: a trusted call runs nothing; a call that is not trusted runs the deep check in front of its body and the fill after it. Questions 9 and 4: every type gets a derived provision, per sort or per type shape (tuple, function type); the outer-type test with no dictionary is dropped. Question 5: a domain is written on its carrier only; sort W ... provides SortDomain[T = Colour] is refused at load. Question 10: the member is named check. Question 3 (taken as agreed, not confirmed): coherence by carrier is SortDomain's alone. From 060.1 section 8.18: the dictionary is always passed and trusted wraps it, so has[X](v: X) needs requires SortDomain[T = X]. Section 5.2 (open conditions) is NOT built: 060.1 section 9's S3-S4 land with this ticket's S3 instead.

STAGES (077 section 8). S1 MEASURE, nothing built: (a) the cost of SortDomain rows for every sort, optimized build; (c) a census of short-name collisions in SortOpsTable between an operation and a would-be rule member; (d) how TypeValue reaches a tuple and a function type today -- reuse its derivation if it is per shape; (e) the rows the deep check in front of a body moves. S2 rule members in a provision's where block (tree-sitter and fastparse), dispatch in the resolver, the derivation emitting provisions read into the old table so no answer moves. S3 lookup by head, rows for every sort, typed columns through the requirement machinery -- together with WI-20261127-DAPCN's S3-S4. S3b check derived beside fill, the deep check in front of a call that is not trusted. S4 the table deleted, primitives in stdlib source, hand-written domains as provisions. S5 the kernel-language text (sections 5.3, 8.7), 060 section 2.3, 066 section 3, 067 section 3 -- agreed with the user first.

PREREQUISITE OF S3b, inside this ticket: WI-20261124-YFD7F's evidence rule extended to the inside calls it leaves on the plain dictionary -- a citation from an operation body, a clause holding a cut, a goal under not or a quantifier, a construction with a variable -- so the deep check's second walk is left at a true entry only.

ORDER (077's status line): after 076 Stage A (WI-20261127-AGR9S); S1-S2 after DAPCN's S1-S2; S3 with DAPCN's S3-S4; S4-S5 last. 076 Stage D's @[fair] on Fillable.fill needs this ticket's S2. WI-20260911-WT8WG's items 3 and 4 are this ticket's S4 and S5.

DONE WHEN. S1 reported first and the plan revised with the user on it. Then, each stage's rows DRIVING the capability with back-outs measured at their site: a written provides SortDomain[...] where rule fill(...) ... end loads and answers (S2); the witness row answers one count on every path and declaredSD loads and answers (S3); Wrap[T = Bool].isT(true) answers 1, noDict[X]() without requires SortDomain[T = X] is refused at load, cons(head: 5, tail: "junk") is refused by a check-only column (S3b); Box written as a provision answers 4 / 2 / 3 at Colour / One / Box[T = One] (S4); kernel-language text agreed before S5 lands; full workspace via rustland/scripts/test.sh, families, scaland testFull.

