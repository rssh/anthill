## Attributes

- id: WI-20261124-V260E-a-spec-operation-s-carrier
- created: 2026-11-24T09:11:32Z

- status: Open
- status_agent: user
- status_at: 2026-11-24T09:11:32Z

- acceptance: cargo-test

## Description

A spec operation's carrier bound by several arguments is read off the first: nil = [1] is refused and [1] = nil loads
WHO NEEDS IT. Found with WI-20261124-C6VN0 (the user asked it sized there, 2026-11-24, and filed if large). Any clause or body comparing an empty literal with a value that fixes the element, in that order.
WHAT HAPPENS. MEASURED 2026-11-24 on 1aa2a9e7d, with WI-20261124-C6VN0 in the tree for the rule and operation rows (it changes query routing only), through a probe binary since deleted: refused at load, "type mismatch in anthill.prelude.PartialEq.eq.dispatch: expected matching impl for per-call bindings, got no impl matches -- unresolved: anthill.prelude.PartialEq[T = anthill.prelude.List.T]": rule r() :- nil = [1]; rule r() :- nil() = [1]; rule r() :- [] = [1]; rule r() :- none = some(1) (Option.T); operation r() -> Bool = nil = [1], = nil() = [1], = [] = [1]. Loads: rule r() :- [1] = nil; rule r() :- ?x <=> nil, ?x = [1]. A query built term to term is refused the same way: PartialEq.eq(nil, [1]) through execute_typed_logical_query_with.
WHY (read from the code). The carrier of a spec operation is bound from its receiver argument (receiver_carrier, then bind_spec_params_from_carrier; kb/typing/apply.rs, after the join at ~806). The join of the arguments that bind a parameter (join_repeated_sort_params, kernel-language 8.1, WI-20260926-NEKR0 / WI-20261001-80ZV8) is asked of a DATA sort only (sort_params_join), deliberately: the comment there says a spec's parameters are a provision's, read off the receiver's carrier or the enclosing requires. So the first argument's type is the carrier, and nil's open element slot stays open. 8.1 states the join for an operation's own [A] and a data sort's parameter; 5.4 says a list of nothing stands first as well as second for List.append(acc, [1]). Neither says it of a spec's carrier.
WHAT IS ASKED. A language decision, then the code: does a spec operation's carrier that several arguments bind take their join, as 8.1's parameters do? Questions for the wording: (1) what the join is where the arguments are two providers of an abstract sort (eq(circle, square), both providing Shape): the abstract sort, a refusal, or unchanged (first argument); (2) whether only an open slot is filled from a later argument (nil beside [1]: List[T = ?] meets List[Int64]), which leaves every program that loads today with its verdict, or the full join; (3) the sites: operation body, rule body (op_slot_route pins a sort parameter in argument order too, per the join_instantiation.rs doc), query.
NOT ASKED. A default element type for an empty literal nothing fixes: nil = nil may stay refused (WI-20261124-C6VN0 types it through a declared variable).
DONE WHEN. rule r() :- nil = [1] and the operation-body spelling load and decide false, none = some(1) likewise, at the same verdicts as the swapped order; the swapped order unchanged; a row for the abstract-sort case at the decided reading; families green with the verdict lines moved (if any) committed.

