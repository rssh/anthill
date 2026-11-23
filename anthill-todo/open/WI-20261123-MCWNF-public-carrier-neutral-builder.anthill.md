## Attributes

- id: WI-20261123-MCWNF-public-carrier-neutral-builder
- created: 2026-11-23T10:33:26Z

- status: Open
- status_agent: user
- status_at: 2026-11-23T10:33:26Z

- acceptance: cargo-test, scaland-sbt-test

## Description

Public carrier-neutral builder: an application of a functor to children on any carrier (KnowledgeBase::fn_value, public)
WHO NEEDS IT. anthill-traces (its WI-20261122-XZ0QE, the contract evaluator) walks an operation's stored contract clauses — OperationInfo.requires / .ensures, WrittenClause.stored (WI-20261122-517Y5) — and builds goals from them with the parameters and 'result' replaced by values, consts by their literals and a field access over a record folded; it resolves those goals with execute_typed_logical_query_with (WI-20261122-96QKW).
WHAT IS THERE (read from code at 2ab7ca823, 2026-11-23). Reading is carrier-neutral: TermView (head, pos_arg, named_arg, named_field, named_keys) over a TermId and over every Value, a Value::Node included, and ViewItem::to_value. Building is not: the public constructors take TermId children only — make_entity_term(functor, pos: SmallVec<TermId>, named: SmallVec<(Symbol, TermId)>) and alloc(Term). The builder over Value children, KnowledgeBase::fn_value(functor, pos: Vec<Value>, named: Vec<(Symbol, Value)>) -> Value — the single source of the Term-vs-Value::Entity decision (WI-348), used by reify, assert_fact_carrier and the loader's contract_goal_as_written — is private (kb/mod.rs, fn fn_value).
WHY IT MATTERS. A stored contract clause is not always a term: a goal written through a type alias (requires Show[T = Money], x > 0 with sort Money = Int64) is stored by contract_goal_as_written as a Value::Entity whose binding is the written Value::Node, inside a Value conjunction. A client can read it through TermView but cannot rebuild it with values put in, except by lowering it to a TermId first (node_occurrence::value_to_term) — a conversion needed only because the public builders take terms — or by writing Value::Entity { .. } by hand, which restates fn_value's carrier decision outside the crate. anthill-traces does neither: until this lands it reports such a clause undecided, naming this item.
WHAT IS ASKED. A public way to build an application over children on any carrier, with fn_value's contract (a hash-consed Value::Term when every child lowers to a leaf, a Value::Entity otherwise): fn_value made public, or a public twin documented as THE carrier-neutral constructor. Its doc says whether a record's named arguments are put in canonical order as make_entity_term does (canonicalize_record_named_args): fn_value's term branch allocs Term::Fn directly (read from code), which is right for a caller rebuilding a term it read, and a caller building one from scratch needs to know.
WHAT IS NOT ASKED: a change to execute (execute_typed_logical_query_with already takes a Value); a typed builder.
DONE WHEN: a test outside the crate builds an application whose children are a Value::Node, a Value::Term and a native literal through the public builder, and the result reads through TermView as its term twin does (views_structurally_equal); reify, assert_fact_carrier and contract_goal_as_written build through the same function; the named-argument rule is in its doc and a row drives it.

