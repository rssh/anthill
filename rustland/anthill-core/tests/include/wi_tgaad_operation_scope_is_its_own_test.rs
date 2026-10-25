//! WI-20261025-TGAAD — AN OPERATION'S SCOPE IS ITS OWN, ALSO WHERE A SORT SHARES ITS NAME.
//!
//! A sort that shares its name with an operation is one symbol (kernel-language.md §4.4),
//! and the operation's scope was minted from that symbol, so it was the sort's scope: a
//! rule in the sort's body read the operation's parameter `c` where the namespace has a
//! relation `c`, and answered nothing; `import ns.{T}` bound the operation's type
//! parameter; the sort took `Pos[T = Int64]` from `operation Pos[T]`; a sort member and a
//! parameter of one name were one symbol. Each operation now declares its signature's
//! names in the scope it opens (`SymbolTable::operation_scope`), whose owner is still the
//! operation. A sort member keeps the qualified name a parameter spells too, whichever is
//! declared first (`SymbolTable::define`, `SymbolTable::declaration_at`), and the type
//! parameter readers answer for the sort, the operation's own read through
//! `KnowledgeBase::operation_type_param_syms`.
//!
//! Every row runs both declaration orders.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ─────────────────────────────────
//!
//! Measured one part at a time, over this file and the pair's neighbours (GJVVW, 7EXEY,
//! WI-974, WN9P8, WI-977, WI-954, WI-993, JB6RS, the induction rows); the full workspace
//! for the parts no row of those reached.
//!
//! Rows of this file by their first words; `GJVVW ×8` is eight rows of that file.
//!
//! | part backed out | rows that fail |
//! |---|---|
//! | the operation's scope (`operation_scope` minting the sort's) | `a_rule_in_the_sorts_body`, `an_import_reaches_no_type_parameter`, `the_sort_takes_no_type_parameter`, `the_operations_body_reads`, `a_wildcard_import`, `a_callback_parameter`, `a_callbacks_flow`, `a_nested_sort`; GJVVW ×8 |
//! | the sort's link to its namespace when the operation came first (the `sort` arm) | `a_rule_in_the_sorts_body`, `a_sort_member_and_a_parameter`, `a_callback_parameter`, `a_nested_sort`, `the_operations_body_reads`, `the_operations_requirement`, `the_operations_result`; 7EXEY ×7, WI-974 ×2 — `unresolved name 'Int64'` in the sort |
//! | a sort member keeps the path (`SymbolTable::define`) | `a_sort_member_and_a_parameter`, `a_nested_sort`, `a_callbacks_flow`, `the_sort_and_the_operation_each` |
//! | the `sort` arm reusing a place (`declaration_at`) | `a_nested_sort`, `a_callbacks_flow`, `the_sort_and_the_operation_each` |
//! | the `entity` arm reusing a place | `a_sort_member_and_a_parameter`, `a_callback_parameter` |
//! | the readers answering the sort for the pair (`type_param_scope`) | `the_sort_takes_no_type_parameter`; 7EXEY ×2, WI-974 ×1 |
//! | the dotted projection asking the operation for its own parameter | WI-974's `an_operations_own_parameter_projects_beside_a_same_named_sort_in_both_orders` |
//! | the named slot read off the operation (`forwarded_binder`) | `an_operations_named_slot_forwards` |
//! | the parameter record read off the scope (`op_info::extract_params`) | `a_sort_member_and_a_parameter`, `a_callback_parameter`, `a_callbacks_flow`, `a_nested_sort`, `the_sorts_induction_schema` |
//! | `result` read off the scope (`region::resolve_op_result_sym`) | `the_operations_result` |
//! | a callback's result, a callback's places read off the scope (`flow_derive`, `register_callback_places`) | `a_callbacks_flow` (each) |
//! | the parameter's type recorded under its place (`load_operation`) | `a_parameters_field_path` |
//! | the wildcard and its import parent skipping a place | `a_wildcard_import` (each) |
//! | the induction schema skipping a place | `the_sorts_induction_schema` |
//! | the typer's referencing scope (`TypingEnv::referencing_scope`) | 106 of the 107 rows measured |
//! | the member alignment's scopes (`signature.rs`) | 26 rows of the workspace: `spec_op_requirement_at_member` ×16, 0K8WD, 0RP29 ×2, 159S9, BQHGD, JPSDH ×2, VNQTR ×3 |
//!
//! Two parts fail no row, by what was measured. `canonical_sym` answering a place for
//! itself is reached where a sort member holds the path (the operation's `T`, `b`,
//! `result` here) by the type-parameter readers, the provider index and the requirement
//! keys, and the member answers each of those the same in every program found.
//! `OwnTypeParams::of` reads the operation's scope for the symbol spelling of a spec
//! operation's own parameter in its row, which every program found spells as the
//! variable — guardians' `wide_row` among them.
//!
//! The controls pass either way, by design: the renamed parameter, the sort alone, an
//! operation of another name.

use anthill_core::eval::Value;

use crate::common::{
    assert_refused_naming, definite_unary, interp_for, load_errors_of, load_errors_of_files,
    load_kb_with, run_int64,
};

/// `decls` in namespace `ns`, after the imports every row uses.
fn program(ns: &str, decls: &str) -> String {
    format!("namespace test.tgaad.{ns}\n  import anthill.prelude.{{Int64, Bool}}\n{decls}end\n")
}

/// The two orders of `first` and `second`, named.
fn both_orders<'a>(first: &'a str, second: &'a str) -> [(&'static str, String); 2] {
    [
        ("the sort first", format!("{first}{second}")),
        ("the operation first", format!("{second}{first}")),
    ]
}

/// The definite `Int64` answers of `relation(?x)`.
fn answers(src: &str, relation: &str) -> Vec<i64> {
    definite_unary(&mut load_kb_with(src), relation)
        .into_iter()
        .map(|v| match v {
            Value::Int(n) => n,
            other => panic!("`{relation}` answered a non-Int64 {other:?}"),
        })
        .collect()
}

/// The ticket's first program: the sort's rule reads the namespace's relation `c`, not the
/// operation's parameter, and the operation still reads its own. The CONTROL is the
/// parameter renamed, which answers 1 either way by design.
#[test]
fn a_rule_in_the_sorts_body_reads_the_relation_not_the_parameter() {
    let sort = "  fact c(1)\n  sort Pos\n    entity pk(v: Int64)\n    rule inner(?x) :- c(?x)\n  end\n";
    let go = "  operation go() -> Int64 = Pos(5)\n";
    for (param, what) in [("c", "a parameter named like the relation"), ("d", "CONTROL, renamed")] {
        let op = format!("  operation Pos({param}: Int64) -> Int64 = {param}\n");
        for (order, decls) in both_orders(sort, &op) {
            let src = program("pin", &format!("{decls}{go}"));
            assert_eq!(answers(&src, "test.tgaad.pin.Pos.inner"), vec![1], "{what}, {order}");
            assert_eq!(run_int64(&src, "test.tgaad.pin.go"), Ok(5), "{what}, {order}: the operation reads `{param}`");
        }
    }
}

/// The ticket's second program: the operation's type parameter is no member of the
/// namespace's sort, so no import reaches it.
#[test]
fn an_import_reaches_no_type_parameter_of_the_operation() {
    let sort = "  sort Pos\n    entity pk\n  end\n";
    let op = "  operation Pos[T](x: T) -> T = x\n";
    for (order, decls) in both_orders(sort, op) {
        let user = "namespace test.tgaad.ptpuse\n  import test.tgaad.ptp.{T}\nend\n";
        let errs = load_errors_of_files(&[&program("ptp", &decls), user]);
        assert_refused_naming(&errs, &["unresolved import 'test.tgaad.ptp.T'"], order);
    }
}

/// The ticket's third program: the sort declares no type parameter, and is refused one as
/// it is without the operation — the CONTROL, whose refusal every order must match.
#[test]
fn the_sort_takes_no_type_parameter_of_the_operation() {
    let sort = "  sort Pos\n    entity pk\n  end\n";
    let op = "  operation Pos[T](x: T) -> T = x\n";
    let user = "  operation useSort(p: Pos[T = Int64]) -> Int64 = 1\n";
    let refusal = "`test.tgaad.ptq.Pos` has no type parameter named 'T'";
    assert_refused_naming(&load_errors_of(&program("ptq", &format!("{sort}{user}"))), &[refusal], "CONTROL, the sort alone");
    for (order, decls) in both_orders(sort, op) {
        assert_refused_naming(&load_errors_of(&program("ptq", &format!("{decls}{user}"))), &[refusal], order);
    }
}

/// A sort's entity `c` and the operation's parameter `c` are two symbols: the fact over the
/// entity is found, by its bare name and by its path, and the operation reads its parameter.
#[test]
fn a_sort_member_and_a_parameter_of_one_name_are_two_names() {
    let sort = "  sort Pos\n    entity c(v: Int64)\n  end\n";
    let op = "  operation Pos(c: Int64) -> Int64 = c + 1\n";
    let uses = "  fact holds(c(v: 7))\n  rule bare(?x) :- holds(c(v: ?x))\n  \
                rule path(?x) :- holds(test.tgaad.mem.Pos.c(v: ?x))\n  \
                operation go() -> Int64 = Pos(41)\n";
    for (order, decls) in both_orders(sort, op) {
        let src = program("mem", &format!("{decls}{uses}"));
        assert_eq!(answers(&src, "test.tgaad.mem.bare"), vec![7], "{order}: the entity, bare");
        assert_eq!(answers(&src, "test.tgaad.mem.path"), vec![7], "{order}: the entity, by its path");
        assert_eq!(run_int64(&src, "test.tgaad.mem.go"), Ok(42), "{order}: the parameter");
    }
}

/// The sort's type parameter `T` and the operation's `T` are each their declaration's: the
/// sort is applied at its own, the operation called at its own.
#[test]
fn the_sort_and_the_operation_each_have_their_own_type_parameter() {
    let sort = "  sort Pair\n    sort T = ?\n    entity mk(v: T)\n  end\n";
    let op = "  operation Pair[T](x: T) -> T = x\n";
    let uses = "  operation useSort(p: Pair[T = Int64]) -> Int64 = 1\n  \
                operation goSort() -> Int64 = useSort(mk(v: 3))\n  \
                operation goOp() -> Int64 = Pair(5)\n  \
                operation goBracket(p: Int64) -> Int64 = Pair[T = Int64](p)\n";
    for (order, decls) in both_orders(sort, op) {
        let src = program("tps", &format!("{decls}{uses}"));
        assert_eq!(run_int64(&src, "test.tgaad.tps.goSort"), Ok(1), "{order}: the sort's `T`");
        assert_eq!(run_int64(&src, "test.tgaad.tps.goOp"), Ok(5), "{order}: the operation's `T`");
        match interp_for(&src).call("test.tgaad.tps.goBracket", &[Value::Int(6)]) {
            Ok(Value::Int(n)) => assert_eq!(n, 6, "{order}: the operation's `T` written in the call's bracket"),
            other => panic!("{order}: the bracketed call did not run to an Int64: {other:?}"),
        }
    }
    // The sort's `T` higher-kinded, the operation's plain.
    let hk = "  sort Pair\n    sort [T] { sort [A] }\n    entity mk\n  end\n";
    for (order, decls) in both_orders(hk, op) {
        let src = program("tpk", &format!("{decls}  operation goOp() -> Int64 = Pair(5)\n"));
        assert_eq!(run_int64(&src, "test.tgaad.tpk.goOp"), Ok(5), "{order}, a higher-kinded `T`: the operation's");
    }
}

/// The operation's `result` beside a relation of the sort named `result`: each is its own.
/// The operation's `ensures` speaks of its own `result` at a call — `let y = Pos(7)` gives
/// `neq(y, 0)`, which discharges `div(100, y)`'s guard.
#[test]
fn the_operations_result_beside_a_sorts_relation_named_result() {
    let sort = "  sort Pos\n    entity pk(v: Int64)\n    fact result(1)\n  end\n";
    let op = "  operation Pos(c: Int64) -> Int64 ensures neq(result, 0) = c + 1\n";
    let uses = "  import anthill.prelude.Divisible.{div}\n  import anthill.prelude.PartialEq.{neq}\n  \
                operation go() -> Int64 =\n    let y = Pos(1)\n    let q = div(100, y)\n    q\n";
    for (order, decls) in both_orders(sort, op) {
        let src = program("res", &format!("{decls}{uses}"));
        assert_eq!(answers(&src, "test.tgaad.res.Pos.result"), vec![1], "{order}: the sort's relation");
        assert_eq!(run_int64(&src, "test.tgaad.res.go"), Ok(50), "{order}: the operation's `result`");
    }
}

/// A nested sort `c` of the sort beside the operation's parameter `c`: the nested sort's
/// entity is reached by its path, and the operation reads its parameter.
#[test]
fn a_nested_sort_beside_a_parameter_of_its_name() {
    let sort = "  sort Pos\n    sort c\n      entity e(v: Int64)\n    end\n  end\n";
    let op = "  operation Pos(c: Int64) -> Int64 = c + 1\n";
    let uses = "  fact holds(Pos.c.e(v: 4))\n  rule nested(?x) :- holds(Pos.c.e(v: ?x))\n  \
                operation go() -> Int64 = Pos(1)\n";
    for (order, decls) in both_orders(sort, op) {
        let src = program("nest", &format!("{decls}{uses}"));
        assert_eq!(answers(&src, "test.tgaad.nest.nested"), vec![4], "{order}: the nested sort");
        assert_eq!(run_int64(&src, "test.tgaad.nest.go"), Ok(2), "{order}: the parameter");
    }
}

/// A parameter's field path in the effects clause is checked against the PARAMETER's type
/// beside the sort's entity of the parameter's name: `Modify[b.nosuch]` over `b: Box` is
/// refused as it is for an operation of another name — the CONTROL.
#[test]
fn a_parameters_field_path_is_checked_beside_a_sort_member_of_its_name() {
    let boxed = "  sort Box\n    sort T = ?\n    entity box(contents: T)\n  end\n";
    let sort = "  sort Pos\n    entity b(v: Int64)\n  end\n";
    let refusal = "field projection 'b.nosuch': test.tgaad.fld.Box has no field 'nosuch'";
    for name in ["Pos", "other"] {
        let op = format!("  operation {name}(b: Box) -> Int64\n    effects Modify[b.nosuch]\n    = 0\n");
        for (order, decls) in both_orders(sort, &op) {
            let errs = load_errors_of(&program("fld", &format!("{boxed}{decls}")));
            assert_refused_naming(&errs, &[refusal], &format!("`{name}`, {order}"));
        }
    }
}

/// The flow facts over the places of the operation `op`, each named by its path from the
/// operation (`f.result`). A flow fact holds places only, so the path names the place even
/// where a sort member spells it too.
fn flow_facts(kb: &anthill_core::kb::KnowledgeBase, op: &str) -> Vec<(String, String, String)> {
    use anthill_core::kb::term::Term;
    let prefix = format!("{op}.");
    let name_of = |t| match kb.get_term(t) {
        Term::Ref(s) | Term::Fn { functor: s, .. } => {
            kb.qualified_name_of(*s).strip_prefix(prefix.as_str()).map(str::to_owned)
        }
        _ => None,
    };
    let flow = kb.try_resolve_symbol("anthill.reflect.feed.Flow.flow").expect("`flow`");
    let mut facts = Vec::new();
    for rid in kb.rules_by_functor(flow) {
        let Term::Fn { named_args, .. } = kb.get_term(kb.rule_head(rid)) else {
            continue;
        };
        let field = |key: &str| named_args.iter().find(|(k, _)| kb.local_name_of(*k) == key).map(|(_, v)| *v);
        let (Some(from), Some(to), Some(kind)) = (field("from"), field("to"), field("kind")) else {
            continue;
        };
        let kind = match kb.get_term(kind) {
            Term::Ref(s) | Term::Fn { functor: s, .. } => kb.local_name_of(*s).to_owned(),
            _ => continue,
        };
        if let (Some(from), Some(to)) = (name_of(from), name_of(to)) {
            facts.push((from, kind, to));
        }
    }
    facts.sort();
    facts
}

/// The flow a callback's places carry beside the sort's nested sort `f` and its relation
/// `result`, whose paths spell the callback `f` and its `f.result`: the argument feeds the
/// callback's parameter, and the callback's result the operation's.
#[test]
fn a_callbacks_flow_beside_sort_members_spelling_its_places() {
    let sort = "  sort Pos\n    sort f\n      fact result(1)\n    end\n  end\n";
    let op = "  operation Pos(z: Int64, f: (a: Int64) -> Int64) -> Int64 = f(z)\n";
    let expected: Vec<(String, String, String)> = [("f.result", "direct", "result"), ("z", "direct", "f.a")]
        .iter()
        .map(|(a, k, b)| (a.to_string(), k.to_string(), b.to_string()))
        .collect();
    for (order, decls) in both_orders(sort, op) {
        let src = program("flow", &decls);
        assert_eq!(answers(&src, "test.tgaad.flow.Pos.f.result"), vec![1], "{order}: the relation");
        let facts = flow_facts(&load_kb_with(&src), "test.tgaad.flow.Pos");
        assert_eq!(facts, expected, "{order}: the callback's flow");
    }
}

/// The operation's own type parameter, required beside a sort of the operation's name: the
/// requirement dispatches through the provision at the call's type.
#[test]
fn the_operations_requirement_on_its_type_parameter_beside_the_sort() {
    let spec = "  sort Tag\n    sort T = ?\n    operation tag(x: T) -> Int64\n  end\n  \
                sort Amount\n    entity amount(v: Int64)\n  end\n  \
                operation amountTag(a: Amount) -> Int64 =\n    match a\n      case amount(v) -> v\n  \
                namespace Amount\n    provides Tag[T = Amount, tag = amountTag]\n  end\n";
    let sort = "  sort Measure\n    entity m(v: Int64)\n  end\n";
    let op = "  operation Measure[A](a: A) -> Int64 requires Tag[T = A] = Tag.tag(a)\n";
    let uses = "  operation go() -> Int64 = Measure(amount(v: 9))\n";
    for (order, decls) in both_orders(sort, op) {
        let src = program("req", &format!("{spec}{decls}{uses}"));
        assert_eq!(run_int64(&src, "test.tgaad.req.go"), Ok(9), "{order}");
    }
}

/// The witnesses and the printer the forward row drives a set with (WN9P8's).
const ORDERS: &str = "  import anthill.prelude.{String, WeakOrd, List, SortedSet}\n  \
                      import anthill.prelude.String.{length}\n  \
                      import anthill.prelude.Numeric.{sub}\n  \
                      import anthill.prelude.List.{cons, nil}\n  \
                      sort ByLength\n    provides WeakOrd[T = String]\n    \
                      operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))\n  end\n  \
                      sort RevLen\n    provides WeakOrd[T = String]\n    \
                      operation compare(a: String, b: String) -> Int64 = sub(length(b), length(a))\n  end\n  \
                      sort Show\n    operation join(l: List[T = String]) -> String =\n      \
                      match l\n        case nil() -> \"\"\n        \
                      case cons(h, t) -> String.concat(h, String.concat(\",\", join(t)))\n  end\n";

/// A named requirement slot of the operation's own, forwarded by a caller that holds its
/// dictionary: the slot's binder is the operation's type parameter, beside a sort of the
/// operation's name. Each set is inserted into in the order it was built with.
#[test]
fn an_operations_named_slot_forwards_beside_the_sort() {
    let sort = "  sort Grow\n    entity g\n  end\n";
    let op = "  operation Grow[E, OE](s: SortedSet[T = E, O = OE], x: E) -> SortedSet[T = E, O = OE]\n      \
              requires OE: WeakOrd[E] =\n    SortedSet.insert(s, x)\n";
    let uses = "  operation add[E, OE](s: SortedSet[T = E, O = OE], x: E) -> SortedSet[T = E, O = OE]\n      \
                requires OE: WeakOrd[E] =\n    Grow(s, x)\n";
    let three = |order: &str| {
        format!(
            "Show.join(SortedSet.toList(add(add(add(SortedSet.empty[T = String, O = {order}](), \
             \"a\"), \"bbb\"), \"cc\")))"
        )
    };
    let drivers = format!(
        "  operation byLength() -> String = {}\n  operation revLen() -> String = {}\n",
        three("ByLength"),
        three("RevLen"),
    );
    // The sort naming a slot of the same name for a requirement of its own.
    let slotted = "  sort Grow\n    sort E = ?\n    requires OE: WeakOrd[E]\n    entity g\n  end\n";
    for (sort, what) in [(sort, "a sort with no slot"), (slotted, "a sort naming `OE` too")] {
        for (order, decls) in both_orders(sort, op) {
            let src = program("fwd", &format!("{ORDERS}{decls}{uses}{drivers}"));
            let mut interp = interp_for(&src);
            for (entry, expected) in [("byLength", "a,cc,bbb,"), ("revLen", "bbb,cc,a,")] {
                match interp.call(&format!("test.tgaad.fwd.{entry}"), &[]) {
                    Ok(Value::Str(s)) => assert_eq!(s.as_str(), expected, "{what}, {order}: `{entry}`"),
                    other => panic!("{what}, {order}: `{entry}` did not answer a string: {other:?}"),
                }
            }
        }
    }
}

/// A callback parameter `f` beside the sort's entity `f`: the operation applies its
/// callback, and the fact over the entity is found.
#[test]
fn a_callback_parameter_beside_a_sort_member_of_its_name() {
    let sort = "  sort Pos\n    entity f(v: Int64)\n  end\n";
    let op = "  operation Pos(f: (Int64) -> Int64, a: Int64) -> Int64 = f(a)\n";
    let uses = "  fact holds(f(v: 2))\n  rule bare(?x) :- holds(f(v: ?x))\n  \
                operation go() -> Int64 = Pos(lambda (n) -> n + 1, 4)\n";
    for (order, decls) in both_orders(sort, op) {
        let src = program("cbk", &format!("{decls}{uses}"));
        assert_eq!(answers(&src, "test.tgaad.cbk.bare"), vec![2], "{order}: the entity");
        assert_eq!(run_int64(&src, "test.tgaad.cbk.go"), Ok(5), "{order}: the callback");
    }
}

/// A wildcard import of an operation's type parameter names nothing an import reaches, as
/// the plain import of it does not (WI-20261023-GJVVW) — not a declaration without contents.
#[test]
fn a_wildcard_import_of_an_operations_type_parameter_is_unresolved() {
    let lib = program("wild", "  operation idt[T](x: T) -> T = x\n");
    let user = "namespace test.tgaad.wilduse\n  import test.tgaad.wild.idt.T.*\nend\n";
    let errs = load_errors_of_files(&[&lib, user]);
    assert_refused_naming(&errs, &["unresolved import 'test.tgaad.wild.idt.T'"], "the wildcard");
    assert!(
        !errs.iter().any(|e| e.contains("has no contents")),
        "the type parameter is no declaration an import names: {errs:#?}"
    );
}

/// The sort's induction schema `Pos.induction` beside a parameter named `induction`: the
/// schema is the sort's relation, reached by its path from the namespace, and the operation
/// reads its parameter.
#[test]
fn the_sorts_induction_schema_beside_a_parameter_named_induction() {
    let sort = "  sort Pos\n    entity pk\n    entity pq\n  end\n";
    let op = "  operation Pos(induction: Int64) -> Int64 = induction\n";
    let uses = "  rule useInd(?p) :- Pos.induction(?p)\n  operation go() -> Int64 = Pos(3)\n";
    for (order, decls) in both_orders(sort, op) {
        let src = program("ind", &format!("{decls}{uses}"));
        let kb = load_kb_with(&src);
        let schema = kb
            .try_resolve_symbol("test.tgaad.ind.Pos.induction")
            .unwrap_or_else(|| panic!("{order}: no `Pos.induction`"));
        assert_eq!(kb.rules_by_functor(schema).len(), 1, "{order}: the schema's one clause");
        assert_eq!(run_int64(&src, "test.tgaad.ind.go"), Ok(3), "{order}: the parameter");
    }
}

/// The operation's body reads the sort's members as a declaration beside the sort does: by
/// the sort's name (kernel-language.md §4.4; user, 2026-10-25). A bare member of the sort is
/// refused there, as from any operation of the namespace — the CONTROL, an operation of
/// another name. It loaded before, when the two shared one scope.
#[test]
fn the_operations_body_reads_the_sorts_members_by_the_sorts_name() {
    let sort = "  sort Pos\n    entity pk(v: Int64)\n    operation helper() -> Int64 = 7\n  end\n";
    for (name, what) in [("Pos", "the operation of the sort's name"), ("other", "CONTROL, another name")] {
        let qualified = format!("  operation {name}(c: Int64) -> Int64 = Pos.helper() + c\n  \
                                 operation go() -> Int64 = {name}(1)\n");
        let bare = format!("  operation {name}(c: Int64) -> Int64 = helper() + c\n");
        for (order, decls) in both_orders(sort, &qualified) {
            assert_eq!(run_int64(&program("body", &decls), "test.tgaad.body.go"), Ok(8), "{what}, {order}");
        }
        for (order, decls) in both_orders(sort, &bare) {
            assert_refused_naming(
                &load_errors_of(&program("body", &decls)),
                &["`helper` is a member of sort Pos, not in scope as a bare name here"],
                &format!("{what}, {order}"),
            );
        }
    }
}
