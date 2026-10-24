//! WI-20261024-QK77S, found with it — a sort's qualified name is the type value its one-segment
//! name is in a clause's data slot, a rule body's and a query's, as it is in an operation body
//! (WI-20260908-9WVT7 read a constructor's qualified name so, and left the other kinds): `?t <=>
//! D.T` binds `Int64` as `?t <=> MyInt` does, and `fact held(D.T)` holds `Int64`. A type member
//! reached through an alias that fixes parameters is read at them there too: `CA.T` over `sort
//! CA = P[T = String]` is `String`, `CQ.L` over `sort CQ = Q[A = Int64]` is `List[T = Int64]`.
//! Before, `?t <=> D.T` bound the alias's own name `T`, `?t = D.T` and `holds(D.T)` were load
//! errors ("a defect in the walk that built this occurrence", "T.name: expected resolved
//! name"), and `?t <=> CA.T` bound the chain `field_access(CA, T)`.
//!
//! CONTROLS — measured, each piece backed out on its own in one build, over this module and
//! the ones whose rows moved with it:
//!   a dotted sort left the chain in the clause's and the rule body's walk — FAIL:
//!     a_dotted_sort_in_a_rule_body_is_its_type_value
//!     a_fact_holding_a_dotted_sort_holds_the_type
//!     `wi_rxt6s_…::a_data_slot_still_stores_the_chain`,
//!     `wi_r1w5a_…::a_type_in_a_calls_argument_is_its_type_value`,
//!     `wi_4nekz_…::the_five_other_name_kinds_still_agree_with_the_operation_body`
//!   the member through an alias not read at its parameters (`dotted_type_named`'s alias
//!   rung off), and separately the definition never read at them (`member_at`) — FAIL, each:
//!     an_alias_member_in_a_data_slot_is_read_at_the_alias
//!     an_open_member_through_an_alias_is_refused_in_a_clause

use anthill_core::kb::resolve::ResolveConfig;

use crate::common::{
    assert_refused_naming, load_errors_of, load_kb_with, print_type, query_pattern_term,
    query_unary, supply_invocation_imports,
};

const DECLS: &str = "\
  sort D
    sort T = Int64
    entity d(x: T)
  end
  sort P
    sort T = ?
    entity p(x: T)
  end
  sort Q
    sort A = ?
    sort L = List[T = A]
    entity q(x: A)
  end
  sort Q2
    sort A = ?
    sort B = ?
    sort PB = List[T = B]
    entity q2(x: A, y: B)
  end
  sort MyInt = Int64
  sort CA = P[T = String]
  sort CQ = Q[A = Int64]
  sort C2 = Q2[A = Int64]
";

fn program(ns: &str, clauses: &str) -> String {
    format!(
        "namespace qk77ds.{ns}\n  import anthill.prelude.{{Int64, String, List, Type}}\n{DECLS}{clauses}end\n"
    )
}

/// The answers of `qk77ds.<ns>.<rel>(?x)`, printed.
fn answers(ns: &str, clauses: &str, rel: &str) -> Vec<String> {
    let mut kb = load_kb_with(&program(ns, clauses));
    query_unary(&mut kb, &format!("qk77ds.{ns}.{rel}"))
        .into_iter()
        .map(|(v, definite)| {
            assert!(definite, "{ns}.{rel}: an undecided answer {v:?}");
            print_type(&kb, &v)
        })
        .collect()
}

/// How many facts the query `pattern` finds, read as `anthill query -i` reads it.
fn query_count(ns: &str, clauses: &str, pattern: &str) -> usize {
    let mut kb = load_kb_with(&program(ns, clauses));
    supply_invocation_imports(&mut kb, &[&format!("qk77ds.{ns}.*"), "anthill.prelude.*"]);
    let goal = query_pattern_term(&mut kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// `?t <=> D.T` binds what `?t <=> MyInt` binds, `Int64`; `?t = D.T` loads as `?t = MyInt`
/// does.
#[test]
fn a_dotted_sort_in_a_rule_body_is_its_type_value() {
    let by_alias = answers("rb1", "  rule r(?t) :- ?t <=> MyInt\n", "r");
    let by_path = answers("rb2", "  rule r(?t) :- ?t <=> D.T\n", "r");
    assert_eq!(by_alias.len(), 1, "{by_alias:?}");
    assert_eq!(by_path, by_alias);
    assert_eq!(by_path, vec!["Int64"]);
    assert_eq!(
        load_errors_of(&program("rb3", "  rule r(?t) :- ?t = D.T\n")),
        Vec::<String>::new()
    );
}

/// `fact held(D.T)` holds `Int64`: a goal writing `Int64` and a query writing either find it.
#[test]
fn a_fact_holding_a_dotted_sort_holds_the_type() {
    let clauses = "  fact held(D.T)\n  rule r(?t) :- held(Int64), held(?t)\n";
    assert_eq!(answers("fa1", clauses, "r"), vec!["Int64"]);
    for pattern in ["held(Int64)", "held(D.T)"] {
        assert_eq!(query_count("fa2", clauses, pattern), 1, "{pattern}");
    }
}

/// Through an alias that fixes parameters, a member is read at them: `?t <=> CA.T` binds
/// `String`, `fact held(CA.T)` holds `String` (found by a query writing `String` and one
/// writing `CA.T`), and `?t <=> CQ.L` binds `List[T = Int64]` — each what the type written out
/// binds.
#[test]
fn an_alias_member_in_a_data_slot_is_read_at_the_alias() {
    for (ns, through, written) in [
        ("am1", "CA.T", "String"),
        ("am2", "CQ.L", "List[T = Int64]"),
    ] {
        let read = answers(ns, &format!("  rule r(?t) :- ?t <=> {through}\n"), "r");
        let direct = answers(ns, &format!("  rule r(?t) :- ?t <=> {written}\n"), "r");
        assert_eq!(read.len(), 1, "{through}: {read:?}");
        assert_eq!(read, direct, "{through}");
    }
    let clauses = "  fact held(CA.T)\n";
    for pattern in ["held(String)", "held(CA.T)"] {
        assert_eq!(query_count("am3", clauses, pattern), 1, "{pattern}");
    }
}

/// A member whose definition names a parameter the alias leaves open is no type: refused in a
/// fact and in a rule body, in the words the dot on the alias is refused with in an operation
/// body.
#[test]
fn an_open_member_through_an_alias_is_refused_in_a_clause() {
    for (ns, clause) in [
        ("op1", "  fact held(C2.PB)\n"),
        ("op2", "  rule r(?t) :- ?t <=> C2.PB\n"),
    ] {
        let errs = load_errors_of(&program(ns, clause));
        assert_eq!(errs.len(), 1, "{ns}: {errs:#?}");
        assert_refused_naming(
            &errs,
            &[
                "`C2.PB` names no type here",
                "`PB` is defined over a parameter of `Q2` the receiver leaves open",
            ],
            ns,
        );
    }
}
