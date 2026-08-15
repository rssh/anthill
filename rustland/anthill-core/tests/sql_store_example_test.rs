//! WI-934 — the SQL store sketch lives in `examples/sql-store/`, not the stdlib,
//! and it still loads and destructures there.
//!
//! WHY IT MOVED. `anthill.persistence.sql` declared `SqlStore` / `SqlDialect` /
//! `QueryBinding` / `ColumnDef` and no host implements a SQL backend, so
//! `retract` / `update` / `retrieve` against a `SqlStore` value reach no registered
//! mirror. WI-931 removed the file's two provision facts for exactly that reason;
//! what remained was a shape with no realization. The rule that follows from — and
//! the reason the `Store` / `NonMonotonicStore` / `QueryableStore`
//! algebra STAYS in the stdlib — is stated once, in
//! `docs/proposals/038-builtin-sorts.md`, "What the stdlib carries".
//!
//! WHAT THIS SUITE PINS, in two halves that need each other:
//!
//!   * `the_sql_store_shape_left_the_stdlib` — a bare stdlib load no longer defines
//!     the sort. On its own that is a weak claim: `try_resolve_symbol` answers
//!     `None` for any name that was never interned, so a typo would "pass" it. It is
//!     paired IN THE SAME TEST with a name that must still resolve — the store
//!     algebra that stayed — so the negative is a measurement and not a spelling.
//!     Its complement over the file tree is `stdlib_drift_test` (anthill-stl).
//!
//!   * the four `the_demo_*` tests — the example is RESOLVED, not merely loaded. A
//!     file nothing loads rots; a file something loads but never queries rots into a
//!     declaration that no longer means anything, and `the_shape_loads_from_examples`
//!     on its own would keep passing through exactly that. So each field kind the
//!     shape declares is driven to an ANSWER: a `String`, a `SqlDialect` variant, a
//!     `Quoted` SQL fragment, and the `List[T = ColumnDef]`.
//!     `sql_store_provides_nothing` and `reinstating_the_sql_store_provision_is_refused`
//!     (WI-931's suite) carry the other half: that the moved file still declares no
//!     provision, and still cannot be given one.
//!
//!   * `both_load_orders_of_the_example_answer_the_same` (WI-936) — the two files load
//!     in EITHER order and answer the same. WI-934 had to pin the dependency order
//!     here, because the losing order cost the `columns` destructuring silently; the
//!     loader now settles every entity's field types before converting any file's
//!     terms, so [`load_example`] walks the directory (a file added later cannot be
//!     silently skipped) and that walk is itself the order that used to lose.
//!
//! CONTROL, MEASURED by backing the move out rather than asserted. Copying
//! `sql.anthill` back to `stdlib/anthill/persistence/` fails
//! `the_sql_store_shape_left_the_stdlib` and the two `stdlib_drift_test` tests
//! (anthill-stl), and nothing else — the six other tests here pass either way BY
//! DESIGN, since they read the example at its own path and say nothing about the
//! stdlib. That first run is also what caught the test being weaker than it read:
//! with only `anthill.persistence.sql.SqlStore` asserted absent it PASSED with the
//! file restored, because the move renamed the namespace too. Both spellings are
//! named now, and the backout fails as it should.
//!
//! This is a top-level test binary rather than a `tests/include/` module because it
//! drives an EXAMPLE — the shape `classic_mini_test` and `github_todo_test` already
//! set.

mod common;

use anthill_core::eval::Value;
use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;

use common::{
    collect_anthill_files, example_source, examples_dir, query_unary, try_load_kb_with,
    try_load_kb_with_files,
};

/// The stdlib + host bindings + every `.anthill` under `examples/sql-store/`, in
/// DIRECTORY WALK order — so a file added to the example later is loaded rather than
/// silently skipped.
///
/// THE WALK ORDER IS THE ORDER THAT USED TO LOSE, and that is why it stays. It is
/// alphabetical, so `demo.anthill` (the facts) precedes `sql.anthill` (the schema
/// they are written against), and until WI-936 that order LOADED CLEAN while silently
/// costing the `columns` destructuring: `QueryBinding.columns`'s declared
/// `List[T = ColumnDef]` is what desugars the demo's list literal to a `cons` spine,
/// and with the demo converted first `account_column_type` answered NOTHING instead
/// of `"text"`. Measured both ways then — `sql, demo` → 1 solution, `demo, sql` → 0,
/// no diagnostic either way. WI-934 pinned the dependency order here as a local
/// workaround; WI-936 fixed the loader (entity field types are registered for every
/// file before any file's terms are converted), so the pin is gone and this suite
/// drives the fix on real files.
/// [`both_load_orders_of_the_example_answer_the_same`] holds the explicit both-ways
/// measurement.
fn load_example() -> KnowledgeBase {
    let dir = examples_dir().join("sql-store");
    let sources: Vec<String> = collect_anthill_files(&dir)
        .iter()
        .map(|p| std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display())))
        .collect();
    assert!(
        !sources.is_empty(),
        "examples/sql-store/ must hold at least one .anthill file"
    );
    let refs: Vec<&str> = sources.iter().map(String::as_str).collect();

    try_load_kb_with_files(&refs).unwrap_or_else(|errs| {
        for e in &errs {
            eprintln!("load error: {e}");
        }
        panic!(
            "examples/sql-store must LOAD against the stdlib; got {} error(s)",
            errs.len()
        );
    })
}

/// SUBJECT — the sort is gone from the standard library, and its algebra is not.
///
/// The positive assertion is what makes the negative ones mean something:
/// `anthill.persistence.QueryableStore` is the spec a SQL backend would be written
/// against and it STAYED, so a KB in which the store algebra resolves but no
/// `SqlStore` does is measuring the move rather than a mistyped path or an empty KB.
///
/// BOTH SPELLINGS are refused, and that is not belt-and-braces — it is what the
/// control measured. With only the old name asserted, restoring the file to
/// `stdlib/anthill/persistence/` PASSED this test: the move also renamed the
/// namespace, so the old name stays absent however the file is filed. Naming the
/// new spelling too makes this a claim about where the file LIVES.
#[test]
fn the_sql_store_shape_left_the_stdlib() {
    let kb = try_load_kb_with("namespace wi934.probe\nend\n").expect("stdlib loads");

    assert!(
        kb.try_resolve_symbol("anthill.persistence.QueryableStore")
            .is_some(),
        "the abstract store algebra STAYS in the stdlib — only the SQL sketch moved",
    );
    for qn in [
        "anthill.persistence.sql.SqlStore",
        "anthill.persistence.sql.QueryBinding",
        "anthill.examples.persistence.sql.SqlStore",
        "anthill.examples.persistence.sql.QueryBinding",
    ] {
        assert!(
            kb.try_resolve_symbol(qn).is_none(),
            "`{qn}`: the SQL sketch must not ship in the standard library under ANY \
             name — it lives in examples/sql-store/ (WI-934)",
        );
    }
}

/// SUBJECT — and it resolves at its new home, in an example-flavoured namespace.
#[test]
fn the_shape_loads_from_examples() {
    let kb = load_example();
    for n in ["SqlStore", "SqlDialect", "QueryBinding", "ColumnDef"] {
        let qn = format!("anthill.examples.persistence.sql.{n}");
        assert!(
            kb.try_resolve_symbol(&qn).is_some(),
            "`{qn}` must resolve from examples/sql-store/sql.anthill",
        );
    }
}

/// SUBJECT — a store VALUE is built, asserted as a fact, and destructured by field.
///
/// This is the capability the shape actually supplies today: not persistence (no
/// host realizes it) but the declarations being real sorts. Driving it is what
/// separates "the example still parses" from "the example still means something" —
/// a `SqlStore` whose `connection` field was renamed would load clean and fail here.
#[test]
fn the_demo_store_destructures_by_field() {
    let mut kb = load_example();

    let sols = query_unary(
        &mut kb,
        "anthill.examples.persistence.sql.demo.audit_connection",
    );
    assert_eq!(
        sols.len(),
        1,
        "one `audit_db` fact, so exactly one connection string"
    );
    assert!(
        sols[0].1,
        "the answer must be DEFINITE — an undecided row would read as one"
    );
    assert_eq!(
        text_of(&kb, &sols[0].0),
        "postgresql://localhost/anthill",
        "the `connection` field reaches the rule head",
    );
}

/// SUBJECT — the dialect enum. `SqlDialect` is the shape's one non-scalar field, and
/// the whole point of the design it sketches (PostgreSQL / MySQL / SQLite / DuckDB
/// are DIALECTS of one store type, not four store types), so a variant reaching the
/// head unchanged is worth its own assertion.
#[test]
fn the_demo_store_carries_its_dialect_variant() {
    let mut kb = load_example();

    let sols = query_unary(
        &mut kb,
        "anthill.examples.persistence.sql.demo.audit_dialect",
    );
    assert_eq!(sols.len(), 1, "one `audit_db` fact, so exactly one dialect");
    let Value::Term { id } = sols[0].0 else {
        panic!(
            "a dialect must reach the head as a term, got {:?}",
            sols[0].0
        )
    };
    // A nullary enum variant rides as a `Ref`, not a zero-arg application; refusing
    // `Term::Fn` here is deliberate, so a regression that re-wrapped it as a zero-arg
    // call would be reported rather than accepted.
    let Term::Ref(s) = kb.get_term(id) else {
        panic!(
            "a dialect variant must be a name, got {:?}",
            kb.get_term(id)
        )
    };
    assert_eq!(
        kb.qualified_name_of(*s),
        "anthill.examples.persistence.sql.SqlDialect.Postgresql",
        "the `Postgresql` variant reaches the rule head as itself, from the example's \
         own namespace — the QUALIFIED name, since a short-name compare would accept a \
         `Postgresql` from anywhere",
    );
}

/// SUBJECT — the `QueryBinding`: a `String` field and a `Quoted` SQL fragment.
///
/// `Quoted(language, source)` (kernel spec §4.2) is what makes this binding writable
/// with no SQL backend anywhere — the SQL is formal, just in another language, and
/// opaque to the kernel. It reaches the rule head as an ordinary two-argument
/// application, which is the whole claim: the fragment is carried, not interpreted.
#[test]
fn the_demo_binding_carries_its_quoted_sql() {
    let mut kb = load_example();

    let sols = query_unary(&mut kb, "anthill.examples.persistence.sql.demo.audit_table");
    assert_eq!(
        sols.len(),
        1,
        "one `audit_binding` fact, so exactly one table"
    );
    assert_eq!(
        text_of(&kb, &sols[0].0),
        "audit_entries",
        "the `table` field reaches the head"
    );

    let sols = query_unary(
        &mut kb,
        "anthill.examples.persistence.sql.demo.audit_retrieve_sql",
    );
    assert_eq!(sols.len(), 1, "…and exactly one retrieve fragment");
    let Value::Term { id } = sols[0].0 else {
        panic!("a Quoted fragment must ride as a term, got {:?}", sols[0].0)
    };
    let Term::Fn {
        functor, pos_args, ..
    } = kb.get_term(id)
    else {
        panic!(
            "Quoted must reach the head as an application, got {:?}",
            kb.get_term(id)
        )
    };
    let (functor, pos_args) = (*functor, pos_args.clone());
    assert_eq!(
        kb.local_name_of(functor),
        "Quoted",
        "the fragment stays a `Quoted` term — nothing evaluates or unwraps it",
    );
    assert_eq!(
        (
            text_of(&kb, &Value::Term { id: pos_args[0] }),
            text_of(&kb, &Value::Term { id: pos_args[1] }),
        ),
        (
            "sql".to_string(),
            "SELECT account, action, amount FROM audit_entries WHERE account = $1".to_string(),
        ),
        "both the language tag and the source survive verbatim",
    );
}

/// SUBJECT — and the `List[T = ColumnDef]` face, destructured IN THE LANGUAGE.
///
/// `QueryBinding.columns` is declared `List[T = ColumnDef]`, and that declared type is
/// doing work: the literal desugars to a `cons` spine, so the demo's rule can match
/// `cons(head: ColumnDef(…), tail: ?)`. MEASURED while writing this: the same literal
/// in an UNTYPED fact argument stays a flat n-ary node and that pattern matches
/// nothing — which is why the demo puts its columns inside the binding rather than in
/// a bare fact of their own.
///
/// The demo carries its own CONTROL, and it is what makes the positive answer mean
/// "the HEAD matched" rather than "something in the list matched": `action` is the
/// second column, and matching it at the spine's head answers nothing.
#[test]
fn the_demo_column_list_destructures_through_its_declared_type() {
    let mut kb = load_example();

    let sols = query_unary(
        &mut kb,
        "anthill.examples.persistence.sql.demo.account_column_type",
    );
    assert_eq!(sols.len(), 1, "the spine's head matches exactly once");
    assert_eq!(
        text_of(&kb, &sols[0].0),
        "text",
        "the first `ColumnDef` — matched by its own `name` and `field` — yields its \
         own `sql_type`",
    );

    let sols = query_unary(
        &mut kb,
        "anthill.examples.persistence.sql.demo.action_column_at_head",
    );
    assert!(
        sols.is_empty(),
        "`action` is the SECOND column; matching it at the spine's head must answer \
         nothing, else the pattern matches anywhere in the list: {sols:?}",
    );
}

/// SUBJECT (WI-936) — the example answers the SAME in either file order, driven both
/// ways in one test so the two cannot silently diverge again.
///
/// This is the ticket's acceptance on real files: `sql, demo` is the dependency order
/// and `demo, sql` is what an alphabetical walk produces. Until WI-936 they disagreed
/// — 1 solution vs 0 — with no parse error, no load error and no diagnostic either
/// way, because `QueryBinding.columns`'s declared `List[T = ColumnDef]` was registered
/// only when `sql.anthill` LOADED, not when it was scanned. The sibling rule reading
/// `columns` as a bare variable answered in both orders, which is what made the loss
/// quiet; it is asserted here too, so a regression that broke BOTH orders could not
/// pass this test by making the two agree on nothing.
#[test]
fn both_load_orders_of_the_example_answer_the_same() {
    let sql = example_source("sql-store/sql.anthill");
    let demo = example_source("sql-store/demo.anthill");

    let mut answers = Vec::new();
    for order in [[sql.as_str(), demo.as_str()], [demo.as_str(), sql.as_str()]] {
        let mut kb = try_load_kb_with_files(&order).unwrap_or_else(|errs| {
            for e in &errs {
                eprintln!("load error: {e}");
            }
            panic!("both orders must load; got {} error(s)", errs.len());
        });
        let spine = query_unary(
            &mut kb,
            "anthill.examples.persistence.sql.demo.account_column_type",
        )
        .iter()
        .map(|(v, _)| text_of(&kb, v))
        .collect::<Vec<_>>();
        // The quiet sibling: `columns` read as a WHOLE, which answered in both orders
        // even when the spine did not.
        let whole = query_unary(
            &mut kb,
            "anthill.examples.persistence.sql.demo.audit_column_defs",
        )
        .len();
        answers.push((spine, whole));
    }

    assert_eq!(
        answers[0], answers[1],
        "the two load orders disagree — `sql, demo` gave {:?} and `demo, sql` gave {:?}",
        answers[0], answers[1],
    );
    assert_eq!(
        answers[0].0,
        ["text"],
        "the spine's head is the `account` column, in either order"
    );
    assert_eq!(
        answers[0].1, 1,
        "…and `columns` read as a whole answers once, in either order"
    );
}

// ── local helper ────────────────────────────────────────────────────

/// A `String`-valued answer, in whichever carrier it arrives in — a rule head may
/// deliver an unboxed `Value::Str`, a `TermId` pointing at a string constant, or a
/// `Value::Node`, and which one is not this suite's subject. `TermView::head` reads
/// all three, so this is the one `matches!` and not a per-carrier ladder (the
/// `reifies_to_int` precedent in `wi616_semantic_eq_test`).
///
/// PANICS on a non-string head rather than rendering it: every caller asserts about a
/// declared `String` field, so anything else means the shape changed, and a
/// `{:?}`-compare would report that as a text mismatch instead of as the structural
/// change it is.
fn text_of(kb: &KnowledgeBase, v: &impl TermView) -> String {
    match v.head(kb) {
        ViewHead::Const(Literal::String(s)) => s,
        other => panic!("expected a String field value, got {other:?}"),
    }
}
