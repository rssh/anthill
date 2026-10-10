//! WI-20261004-2HJW8 — a type alias whose definition reaches its own name is refused where
//! it is declared.
//!
//! THE RULE. An alias is the type it is defined as, so an alias that names itself —
//! directly (`sort S = S`), through a chain of aliases (`sort A = B`, `sort B = A`), or
//! inside an applied link (`sort Loop = List[T = Loop]`) — would be an infinite type. It
//! is a load error at the declaration, naming the chain. A recursive type is written
//! through a sort with a constructor, which gives the recursion a value to stand on.
//!
//! BEFORE. Every such declaration loaded, with no message. Used as a type the alias was
//! a name nothing conforms to (`f(x: A)` refused every argument), and since an alias
//! written bare is read as its type (WI-20261009-ZY11J) a type naming `Loop` twice read
//! it at two depths: `h(x: List[T = Loop]) = g(x)` over `g(x: Loop)` was refused,
//! "expected List[T = Loop], got List[T = List[T = Loop]]".
//!
//! CONTROLS — measured, each piece backed out on its own:
//!
//!   the refusal (`AliasDeclarePass::refuse_alias_reaching_itself` finding no chain) —
//!   FAIL:
//!     an_alias_that_names_itself_is_refused_where_it_is_declared
//!     a_chain_of_aliases_that_comes_back_is_refused_at_each_link
//!     an_alias_that_names_a_chain_without_being_on_it_is_not_refused
//!   an alias not waiting for itself (`pending_aliases_named` leaving the alias being
//!   declared out, as it did) — FAIL:
//!     an_alias_that_names_itself_is_refused_where_it_is_declared — the alias is then
//!       ready in the first round and never reaches the one that refuses.
//!
//!   PASS EITHER WAY, by design:
//!     an_alias_that_reaches_no_name_of_its_own_loads — the fence: what must keep loading.
//!
//!   `wi_f8pyz_spec_clause_alias_test`: a spec clause naming a cyclic alias keeps its own
//!   refusal ("its chain comes back to itself"), beside the declarations'. Its two
//!   reports-once rows count three refusals over a cyclic alias — the clause's one and
//!   the two declarations' — and FAIL with the refusal backed out, counting one.

use anthill_core::eval::Value;

use crate::common::{interp_for, load_errors_of};

fn source(ns: &str, body: &str) -> String {
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{Int64, String, List, Option}}\n{body}\nend\n"
    )
}

/// The load errors of a source, which must have some.
fn refusals(ns: &str, body: &str) -> Vec<String> {
    let errs = load_errors_of(&source(ns, body));
    assert!(!errs.is_empty(), "{ns}: must be refused, and loaded clean");
    errs
}

/// Load, call `test.<ns>.go()`, and hand back the integer it answers.
fn run(ns: &str, body: &str) -> i64 {
    let mut interp = interp_for(&source(ns, body));
    match interp.call(&format!("test.{ns}.go"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{ns}: expected an Int64, got {other:?}"),
    }
}

/// The refusal of the alias `alias` — one, at `line:col`, naming `chain`.
fn assert_refused_at(errs: &[String], ns: &str, alias: &str, at: &str, chain: &str) {
    let named = format!("type alias `test.{ns}.{alias}` reaches its own name");
    let hits: Vec<&String> = errs.iter().filter(|e| e.contains(&named)).collect();
    assert_eq!(hits.len(), 1, "{ns}: one refusal of `{alias}`: {errs:#?}");
    assert!(hits[0].starts_with(&format!("{at}: ")), "{ns}: at the declaration: {}", hits[0]);
    assert!(hits[0].contains(&format!("({chain})")), "{ns}: naming the chain: {}", hits[0]);
}

// ── refused ─────────────────────────────────────────────────────────────────

/// The alias that is its own definition, and the one that names itself inside an
/// applied link. Neither names another alias, so neither waited for one.
#[test]
fn an_alias_that_names_itself_is_refused_where_it_is_declared() {
    let errs = refusals("hjwself", "  sort S = S\n  operation go() -> Int64 = 1");
    assert_refused_at(&errs, "hjwself", "S", "3:3", "S -> S");
    assert_eq!(errs.len(), 1, "{errs:#?}");

    let errs = refusals("hjwinside", "  sort Loop = List[T = Loop]\n  operation go() -> Int64 = 1");
    assert_refused_at(&errs, "hjwinside", "Loop", "3:3", "Loop -> Loop");
    assert_eq!(errs.len(), 1, "{errs:#?}");

    // … nested in a sort, by the name it has there.
    let errs = refusals(
        "hjwnested",
        "  sort Host\n    sort HA = List[T = HA]\n    entity h\n  end\n  operation go() -> Int64 = 1",
    );
    assert_refused_at(&errs, "hjwnested", "Host.HA", "4:5", "HA -> HA");
}

/// A chain that comes back: each alias on it is refused at its own declaration, by the
/// chain as it starts there — through bare links, and through applied ones.
#[test]
fn a_chain_of_aliases_that_comes_back_is_refused_at_each_link() {
    for (ns, body) in [
        ("hjwbare", "  sort A = B\n  sort B = A\n  operation go() -> Int64 = 1"),
        (
            "hjwapplied",
            "  sort A = List[T = B]\n  sort B = Option[T = A]\n  operation go() -> Int64 = 1",
        ),
    ] {
        let errs = refusals(ns, body);
        assert_refused_at(&errs, ns, "A", "3:3", "A -> B -> A");
        assert_refused_at(&errs, ns, "B", "4:3", "B -> A -> B");
        assert_eq!(errs.len(), 2, "{ns}: {errs:#?}");
    }
}

/// An alias that only NAMES one on a chain is not on it: `D` names `A`, and nothing
/// leads from `A` back to `D`. The three on the chain are refused, `D` is not.
#[test]
fn an_alias_that_names_a_chain_without_being_on_it_is_not_refused() {
    let errs = refusals(
        "hjwbeside",
        "  sort A = B\n  sort B = C\n  sort C = List[T = A]\n  sort D = List[T = A]\n  \
         operation go() -> Int64 = 1",
    );
    assert_refused_at(&errs, "hjwbeside", "A", "3:3", "A -> B -> C -> A");
    assert_refused_at(&errs, "hjwbeside", "B", "4:3", "B -> C -> A -> B");
    assert_refused_at(&errs, "hjwbeside", "C", "5:3", "C -> A -> B -> C");
    assert!(
        !errs.iter().any(|e| e.contains("hjwbeside.D` reaches")),
        "`D` is on no chain: {errs:#?}"
    );
}

// ── not refused ─────────────────────────────────────────────────────────────

/// What reaches no name of its own loads and runs, as it did: a chain that ends, an
/// alias naming one declared below it, recursion through a constructor — the sort is
/// nominal, and `Kids` names it, not itself — a carrier providing a spec at itself, and an
/// alias that shares its short name with the sort it stands for.
#[test]
fn an_alias_that_reaches_no_name_of_its_own_loads() {
    for (ns, body, answer) in [
        (
            "hjwends",
            "  sort Top = Mid\n  sort Mid = List[T = Int64]\n  \
             operation f(x: Top) -> Int64 = x.length()\n  operation go() -> Int64 = f([1, 2])",
            2,
        ),
        (
            "hjwbelow",
            "  sort Y = Later\n  sort Later = Int64\n  operation f(x: Y) -> Int64 = x\n  \
             operation go() -> Int64 = f(5)",
            5,
        ),
        (
            "hjwnominal",
            "  sort Tree\n    entity node(kids: Kids)\n  end\n  sort Kids = List[T = Tree]\n  \
             operation count(t: Tree) -> Int64 = t.kids.length()\n  \
             operation go() -> Int64 = count(node(kids: [node(kids: [])]))",
            1,
        ),
        (
            "hjwfbound",
            "  sort Ord2[T]\n    operation cmp(a: T, b: T) -> Int64\n  end\n  \
             sort Car\n    entity car(n: Int64)\n    provides Ord2[T = Self]\n    \
             operation cmp(a: Car, b: Car) -> Int64 = a.n - b.n\n  end\n  \
             operation go() -> Int64 = Ord2.cmp(car(n: 5), car(n: 2))",
            3,
        ),
        (
            "hjwsamename",
            "  namespace inner\n    sort Box2\n      entity b2(n: Int64)\n    end\n  end\n  \
             sort Box2 = inner.Box2\n  operation f(x: Box2) -> Int64 = x.n\n  \
             operation go() -> Int64 = f(inner.Box2.b2(n: 4))",
            4,
        ),
    ] {
        assert_eq!(run(ns, body), answer, "{ns}");
    }
}
