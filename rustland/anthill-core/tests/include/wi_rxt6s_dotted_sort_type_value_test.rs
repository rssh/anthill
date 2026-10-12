//! WI-20261012-RXT6S — a sort named by a dotted path is the type value its bare name is
//! (proposal 055 §2; the dot on such a receiver is WI-20260824-PAPX0's and, in a rule
//! body, WI-20261008-A3FY2's — `docs/kernel-language.md` §5.4).
//!
//! THE RULE. A nominal type written in a value position denotes a `Type` value, and a
//! name with dots in it is a name:
//!
//!   which(Outer.Inner)            as  which(Inner)        under `import ….Outer.Inner`
//!   let t = lib.t.Far             as  let t = Far         under `import lib.t.Far`
//!   (..lib.t.Far).k()             as  (Far).k()
//!   rule r(?x) :- ?x <=> (Outer.Inner).deep()     as  ?x <=> (Inner).deep()
//!
//! Before, a dotted name with no `(…)` was left the `field_access` chain it parses as
//! (§6.7) and the typer read each segment as a bare name: `Inner.name: expected resolved
//! name, got unresolved`, one such error a segment for a namespace path. The loader's
//! chain ladder had a rung for a local root, a rule and a const, and none for a sort.
//!
//! WHAT A ROW ASSERTS. `which` compares the type value it is given with the imported bare
//! names, so a row says WHICH sort the path named and not only that it loaded; a receiver
//! row calls a member only that sort declares.
//!
//! EVERY ROW HAS ITS OWN SOURCE, as in `wi_a3fy2_rule_body_type_receiver_test`.
//!
//! CONTROLS — measured against this module, `wi_a3fy2_rule_body_type_receiver_test` and
//! `wi_4nekz_dotted_equation_operand_test`, each piece backed out on its own:
//!
//!   the ladder's rung (`Loader::try_qualified_sort_ref` answering `false` always) — FAIL:
//!     an_argument_names_the_sort_its_bare_name_names
//!     a_let_binds_the_sort
//!     a_result_is_the_sort
//!     a_parenthesized_receiver_in_an_operation_body_is_the_sort
//!     an_entity_an_eponymous_sort_and_an_alias_keep_their_bare_reading
//!     a_path_is_a_type_value_wherever_a_value_is_written
//!     a_path_in_a_slot_of_another_sort_is_an_ordinary_mismatch
//!     a_member_past_the_sort_is_read_off_the_sort
//!     an_eponymous_sort_by_a_path_is_refused_as_its_bare_name_is (its operation-body row)
//!     the_whole_name_is_read_before_a_consts_field
//!     a_path_from_the_root_is_reached_past_a_binder
//!     a_parenthesized_receiver_in_a_rule_body_is_the_sort — the rule body's receiver is
//!       built by the operation body's walk
//!   and, in their own modules, `a_dotted_sort_name_is_a_written_type_in_both_bodies` and
//!   `the_five_other_name_kinds_still_agree_with_the_operation_body`.
//!   the rung placed after the prefix pass — FAIL:
//!     the_whole_name_is_read_before_a_consts_field (its sort row)
//!   the rule body's receiver (`Loader::dotted_sort_name` answering `None` always) — FAIL:
//!     a_parenthesized_receiver_in_a_rule_body_is_the_sort
//!     an_entity_an_eponymous_sort_and_an_alias_keep_their_bare_reading (its rule-body row)
//!     an_eponymous_sort_by_a_path_is_refused_as_its_bare_name_is (its rule-body row)
//!   and `a_dotted_sort_name_is_a_written_type_in_both_bodies`.
//!   the reference handed back for a path that names no written type (that arm of
//!   `Loader::written_type_receiver_occurrence` answering "no written type") — FAIL:
//!     an_eponymous_sort_by_a_path_is_refused_as_its_bare_name_is (its rule-body row)
//!
//!   PASS UNDER EACH OF THOSE, by design — they are the fences:
//!     the_imported_bare_names_are_unchanged — no path is written.
//!     the_companion_calls_are_unchanged — a call's functor is one name, never a chain.
//!     a_dotted_rule_citation_is_still_the_relation, a_dotted_const_is_still_its_value —
//!       the two rungs above the sort's; a whole name resolves to one symbol.
//!     a_binder_named_like_the_root_is_still_the_receiver — the local pass comes first.
//!     a_data_slot_still_stores_the_chain — a clause's own term is not this walk's.
//!     a_rule_bodys_argument_is_still_the_term_it_was — the boundary, below.
//!   The rung placed FIRST, before the rule's and the const's, changes no row of the
//!   core crate: the three hand on one node.
//!
//! THE BOUNDARY. Only the receiver of a dot is read so in a rule body's own term. A path
//! written as an ARGUMENT there stays the chain the clause stores, so `?x <=>
//! which(Outer.Inner)` hands `which` that chain and not the type value the bare `Inner`
//! is. Reading every type written in a clause's term is proposal 055 umbrella B
//! (WI-20260823-53W12); the row pins today's answer and turns with it.

use anthill_core::eval::Value;

use crate::common::{load_errors_of, load_kb_with, query_unary};

/// `lib.<ns>` — a sort, a free-standing entity, an eponymous sort, an alias, a rule and a
/// const — and `test.<ns>`, which holds a nested sort, `which`, and `body`. `which`
/// answers a number for each sort it knows by its imported bare name, and 0 otherwise.
fn source(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace lib.{ns}
  sort Far
    operation k() -> Int64 = 9
  end
  entity Pt(x: Int64)
  sort Leaf
    entity Leaf(name: String)
  end
  sort Bx[V]
    operation one() -> Int64 = 1
  end
  sort FA = Bx[V = Int64]
  rule rel(1) :- true
  const K: Int64 = 5
end

namespace test.{ns}
  import anthill.prelude.{{Type, Bool, String}}
  import lib.{ns}.{{Far, Pt, Leaf, FA}}
  sort Outer
    sort Inner
      operation deep() -> Int64 = 21
      rule rws(2) :- true
      const IC: Int64 = 6
    end
  end
  import test.{ns}.Outer.Inner
  entity P(t: Int64)
  operation which(t: Type) -> Int64 =
    if t = Inner then 21 else if t = Far then 9 else if t = Pt then 5 else if t = Leaf then 6 else if t = FA then 7 else 0
{body}
end
"#
    )
}

/// Load, resolve `test.<ns>.r(?x)`, and hand back the integers `?x` is bound to. Every
/// answer must be definite.
fn ints(ns: &str, body: &str) -> Vec<i64> {
    let mut kb = load_kb_with(&source(ns, body));
    query_unary(&mut kb, &format!("test.{ns}.r"))
        .into_iter()
        .map(|(v, definite)| {
            assert!(definite, "{ns}: a conditional answer, {v:?}");
            match v {
                Value::Int(n) => n,
                other => panic!("{ns}: expected an Int64, got {other:?}"),
            }
        })
        .collect()
}

/// The refusals of a source that must not load, rendered.
fn refusal(ns: &str, body: &str) -> String {
    let errs = load_errors_of(&source(ns, body));
    assert!(!errs.is_empty(), "{ns}: must be refused, and loaded clean");
    format!("{errs:?}")
}

/// The message a path drew before: a segment read as a bare name nothing declares.
const UNRESOLVED: &str = "expected resolved name";

/// One path a row is written for: the namespace the row is loaded in, the path as written
/// in `test.<ns>`, the member only its sort declares, and what `which` and that member
/// answer for it.
struct Path {
    ns: String,
    written: String,
    member: &'static str,
    answer: i64,
}

/// The three paths of the ticket, each in a namespace of its own under `row`: a nested
/// sort, a sort of another namespace, and that sort by its absolute name.
fn paths(row: &str) -> [Path; 3] {
    let at = |tag: &str, written: &dyn Fn(&str) -> String, member, answer| {
        let ns = format!("{row}{tag}");
        Path {
            written: written(&ns),
            ns,
            member,
            answer,
        }
    };
    [
        at("nested", &|_| "Outer.Inner".to_string(), "deep", 21),
        at("ns", &|ns| format!("lib.{ns}.Far"), "k", 9),
        at("abs", &|ns| format!("..lib.{ns}.Far"), "k", 9),
    ]
}

/// Run `body_of(path)` once a path and assert the answer the path's sort gives.
fn each_path(row: &str, body_of: impl Fn(&Path) -> String) {
    for path in paths(row) {
        assert_eq!(ints(&path.ns, &body_of(&path)), [path.answer], "{}", path.ns);
    }
}

/// A refusal's sentences with what differs between two fixtures of one row taken out:
/// the position, and the namespace.
fn sentences(ns: &str, body: &str) -> Vec<String> {
    load_errors_of(&source(ns, body))
        .into_iter()
        .map(|e| {
            let said = e.split_once(": ").map_or(e.as_str(), |(_, said)| said);
            said.replace(ns, "NS")
        })
        .collect()
}

// ── the rule: an operation body ─────────────────────────────────────────────

/// An argument at a `Type` parameter is the sort the path names.
#[test]
fn an_argument_names_the_sort_its_bare_name_names() {
    each_path("rxt6sarg", |p| {
        format!(
            "  operation go() -> Int64 = which({})\n  rule r(?x) :- ?x <=> go()",
            p.written
        )
    });
}

/// A `let` binds the type value: it is handed on as one, and a dot on the bound name is
/// the sort's companion call.
#[test]
fn a_let_binds_the_sort() {
    each_path("rxt6slet", |p| {
        format!(
            "  operation go() -> Int64 =\n    let t = {}\n    which(t)\n  rule r(?x) :- ?x <=> go()",
            p.written
        )
    });
    each_path("rxt6sletdot", |p| {
        format!(
            "  operation go() -> Int64 =\n    let t = {}\n    t.{}()\n  rule r(?x) :- ?x <=> go()",
            p.written, p.member
        )
    });
}

/// An operation's result declared `Type`.
#[test]
fn a_result_is_the_sort() {
    each_path("rxt6sres", |p| {
        format!(
            "  operation ty() -> Type = {}\n  operation go() -> Int64 = which(ty())\n  rule r(?x) :- ?x <=> go()",
            p.written
        )
    });
}

/// A parenthesized receiver: the dot is the companion call of the sort the path names.
#[test]
fn a_parenthesized_receiver_in_an_operation_body_is_the_sort() {
    each_path("rxt6srecv", |p| {
        format!(
            "  operation go() -> Int64 = ({}).{}()\n  rule r(?x) :- ?x <=> go()",
            p.written, p.member
        )
    });
}

/// A free-standing entity, an eponymous sort and an alias named by a path are what their
/// bare names are: each is the type `which` knows by its imported name, and the alias, as
/// a receiver, binds the parameters it fixes — in both bodies.
#[test]
fn an_entity_an_eponymous_sort_and_an_alias_keep_their_bare_reading() {
    for (ns, name, expected) in [
        ("rxt6sentity", "Pt", 5),
        ("rxt6sepon", "Leaf", 6),
        ("rxt6salias", "FA", 7),
    ] {
        let body = format!(
            "  operation go() -> Int64 = which(lib.{ns}.{name})\n  rule r(?x) :- ?x <=> go()"
        );
        assert_eq!(ints(ns, &body), [expected], "{ns}");
    }
    assert_eq!(
        ints(
            "rxt6saliasrecv",
            "  operation go() -> Int64 = (lib.rxt6saliasrecv.FA).one()\n  rule r(?x) :- ?x <=> go()",
        ),
        [1]
    );
    assert_eq!(
        ints(
            "rxt6saliasrule",
            "  rule r(?x) :- ?x <=> (lib.rxt6saliasrule.FA).one()",
        ),
        [1]
    );
}

/// The path is a value of type `Type` wherever a value is written: a branch of an `if`,
/// an argument that fixes a caller's type parameter, the body of a lambda.
#[test]
fn a_path_is_a_type_value_wherever_a_value_is_written() {
    for (ns, body, expected) in [
        (
            "rxt6sif",
            "  operation go(b: Bool) -> Int64 = which(if b then Outer.Inner else lib.rxt6sif.Far)\n  rule r(?x) :- ?x <=> go(true)\n  rule r(?x) :- ?x <=> go(false)",
            vec![21, 9],
        ),
        (
            "rxt6sgeneric",
            "  operation idT[T](x: T) -> T = x\n  operation go() -> Int64 = which(idT(Outer.Inner))\n  rule r(?x) :- ?x <=> go()",
            vec![21],
        ),
        (
            "rxt6slambda",
            "  operation ap(f: (Int64) -> Type) -> Int64 = which(f(1))\n  operation go() -> Int64 = ap(lambda n -> lib.rxt6slambda.Far)\n  rule r(?x) :- ?x <=> go()",
            vec![9],
        ),
    ] {
        assert_eq!(ints(ns, body), expected, "{ns}");
    }
}

/// Where the slot is of another sort the refusal is the ordinary mismatch, naming the
/// sort the path denotes.
#[test]
fn a_path_in_a_slot_of_another_sort_is_an_ordinary_mismatch() {
    for (ns, body, said) in [
        (
            "rxt6sstring",
            "  operation sz(s: String) -> Int64 = 1\n  operation go() -> Int64 = sz(Outer.Inner)",
            "expected String, got Type (Inner)",
        ),
        (
            "rxt6sbool",
            "  operation go() -> Int64 = if Outer.Inner then 1 else 2",
            "expected Bool, got Type (Inner)",
        ),
    ] {
        let rendered = refusal(ns, body);
        assert!(rendered.contains(said), "{ns}: `{said}` not in {rendered}");
        assert!(!rendered.contains(UNRESOLVED), "{ns}: {rendered}");
    }
}

/// A chain that continues past the sort reaches the sort at its inner level: the path is
/// refused as the one-segment `Inner.deep` is, sentence for sentence. It drew a refusal
/// of its own before, about the sort — a segment nothing declares, or, where the last
/// segment resolves bare as here, an argument of `field_access` of the wrong type.
#[test]
fn a_member_past_the_sort_is_read_off_the_sort() {
    let path = sentences("rxt6spast", "  operation go() -> Int64 = Outer.Inner.deep");
    let bare = sentences("rxt6spastbare", "  operation go() -> Int64 = Inner.deep");
    assert!(!bare.is_empty(), "the one-segment spelling is refused today");
    assert_eq!(path, bare);
}

/// An eponymous sort is no written type by its bare name, and none by a path: as the
/// receiver of a dot the two spellings draw one refusal, in an operation body and in a
/// rule body. In a rule body the path was left its chain, and drew the unresolved-name
/// refusal where the bare name drew another.
#[test]
fn an_eponymous_sort_by_a_path_is_refused_as_its_bare_name_is() {
    const EPON: &str = "  sort Ep\n    entity Ep(name: String)\n    operation em() -> Int64 = 8\n  end\n";
    for (row, wrap) in [
        ("rxt6seponop", ("  operation go() -> Int64 = ", "\n  rule r(?x) :- ?x <=> go()")),
        ("rxt6seponrule", ("  rule r(?x) :- ?x <=> ", "")),
    ] {
        let said = |tag: &str, receiver: &str| {
            let ns = format!("{row}{tag}");
            let receiver = receiver.replace("NS", &ns);
            sentences(&ns, &format!("{EPON}{}({receiver}).em(){}", wrap.0, wrap.1))
        };
        let bare = said("bare", "Ep");
        assert!(!bare.is_empty(), "{row}: the bare spelling is refused today");
        assert_eq!(said("path", "test.NS.Ep"), bare, "{row}");
    }
}

/// The whole name gets first refusal over a field of a const's value, for a sort as for
/// a const and a call. Beside `const origin: Q` stands a namespace `origin`: its sort `X`
/// is what `origin.X` names, not the field `X` of the const — which is what the chain
/// was read as while no rung read a sort, and what it still is where the namespace
/// declares no `X`.
#[test]
fn the_whole_name_is_read_before_a_consts_field() {
    let beside = |member: &str| {
        format!(
            "  sort Q\n    entity q(X: Int64)\n    operation getX(v: Q) -> Int64 = 7\n  end\n  const origin: Q = Q.q(7)\n  namespace origin\n{member}  end\n"
        )
    };
    for (ns, member, go, expected) in [
        (
            "rxt6swholesort",
            "    sort X\n      operation xo() -> Int64 = 2\n    end\n",
            "(origin.X).xo()",
            2,
        ),
        ("rxt6swholeconst", "    const X: Int64 = 3\n", "origin.X", 3),
        (
            "rxt6swholecall",
            "    operation getX() -> Int64 = 3\n",
            "origin.getX()",
            3,
        ),
        ("rxt6swholefield", "    const Y: Int64 = 3\n", "origin.X", 7),
    ] {
        let body = format!(
            "{}  operation go() -> Int64 = {go}\n  rule r(?x) :- ?x <=> go()",
            beside(member)
        );
        assert_eq!(ints(ns, &body), [expected], "{ns}");
    }
}

// ── the rule: a rule body ───────────────────────────────────────────────────

/// The receiver of a dot written in a rule body, as in an operation body.
#[test]
fn a_parenthesized_receiver_in_a_rule_body_is_the_sort() {
    each_path("rxt6srule", |p| {
        format!("  rule r(?x) :- ?x <=> ({}).{}()", p.written, p.member)
    });
}

// ── fences ──────────────────────────────────────────────────────────────────

/// The imported bare names, in every position a path is written above.
#[test]
fn the_imported_bare_names_are_unchanged() {
    for (ns, body, expected) in [
        (
            "rxt6sbarearg",
            "  operation go() -> Int64 = which(Inner) + 100 * which(Far)\n  rule r(?x) :- ?x <=> go()",
            921,
        ),
        (
            "rxt6sbarelet",
            "  operation go() -> Int64 =\n    let t = Inner\n    t.deep()\n  rule r(?x) :- ?x <=> go()",
            21,
        ),
        (
            "rxt6sbareres",
            "  operation ty() -> Type = Far\n  operation go() -> Int64 = which(ty())\n  rule r(?x) :- ?x <=> go()",
            9,
        ),
        (
            "rxt6sbarerecv",
            "  operation go() -> Int64 = (Inner).deep() + 100 * (Far).k()\n  rule r(?x) :- ?x <=> go()",
            921,
        ),
        ("rxt6sbarerule", "  rule r(?x) :- ?x <=> (Inner).deep()", 21),
        (
            "rxt6sbarekinds",
            "  operation go() -> Int64 = which(Pt) + 100 * which(Leaf) + 10000 * which(FA)\n  rule r(?x) :- ?x <=> go()",
            70605,
        ),
    ] {
        assert_eq!(ints(ns, body), [expected], "{ns}");
    }
}

/// The companion calls: a call's functor is the whole dotted name.
#[test]
fn the_companion_calls_are_unchanged() {
    for (ns, body, expected) in [
        (
            "rxt6scompop",
            "  operation go() -> Int64 = Outer.Inner.deep() + 100 * lib.rxt6scompop.Far.k()\n  rule r(?x) :- ?x <=> go()",
            921,
        ),
        ("rxt6scomprule", "  rule r(?x) :- ?x <=> Outer.Inner.deep()", 21),
        (
            "rxt6scompns",
            "  rule r(?x) :- ?x <=> lib.rxt6scompns.Far.k()",
            9,
        ),
    ] {
        assert_eq!(ints(ns, body), [expected], "{ns}");
    }
}

/// A dotted name that resolves to a rule is the relation, at a namespace and past a
/// nested sort.
#[test]
fn a_dotted_rule_citation_is_still_the_relation() {
    for (ns, body) in [
        (
            "rxt6scite",
            "  operation go() -> Int64 effects Error = if lib.rxt6scite.rel.isEmpty then 0 else 1\n  rule r(?x) :- ?x <=> go()",
        ),
        (
            "rxt6scitenested",
            "  operation go() -> Int64 effects Error = if Outer.Inner.rws.isEmpty then 0 else 1\n  rule r(?x) :- ?x <=> go()",
        ),
    ] {
        assert_eq!(ints(ns, body), [1], "{ns}");
    }
}

/// A dotted name that resolves to a const is its value, at a namespace and past a nested
/// sort.
#[test]
fn a_dotted_const_is_still_its_value() {
    assert_eq!(
        ints(
            "rxt6sconst",
            "  operation go() -> Int64 = lib.rxt6sconst.K + Outer.Inner.IC\n  rule r(?x) :- ?x <=> go()",
        ),
        [11]
    );
}

/// A parameter named like the path's root is the receiver, and the dot reads its field.
#[test]
fn a_binder_named_like_the_root_is_still_the_receiver() {
    for (ns, body) in [
        (
            "rxt6sbinder",
            "  operation go(Outer: P) -> Int64 = Outer.t\n  rule r(?x) :- ?x <=> go(P(3))",
        ),
        (
            "rxt6sbinderns",
            "  operation go(lib: P) -> Int64 = lib.t\n  rule r(?x) :- ?x <=> go(P(3))",
        ),
    ] {
        assert_eq!(ints(ns, body), [3], "{ns}");
    }
}

/// Under such a binder the sort is still reached by its absolute name, beside the
/// binder's field.
#[test]
fn a_path_from_the_root_is_reached_past_a_binder() {
    assert_eq!(
        ints(
            "rxt6spast2",
            "  operation go(lib: P) -> Int64 = lib.t + (..lib.rxt6spast2.Far).k()\n  rule r(?x) :- ?x <=> go(P(3))",
        ),
        [12]
    );
}

/// A clause's own term keeps the chain: the fact and the goal that spell one path build
/// one term, for a rule's name and for a sort's. And it is the chain that is stored: the
/// reference the bare name is does not match it, from either side — the boundary of the
/// module doc, in a data slot.
#[test]
fn a_data_slot_still_stores_the_chain() {
    for (ns, body, expected) in [
        (
            "rxt6sdatarel",
            "  fact holds(lib.rxt6sdatarel.rel)\n  rule r(1) :- holds(lib.rxt6sdatarel.rel)",
            vec![1],
        ),
        (
            "rxt6sdatasort",
            "  fact holds(Outer.Inner)\n  rule r(1) :- holds(Outer.Inner)",
            vec![1],
        ),
        (
            "rxt6sdatabaregoal",
            "  fact holds(Outer.Inner)\n  rule r(1) :- holds(Inner)",
            vec![],
        ),
        (
            "rxt6sdatabarefact",
            "  fact holds(Inner)\n  rule r(1) :- holds(Outer.Inner)",
            vec![],
        ),
    ] {
        assert_eq!(ints(ns, body), expected, "{ns}");
    }
}

/// The boundary (module doc). An argument written in a rule body's own term is the term
/// the clause stores: the path stays its chain there, and `which` is handed that chain.
#[test]
fn a_rule_bodys_argument_is_still_the_term_it_was() {
    assert_eq!(
        ints("rxt6sruleargbare", "  rule r(?x) :- ?x <=> which(Inner)"),
        [21]
    );
    assert_eq!(
        ints("rxt6srulearg", "  rule r(?x) :- ?x <=> which(Outer.Inner)"),
        [0]
    );
}
