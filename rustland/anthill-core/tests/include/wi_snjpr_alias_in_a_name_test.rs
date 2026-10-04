//! WI-20260924-SNJPR — a type ALIAS in a NAME is read through: member access, the bare-spec
//! sugar, the names a clause brings into scope, binding blocks, imports, call-site bracket
//! keys and type positions.
//!
//! WI-20260924-F8PYZ made a SPEC CLAUSE read an alias as the spec it stands for. Everywhere
//! else an alias of a sort was a name with nothing behind it — each loud, none what the
//! author meant. Every such name is resolved EARLIER than a spec clause: in the scan
//! (imports, the scope parents a `requires` adds, rule-head addresses and the 059 R3
//! census), or in the declaration pass in source order. So the scan now knows each alias's
//! target HEAD once imports are wired (`KnowledgeBase::alias_heads`, sub-pass 2b), the
//! symbol-answering readers read an alias through it, and the term-answering readers
//! (type positions, the sugar's fixed member) read `alias_targets`, which the load now
//! records for every alias before any declaration is lowered, in dependency order. A name
//! is read through where it is USED, never where one is DECLARED: a rule head keeps the
//! address it spells.
//!
//! A row's "Was:" is the pre-change binary on the same program; a row without one, or the
//! first spelling of a row that loops over spellings, is a CONTROL — the direct spelling,
//! which passes either way by design.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! MEASURED 2026-09-27, one back-out at a time over this file and F8PYZ's
//! (`wi_f8pyz_spec_clause_alias_test`, which no back-out fails), each a MUTATION that
//! leaves the code in place and wrong:
//!
//! 1. THE SCAN RESOLVES NO ALIAS HEAD (`resolve_scan_alias_heads` inserts nothing): the
//!    eight rows the scan-time readers serve —
//!    [`a_member_reached_through_an_alias_dispatches`],
//!    [`an_operation_of_a_sort_is_reached_through_its_alias`],
//!    [`a_requirement_through_an_alias_brings_its_names_into_scope`],
//!    [`a_conversion_through_an_alias_lends_its_names`],
//!    [`an_import_through_an_alias_resolves`],
//!    [`an_import_through_an_alias_of_an_imported_sort_resolves`],
//!    [`a_binding_block_through_an_alias_is_censused_at_its_sort`],
//!    [`a_bracket_key_through_an_alias_selects`].
//! 2. THE DOTTED LADDER HAS NO ALIAS RUNG (`dotted_through_alias` answers nothing):
//!    [`a_member_reached_through_an_alias_dispatches`],
//!    [`an_operation_of_a_sort_is_reached_through_its_alias`].
//! 3. `Alias.Member` IN A TYPE POSITION READS AS WRITTEN (`alias_type_member` skipped):
//!    [`the_sugar_reads_an_alias_as_its_spec`],
//!    [`the_sugar_through_an_alias_keeps_what_it_fixes`],
//!    [`the_sugar_through_an_alias_requires_what_it_fixes`],
//!    [`an_alias_reads_an_alias_declared_below_it`],
//!    [`a_field_reads_an_alias_declared_in_a_later_file`].
//! 4. A TYPE-POSITION APPLICATION READS THE ALIAS AS WRITTEN (`type_alias_application`):
//!    [`an_alias_applied_to_further_arguments_is_its_sort_applied`],
//!    [`an_alias_of_an_applied_alias_merges_their_bindings`],
//!    [`an_application_rebinding_what_its_alias_fixes_is_refused`].
//! 5. A FIELD READ DOES NOT READ THE RECEIVER'S ALIAS (`resolve_projected_member`):
//!    [`a_value_typed_by_an_alias_has_its_fields`],
//!    [`an_alias_reads_an_alias_declared_below_it`].
//! 6. DOT DISPATCH SEARCHES THE ALIAS FOR MEMBERS (`recv_sort` as written):
//!    [`an_operation_of_a_sort_is_reached_through_its_alias`].
//! 7. NO ALIAS PRE-PASS (`declare_type_aliases` records nothing, so each level pre-loads
//!    its own aliases in source order again): [`an_alias_reads_an_alias_declared_below_it`],
//!    [`a_field_reads_an_alias_declared_in_a_later_file`].
//! 8. A BINDING VALUE READS AN APPLIED ALIAS AS WRITTEN (`sort_binding_to_value`, the
//!    clause canon an alias is recorded in): [`a_positional_alias_application_provides_its_spec`],
//!    [`an_alias_of_an_applied_alias_merges_their_bindings`].
//! 9. A BRACKET KEY IS NOT READ THROUGH (`call_key_alias_head`):
//!    [`a_bracket_key_through_an_alias_selects`].
//! 10. THE BINDING-BLOCK CENSUS READS THE WRITTEN NAME (`collect_provides_block`):
//!     [`a_binding_block_through_an_alias_is_censused_at_its_sort`] — the load still
//!     files the clause on `Rec.freshp`, and the census misses the second entry.
//! 11. THE PRE-PASS ORDERS BY A NAME'S FIRST SEGMENT ONLY (`collect_type_expr_heads`):
//!     [`an_alias_of_a_qualified_applied_alias_in_a_later_file_merges`] — `q.S2A` is not
//!     seen as naming `S2A`, so `S2AB` is recorded over the unrecorded alias.
//!
//! [`a_binding_block_through_an_alias_realizes_its_sort`] fails under none of these: its
//! reading is `load_provides_block`'s through `read_spec_alias`, which none of them
//! touches (not measured separately; F8PYZ's refusal stood there before this change).
//!
//! Every row that loops over spellings runs the direct one FIRST, and no back-out failed a
//! row on it: it is the alias spelling that fails.

use crate::common::{
    assert_refused_naming, expect_loaded, interp_for, interp_for_files, try_load_kb_with,
};
use anthill_core::eval::Value;

// ── the fixture ────────────────────────────────────────────────────────────────────────

/// A spec `Store` with its type member `State`, the aliases `StoreAlias = Store` and
/// `WisStore = Store[State = WIS]`, the state shapes `WIS` and `NoSp`, and `FileStore`
/// providing `Store` at `WIS` — then `extra`. `go()` returns `goal`.
fn program(extra: &str, goal: &str) -> String {
    format!(
        r#"
namespace t
  import anthill.prelude.{{Int64, Bool, String}}
  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
  end
  sort StoreAlias = Store
  sort WisStore = Store[State = WIS]
  sort WIS
    entity wis(n: Int64)
  end
  sort NoSp
    entity nosp(n: Int64)
  end
  sort FileStore
    provides Store[State = WIS]
    operation peek(s: WIS) -> Int64 = s.n
  end
{extra}
  operation go() -> Int64 = {goal}
end
"#
    )
}

fn run_go(mut interp: anthill_core::eval::Interpreter) -> i64 {
    match interp.call("t.go", &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`t.go` must run to an Int64: {other:?}"),
    }
}

fn run(src: &str) -> i64 {
    run_go(interp_for(src))
}

fn load_errors(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

// ── member access ──────────────────────────────────────────────────────────────────────

/// A spec operation reached through an alias, bare, carrying bindings, and qualified.
/// Was: "unknown functor" for each alias spelling.
#[test]
fn a_member_reached_through_an_alias_dispatches() {
    for callee in [
        "Store.peek",
        "StoreAlias.peek",
        "WisStore.peek",
        "t.StoreAlias.peek",
    ] {
        let src = program("", &format!("{callee}(wis(n: 9))"));
        assert_eq!(run(&src), 9, "{callee}");
    }
}

/// An operation of a DATA sort, reached through an alias as `Alias.op(…)` and through a
/// receiver typed by an alias. Was: "unknown functor", and "no such member (dot dispatch)".
#[test]
fn an_operation_of_a_sort_is_reached_through_its_alias() {
    let counter = "  sort Counter\n    entity counter(n: Int64)\n    \
                   operation bump(c: Counter) -> Int64 = c.n + 1\n  end\n  sort CA = Counter\n";
    for (param, call) in [
        ("Counter", "c.bump()"),
        ("Counter", "Counter.bump(c)"),
        ("CA", "c.bump()"),
        ("Counter", "CA.bump(c)"),
    ] {
        let src = program(
            &format!("{counter}  operation f(c: {param}) -> Int64 = {call}"),
            "f(counter(n: 4))",
        );
        assert_eq!(run(&src), 5, "c: {param}, {call}");
    }
}

// ── the bare-spec sugar ────────────────────────────────────────────────────────────────

/// `Alias.State` in a signature is the sugar's carrier, as `Store.State` is. Was: refused,
/// "'StoreAlias.State' is not manifest".
#[test]
fn the_sugar_reads_an_alias_as_its_spec() {
    for member in ["Store.State", "StoreAlias.State"] {
        let src = program(
            &format!("  operation look(s: {member}) -> Int64 = Store.peek(s)"),
            "look(wis(n: 9))",
        );
        assert_eq!(run(&src), 9, "{member}");
    }
}

/// A member the alias FIXES is its type: `WisStore.State` is `WIS`, whose `n` a body reads.
/// Was: refused as a projection off the spec.
#[test]
fn a_member_the_alias_fixes_is_its_type() {
    for ty in ["WIS", "WisStore.State"] {
        let src = program(
            &format!("  operation look(s: {ty}) -> Int64 = s.n"),
            "look(wis(n: 9))",
        );
        assert_eq!(run(&src), 9, "s: {ty}");
    }
}

/// `Spec2` over two parameters, `S2A` fixing the first to `WIS`, and `Both` providing it
/// at `WIS` and `NoSp`.
const SPEC2: &str = "  sort Spec2\n    sort A = ?\n    sort B = ?\n    \
                     operation both(a: A, b: B) -> Int64\n  end\n  sort S2A = Spec2[A = WIS]\n  \
                     sort Both\n    provides Spec2[A = WIS, B = NoSp]\n    \
                     operation both(a: WIS, b: NoSp) -> Int64 = a.n + b.n\n  end\n";

/// Through an alias fixing SOME parameters, the synthesized requirement keeps them: `S2A.B`
/// requires `Spec2[A = WIS, B = ?P]`, which the body's call at `A = WIS` needs.
#[test]
fn the_sugar_through_an_alias_keeps_what_it_fixes() {
    for member in ["Spec2.B", "S2A.B"] {
        let src = program(
            &format!("{SPEC2}  operation useB(a: WIS, b: {member}) -> Int64 = Spec2.both(a, b)"),
            "useB(wis(n: 4), nosp(n: 5))",
        );
        assert_eq!(run(&src), 9, "b: {member}");
    }
}

/// … and the requirement the sugar synthesizes names what the alias fixes: `useB`'s
/// `requires` is `Spec2[A = WIS, B = ?P]`, as if the explicit `[P] … requires Spec2[A =
/// WIS, B = P]` were written — read off the operation's recorded clauses. That a call
/// owes it is driven by `wi_ycpaj_bare_spec_sugar_call_requirement_test`.
/// Was: refused as a projection off the alias.
#[test]
fn the_sugar_through_an_alias_requires_what_it_fixes() {
    for (member, want) in [("Spec2.B", "Spec2[B = "), ("S2A.B", "Spec2[A = WIS, B = ")] {
        let src = program(
            &format!("{SPEC2}  operation useB(a: WIS, b: {member}) -> Int64 = 1"),
            "1",
        );
        let kb = expect_loaded(try_load_kb_with(&src));
        let op = kb
            .try_resolve_symbol("t.useB")
            .expect("`t.useB` is declared");
        let rec = anthill_core::kb::op_info::lookup_operation_info(&kb, op)
            .expect("`t.useB` has an OperationInfo");
        let clauses: Vec<String> = rec
            .requires
            .iter()
            .map(|v| anthill_core::kb::typing::type_display_name_value(&kb, v))
            .collect();
        assert!(
            clauses.iter().any(|c| c.starts_with(want)),
            "b: {member} — expected a requirement `{want}…`, got {clauses:?}"
        );
    }
}

// ── the names a clause brings into scope ───────────────────────────────────────────────

/// `requires StoreAlias[State = S]` brings `Store`'s names into scope bare, as `requires
/// Store[…]` does. Was: "`peek` … not in scope as a bare name here".
#[test]
fn a_requirement_through_an_alias_brings_its_names_into_scope() {
    for spec in ["Store", "StoreAlias"] {
        let src = program(
            &format!(
                "  sort User\n    sort S = ?\n    requires {spec}[State = S]\n    \
                 operation look(s: S) -> Int64 = peek(s)\n  end"
            ),
            "User.look(wis(n: 9))",
        );
        assert_eq!(run(&src), 9, "requires {spec}[State = S]");
    }
}

/// A conversion through an alias lends the provided spec's names: `Mid.zug` is `Base`'s.
/// Was: "unknown functor" for `Mid.zug`.
#[test]
fn a_conversion_through_an_alias_lends_its_names() {
    for spec in ["Base", "BaseAlias"] {
        let extra = format!(
            "  sort Base\n    sort T = ?\n    operation zug(x: T) -> Int64\n  end\n  \
             sort BaseAlias = Base\n  sort Mid\n    sort T = ?\n    provides {spec}[T = T]\n  end\n  \
             sort C\n    entity c(n: Int64)\n    provides Mid[T = C]\n    \
             operation zug(x: C) -> Int64 = x.n\n  end"
        );
        assert_eq!(
            run(&program(&extra, "Mid.zug(c(n: 4))")),
            4,
            "provides {spec}"
        );
    }
}

// ── imports ────────────────────────────────────────────────────────────────────────────

/// `Store` and its alias in namespace `qa`, `FileStore` providing it in `t`, which writes
/// `import`.
fn importing(import: &str) -> String {
    format!(
        r#"
namespace qa
  import anthill.prelude.{{Int64}}
  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
  end
  sort StoreAlias = Store
end
namespace t
  import anthill.prelude.{{Int64}}
  {import}
  sort WIS
    entity wis(n: Int64)
  end
  sort FileStore
    provides qa.Store[State = WIS]
    operation peek(s: WIS) -> Int64 = s.n
  end
  operation go() -> Int64 = peek(wis(n: 9))
end
"#
    )
}

/// An import reaching INTO an alias. Was: "unresolved import 'qa.StoreAlias.peek'".
#[test]
fn an_import_through_an_alias_resolves() {
    for import in [
        "import qa.Store.{peek}",
        "import qa.StoreAlias.{peek}",
        "import qa.StoreAlias.peek",
    ] {
        assert_eq!(run(&importing(import)), 9, "{import}");
    }
}

/// An import through an alias the scan can resolve only once ANOTHER import is wired: the
/// alias's target is itself an imported name.
#[test]
fn an_import_through_an_alias_of_an_imported_sort_resolves() {
    let src = r#"
namespace qa
  import anthill.prelude.{Int64}
  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
  end
end
namespace qb
  import qa.{Store}
  sort StoreAlias = Store
end
namespace t
  import anthill.prelude.{Int64}
  import qb.StoreAlias.{peek}
  sort WIS
    entity wis(n: Int64)
  end
  sort FileStore
    provides qa.Store[State = WIS]
    operation peek(s: WIS) -> Int64 = s.n
  end
  operation go() -> Int64 = peek(wis(n: 9))
end
"#;
    assert_eq!(run(src), 9);
}

// ── binding blocks ─────────────────────────────────────────────────────────────────────

/// A binding block over `Stack`, spelled `spec`, whose `operation_map` realizes the
/// `@[host_implemented]` `Stack.size` — so the load is clean only if the block realizes
/// `Stack`.
fn binding_block(spec: &str) -> String {
    format!(
        r#"
namespace t
  import anthill.prelude.{{Int64}}
  sort Stack
    sort T = ?
    operation size(s: Self) -> Int64 @[host_implemented]
  end
  sort StackAlias = Stack
  provides {spec} language rust
    artifact "src/stack.rs"
    operation_map {{ size: "stack_size" }}
  end
end
"#
    )
}

/// Was: refused — "a `provides … language … end` block … does not read an alias".
#[test]
fn a_binding_block_through_an_alias_realizes_its_sort() {
    for spec in ["Stack", "StackAlias"] {
        expect_loaded(try_load_kb_with(&binding_block(spec)));
    }
}

/// A block's rule lands on the predicate of the sort it realizes, and the scan's 059 R3
/// census counts it there too: `freshp`, owned by the `namespace Rec` entry, is refused as
/// assembled from two entries whichever way the block names `Rec`. Was: refused as a block
/// through an alias; with the load alone reading through, the alias spelling put two
/// entries' clauses on one predicate in silence (F8PYZ's measurement).
#[test]
fn a_binding_block_through_an_alias_is_censused_at_its_sort() {
    for spec in ["Rec", "RecAlias"] {
        let src = format!(
            "namespace t\n  import anthill.prelude.{{Int64}}\n  sort Rec\n    \
             entity rec(n: Int64)\n  end\n  namespace Rec\n    rule freshp(1) :- true\n  \
             end\n  sort RecAlias = Rec\n  provides {spec} language anthill\n    \
             rule freshp(2) :- true\n  end\nend\n"
        );
        assert_refused_naming(
            &load_errors(&src),
            &[
                "not allowed in a secondary entry of sort 't.Rec'",
                "the predicate `freshp` is assembled from more than one entry",
            ],
            &format!("provides {spec} language anthill"),
        );
    }
}

// ── call-site bracket keys ─────────────────────────────────────────────────────────────

/// A bracket key naming an alias selects for the spec it stands for. Was: "unknown
/// type-param 'StoreAlias'".
#[test]
fn a_bracket_key_through_an_alias_selects() {
    for key in ["Store", "StoreAlias"] {
        let src = program(
            "  operation usePeek[P](s: P) -> Int64 requires Store[State = P] = Store.peek(s)",
            &format!("usePeek[{key} = FileStore](wis(n: 9))"),
        );
        assert_eq!(run(&src), 9, "[{key} = FileStore]");
    }
}

// ── type positions ─────────────────────────────────────────────────────────────────────

/// `Pair` over `L` and `R`, and its aliases.
const PAIR: &str =
    "  sort Pair\n    sort L = ?\n    sort R = ?\n    entity pair(l: L, r: R)\n  end\n  \
                    sort IntPair = Pair[L = Int64]\n  sort P2 = Pair\n  \
                    sort Full = Pair[L = Int64, R = String]\n";

fn pair_field(ty: &str) -> String {
    program(
        &format!("{PAIR}  operation f(x: {ty}) -> Int64 = x.l"),
        "f(pair(l: 3, r: \"s\"))",
    )
}

/// An alias applied to further arguments, by name and by position. Was: "`t.IntPair` has
/// no type parameter named 'R'", and "over-applied" for the positional.
#[test]
fn an_alias_applied_to_further_arguments_is_its_sort_applied() {
    for ty in [
        "Pair[L = Int64, R = String]",
        "IntPair[R = String]",
        "IntPair[String]",
    ] {
        assert_eq!(run(&pair_field(ty)), 3, "x: {ty}");
    }
}

/// A value typed by an alias has the fields of the type the alias stands for. Was: "no
/// such member (dot dispatch)" for every alias, bindings or not.
#[test]
fn a_value_typed_by_an_alias_has_its_fields() {
    for ty in ["Pair[L = Int64]", "IntPair", "P2", "Full"] {
        assert_eq!(run(&pair_field(ty)), 3, "x: {ty}");
    }
}

/// An application binding again what its alias fixes is refused, naming both.
#[test]
fn an_application_rebinding_what_its_alias_fixes_is_refused() {
    assert_refused_naming(
        &load_errors(&pair_field("IntPair[L = Bool, R = String]")),
        &[
            "'t.IntPair' is a type alias",
            "already binds `L` to `Int64`, which the application binds again",
        ],
        "IntPair[L = Bool, …]",
    );
}

// ── an alias of an applied alias ───────────────────────────────────────────────────────

/// `S2AB` over the APPLIED alias `S2A[B = NoSp]` is `Spec2[A = WIS, B = NoSp]`, the two
/// binding lists merged — in a provision it dispatches. Was: refused where declared, "`t.S2A`
/// has no type parameter named 'B'".
#[test]
fn an_alias_of_an_applied_alias_merges_their_bindings() {
    for (decl, spec) in [
        ("", "Spec2[A = WIS, B = NoSp]"),
        ("  sort S2AB = S2A[B = NoSp]\n", "S2AB"),
        ("  sort S2AP = S2A[NoSp]\n", "S2AP"),
    ] {
        let extra = format!(
            "  sort Spec2\n    sort A = ?\n    sort B = ?\n    \
             operation both(a: A, b: B) -> Int64\n  end\n  sort S2A = Spec2[A = WIS]\n{decl}  \
             sort Both\n    provides {spec}\n    \
             operation both(a: WIS, b: NoSp) -> Int64 = a.n + b.n\n  end"
        );
        let src = program(&extra, "Spec2.both(wis(n: 4), nosp(n: 5))");
        assert_eq!(run(&src), 9, "provides {spec}");
    }
}

/// A positional binding over a bare alias: `W2 = StoreAlias[WIS]` is `Store[State = WIS]`.
/// Was: refused twice — at the declaration, and at the clause as "stands for
/// `SortView(StoreAlias, WIS)`, which is not a sort".
#[test]
fn a_positional_alias_application_provides_its_spec() {
    for (decl, spec) in [("", "Store[WIS]"), ("  sort W2 = StoreAlias[WIS]\n", "W2")] {
        let extra = format!(
            "{decl}  sort F2\n    provides {spec}\n    operation peek(s: WIS) -> Int64 = 2\n  end"
        );
        // `F2` and `FileStore` both provide `Store` at `WIS`, so dispatch there is
        // ambiguous — exactly when `W2` reads as `Store[State = WIS]`.
        assert_refused_naming(
            &load_errors(&program(&extra, "Store.peek(wis(n: 1))")),
            &["ambiguous dispatch"],
            &format!("provides {spec}"),
        );
    }
}

// ── declaration order ──────────────────────────────────────────────────────────────────

/// An alias naming a member of an alias declared BELOW it. Was: "expected Y, got WIS" —
/// `Y` read `WisStore3.State` before `WisStore3` was recorded.
#[test]
fn an_alias_reads_an_alias_declared_below_it() {
    for (decl, ty) in [
        ("  sort Y = WIS\n", "Y"),
        (
            "  sort Y = WisStore3.State\n  sort WisStore3 = Store[State = WIS]\n",
            "Y",
        ),
    ] {
        let src = program(
            &format!("{decl}  operation look(s: {ty}) -> Int64 = s.n"),
            "look(wis(n: 5))",
        );
        assert_eq!(run(&src), 5, "{decl}");
    }
}

/// An entity field naming a member of an alias declared in a LATER file.
#[test]
fn a_field_reads_an_alias_declared_in_a_later_file() {
    let user = program(
        "  sort Holder\n    entity holder(x: LateWis.State)\n  end\n  \
         operation look(h: Holder) -> Int64 = h.x.n",
        "look(holder(x: wis(n: 6)))",
    );
    let decl = "namespace t\n  sort LateWis = Store[State = WIS]\nend\n";
    assert_eq!(run_go(interp_for_files(&[&user, decl])), 6);
}

/// An alias over an applied alias reached by its QUALIFIED path, declared in a LATER file:
/// the inner alias is still recorded first, so the two binding lists merge.
#[test]
fn an_alias_of_a_qualified_applied_alias_in_a_later_file_merges() {
    let extra = "  sort Spec2\n    sort A = ?\n    sort B = ?\n    \
                 operation both(a: A, b: B) -> Int64\n  end\n  sort S2AB = q.S2A[B = NoSp]\n  \
                 sort Both\n    provides S2AB\n    \
                 operation both(a: WIS, b: NoSp) -> Int64 = a.n + b.n\n  end";
    let user = program(extra, "Spec2.both(wis(n: 4), nosp(n: 5))");
    let decl = "namespace t\n  namespace q\n    sort S2A = Spec2[A = WIS]\n  end\nend\n";
    assert_eq!(run_go(interp_for_files(&[&user, decl])), 9);
}
