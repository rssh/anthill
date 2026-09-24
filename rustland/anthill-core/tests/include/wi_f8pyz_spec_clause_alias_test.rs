//! WI-20260924-F8PYZ — a spec clause reads a type ALIAS as the spec it stands for.
//!
//! With `sort StoreAlias = Store`, `sort FileStore provides StoreAlias[State = WIS] … end`
//! LOADED CLEAN and provided nothing: the provision was filed about `StoreAlias`, which
//! declares no operations and which no clause about `Store` meets, so `Store.peek(wis(n:
//! 9))` died at run time "operation has no body: Store.peek" while the same program
//! spelled `provides Store[State = WIS]` returned 9. Found by WI-20260923-ZBWMC's review
//! sweep; the same on the 09-20 binary.
//!
//! USER DECISIONS (2026-09-24): an alias is READ THROUGH, as aliases are in any language —
//! every alias of a spec, bare or carrying bindings — in a provision (its `where` block and
//! `default` mark with it), its `:- …` conditions, a sort's `requires` and an operation's.
//! An alias the reading has no answer for is refused, naming why. Member access through an
//! alias (`StoreAlias.peek`, the bare-spec sugar `StoreAlias.State`), a binding block, and
//! an alias in a type position are NOT this change: they are WI-20260924-SNJPR, which says
//! why a name needs more than a clause does; a binding block refuses an alias until then.
//!
//! AND A QUALIFIED SPEC NAME IS RESOLVED WHOLE: `provided_spec_symbol` and the `where`-block
//! reader resolved only its last segment in the writing scope, whose miss is a silent bare
//! intern, so every reader keyed on the provision's spec was blind to `qa.Colour`,
//! `qa.Store` — the data-sort refusal, the `default` row, the carrier check, the `where`
//! block.
//!
//! A row's "Was:" is the pre-change binary on the same program; a row without one is a
//! CONTROL, the direct spelling beside it, which passes either way by design.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! MEASURED 2026-09-24, one back-out at a time, each a MUTATION that leaves the code in
//! place and wrong — not a deletion, which would compile a different tree. The first two
//! also ran over the whole `wi_tests` binary, and nothing outside this file failed: 5082
//! passed and 26 failed under 1, before the two-parameter rows and the `default` mark's
//! were added; 5110 passed and 4 failed under 2.
//!
//! 1. NO ALIAS IS RECORDED — `record_alias_target` records nothing, so every clause reads
//!    the name as written, as before the change. 31 rows fail: all but the thirteen that
//!    pass under every back-out and four that name a spec through its namespace directly —
//!    the first three of 2 and the second of 8.
//! 2. A QUALIFIED SPEC NAME RESOLVED BY ITS LAST SEGMENT, as `provided_spec_symbol` did:
//!    [`a_data_sort_named_through_its_namespace_is_refused`],
//!    [`a_default_provision_named_through_its_namespace_dispatches`],
//!    [`a_bare_provision_named_through_its_namespace_names_no_carrier`],
//!    [`the_reflect_view_named_as_a_spec_is_refused_as_a_data_sort`].
//! 3. THE CLAUSE READER ANSWERS EVERY NAME AS WRITTEN — `read_spec_alias` returns before it
//!    reads, the alias still recorded: the same 31 rows as 1.
//! 4. AN ALIAS RECORDED AS THE TYPE ITS DECLARATION LOWERS TO (`type_expr_to_value`, a
//!    parameter as its variable) rather than in the clause canon: the five rows of an alias
//!    fixing a type parameter — [`an_alias_fixing_a_parameter_provides_at_the_parameter`],
//!    [`an_alias_written_above_the_parameter_it_fixes_is_the_parameter`],
//!    [`a_sort_requirement_through_an_alias_fixing_a_parameter_is_supplied`],
//!    [`a_conversion_through_an_alias_is_forwarded`],
//!    [`a_condition_through_an_alias_holds_and_binds`].
//! 5. THE PRE-SCAN EXPECTS EVERY NAMED SPEC TO DECODE (its `let … else` an `expect`):
//!    [`the_reflect_view_named_as_a_spec_is_refused_as_a_data_sort`], as a panic.
//! 6. A BARE NAME IN AN OPERATION'S `requires` STAYS AS WRITTEN (`bare_contract_spec`):
//!    [`an_operation_requirement_through_an_alias_is_checked_at_the_call`].
//! 7. THE CARRIER PRE-SCAN SKIPS A BARE PROVISION again:
//!    [`an_alias_spelled_provision_narrows_the_sugar`].
//! 8. THE `where`-BLOCK READER RESOLVES THE LAST SEGMENT, as it did:
//!    [`a_where_block_through_an_alias_holds_the_spec_members`],
//!    [`a_where_block_named_through_its_namespace_holds_the_spec_members`],
//!    [`a_where_block_over_a_refused_alias_reports_once`].
//! 9. A BINDING BLOCK THROUGH AN ALIAS IS NOT REFUSED:
//!    [`a_binding_block_through_an_alias_is_refused`].
//! 10. A NAME THAT IS AN ALIAS AND OWNS MEMBERS READS AS THE ALIAS (`owns_members` false):
//!     [`a_name_that_is_an_alias_and_more_is_refused`].
//! 11. A CLAUSE MAY BIND AGAIN WHAT ITS ALIAS FIXES (`refuse_alias_rebinding` returns):
//!     [`a_clause_rebinding_what_its_alias_fixes_is_refused`].
//! 12. A PROVISION OVER A REFUSED ALIAS IS STILL FILED (`load_provides_clause` does not
//!     return): [`a_default_mark_over_a_refused_alias_reports_once`] alone — the `where`
//!     block's second diagnostic is 8's to catch, `spec_name_symbol` skipping the member.
//!
//! THIRTEEN PASS UNDER EVERY BACK-OUT, BY DESIGN. The controls, each the direct spelling
//! beside an alias row: [`the_spec_named_directly_dispatches`],
//! [`a_provision_split_from_its_declarations_dispatches`],
//! [`a_default_provision_named_directly_is_the_default`],
//! [`a_directly_spelled_provision_narrows_the_sugar`],
//! [`a_spec_of_two_parameters_named_directly_dispatches`],
//! [`a_data_sort_named_directly_is_refused_as_one`],
//! [`a_spec_named_through_its_namespace_dispatches`],
//! [`an_operation_requirement_named_directly_is_supplied`],
//! [`a_sort_requirement_named_directly_is_supplied`],
//! [`a_binding_block_named_directly_loads`], and
//! [`an_alias_in_a_binding_is_the_type_it_stands_for`], where an alias already meant its
//! type. And two that pass either way and say why at their site:
//! [`a_bare_alias_requirement_is_supplied_where_it_holds`] and
//! [`an_alias_over_an_applied_alias_is_refused_where_it_is_declared`].
//!
//! A row that loops over spellings runs its direct ones, the controls, FIRST. Run ALONE —
//! the alias spellings cut from a copy of this file — they pass under 1, 3, 4 and 6, the
//! back-outs that fail their rows: it is the alias spelling that fails a row.

use crate::common::{assert_refused_naming, interp_for, interp_for_files, try_load_kb_with};
use anthill_core::eval::Value;

// ── the fixture ────────────────────────────────────────────────────────────────────────

/// A spec `Store` with its sole type member `State`, the alias `StoreAlias = Store`, the
/// state shapes `WIS` and `NoSp`, then `extra` — the declarations under test. `go()`
/// returns `goal`.
fn program(extra: &str, goal: &str) -> String {
    format!(
        r#"
namespace t
  import anthill.prelude.{{Int64, Bool}}
  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
  end
  sort StoreAlias = Store
  sort WIS
    entity wis(n: Int64)
  end
  sort NoSp
    entity nosp(n: Int64)
  end
{extra}
  operation go() -> Int64 = {goal}
end
"#
    )
}

/// The carrier `FileStore`, whose `peek` returns its state's `n`, providing through `clause`.
fn file_store(clause: &str) -> String {
    format!("  sort FileStore\n    {clause}\n    operation peek(s: WIS) -> Int64 = s.n\n  end")
}

/// The call the provision rows drive: dispatch on `Store`, which only a provision of
/// `Store` can answer.
const PEEK: &str = "Store.peek(wis(n: 9))";

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

/// The refusal of an alias a spec clause cannot read, naming the alias and why.
#[track_caller]
fn assert_alias_refused(errs: &[String], alias: &str, why_tokens: &[&str], why: &str) {
    let mut tokens = vec![format!("'{alias}' is a type alias")];
    tokens.extend(why_tokens.iter().map(|t| t.to_string()));
    let tokens: Vec<&str> = tokens.iter().map(String::as_str).collect();
    assert_refused_naming(errs, &tokens, why);
}

// ── a provision ────────────────────────────────────────────────────────────────────────

/// The ticket's program. Was: loaded clean, and `Store.peek` died "operation has no body".
#[test]
fn a_provision_through_an_alias_dispatches() {
    let src = program(&file_store("provides StoreAlias[State = WIS]"), PEEK);
    assert_eq!(run(&src), 9);
}

/// The control: the spec written directly.
#[test]
fn the_spec_named_directly_dispatches() {
    let src = program(&file_store("provides Store[State = WIS]"), PEEK);
    assert_eq!(run(&src), 9);
}

/// An alias carrying bindings provides them, written by name or by position: `provides
/// WisStore` is `provides Store[State = WIS]`. Was: loaded clean and died like the bare one.
#[test]
fn a_parameterized_alias_provides_its_bindings() {
    for definition in ["Store[State = WIS]", "Store[WIS]"] {
        let extra = format!(
            "  sort WisStore = {definition}\n{}",
            file_store("provides WisStore")
        );
        assert_eq!(
            run(&program(&extra, PEEK)),
            9,
            "sort WisStore = {definition}"
        );
    }
}

/// A chain of aliases stands for the spec at its end. Was: died like the ticket's program.
#[test]
fn an_alias_of_an_alias_provides_the_spec_it_ends_at() {
    let extra = format!(
        "  sort StoreAlias2 = StoreAlias\n{}",
        file_store("provides StoreAlias2[State = WIS]")
    );
    assert_eq!(run(&program(&extra, PEEK)), 9);
}

/// The alias is read while the clause loads, and here it is declared BELOW the clause: the
/// declaration pass has recorded every alias by then. Was: died like the ticket's program.
#[test]
fn an_alias_declared_below_its_use_is_read_through() {
    let extra = format!(
        "{}\n  sort LateAlias = Store",
        file_store("provides LateAlias[State = WIS]")
    );
    assert_eq!(run(&program(&extra, PEEK)), 9);
}

/// … and in a file loaded AFTER the one naming it. Was: died like the ticket's program.
#[test]
fn an_alias_declared_in_a_later_file_is_read_through() {
    let user = program(&file_store("provides LaterAlias[State = WIS]"), PEEK);
    let decl = "namespace t\n  sort LaterAlias = Store\nend\n";
    assert_eq!(run_go(interp_for_files(&[&user, decl])), 9);
}

/// The control for the row above: the same two files, the spec named directly.
#[test]
fn a_provision_split_from_its_declarations_dispatches() {
    let user = program(&file_store("provides Store[State = WIS]"), PEEK);
    let decl = "namespace t\n  sort LaterAlias = Store\nend\n";
    assert_eq!(run_go(interp_for_files(&[&user, decl])), 9);
}

/// Two providers of `Store` at `WIS`, `FileStore` answering 9 and `OtherStore` 0, one of
/// them marked `default` by `mark`.
fn two_providers(mark: &str) -> String {
    format!(
        "{}\n  sort OtherStore\n    provides Store[State = WIS]\n    \
         operation peek(s: WIS) -> Int64 = 0\n  end",
        file_store(mark)
    )
}

/// The `default` mark rides the provision, so it marks the spec the alias stands for. Was:
/// the mark named the alias and so did the provision, leaving `OtherStore` the only
/// provider of `Store` — the call answered 0, the OTHER provider, in silence.
#[test]
fn a_default_provision_through_an_alias_is_the_default() {
    let src = program(
        &two_providers("default provides StoreAlias[State = WIS]"),
        PEEK,
    );
    assert_eq!(run(&src), 9);
}

/// The controls: the mark written on the spec directly picks `FileStore`, and with no mark
/// the two providers are an ambiguity.
#[test]
fn a_default_provision_named_directly_is_the_default() {
    let marked = program(&two_providers("default provides Store[State = WIS]"), PEEK);
    assert_eq!(run(&marked), 9);
    let unmarked = program(&two_providers("provides Store[State = WIS]"), PEEK);
    assert_refused_naming(
        &load_errors(&unmarked),
        &["ambiguous dispatch"],
        "two unmarked providers",
    );
}

/// A provision's `where` block holds the members of the spec the alias stands for. Was:
/// refused — "`t.StoreAlias` declares no operation `peek`".
#[test]
fn a_where_block_through_an_alias_holds_the_spec_members() {
    let extra = "  sort FileStore\n    provides StoreAlias[State = WIS] where\n      \
                 operation peek(s: WIS) -> Int64 = s.n\n    end\n  end";
    assert_eq!(run(&program(extra, PEEK)), 9);
}

// ── the carrier's bare-spec sugar, narrowed by an alias-spelled provision ──────────────

/// A carrier providing through `clause`, whose `count` reads `s.n` off a `Store.State` —
/// which typechecks only if the provision narrows `State` to `WIS` inside the carrier
/// (WI-201 / ZBWMC).
fn narrowing(clause: &str) -> String {
    format!(
        "  sort WisStore = Store[State = WIS]\n  sort FileStore\n    {clause}\n    \
         operation peek(s: Store.State) -> Int64 = s.n\n    \
         operation count(s: Store.State) -> Int64 = s.n\n  end"
    )
}

/// Through the alias, bracketed and bare — the bare alias carries the binding itself. Was:
/// the provision was about the alias, so nothing narrowed `Store.State` and `s.n` was
/// refused ("declare no 'n'").
#[test]
fn an_alias_spelled_provision_narrows_the_sugar() {
    for clause in ["provides StoreAlias[State = WIS]", "provides WisStore"] {
        let src = program(&narrowing(clause), "FileStore.count(wis(n: 7))");
        assert_eq!(run(&src), 7, "{clause}");
    }
}

/// The control: the spec named directly narrows.
#[test]
fn a_directly_spelled_provision_narrows_the_sugar() {
    let src = program(
        &narrowing("provides Store[State = WIS]"),
        "FileStore.count(wis(n: 7))",
    );
    assert_eq!(run(&src), 7);
}

// ── an alias that fixes a type PARAMETER ───────────────────────────────────────────────

/// `Box[E = …]` provides `Store` at `Box[E = E]` through `spec`, generically, answering
/// 100; `Special` provides it at `Box[E = WIS]` alone, answering 200. The more specific
/// provider answers a `box(e: wis(…))`.
fn box_and_special(spec: &str) -> String {
    format!(
        "  sort Box\n    sort E = ?\n    sort StoreOfBox = Store[State = Box[E = E]]\n    \
         entity box(e: E)\n    provides {spec}\n    \
         operation peek(s: Box[E = E]) -> Int64 = 100\n  end\n  sort Special\n    \
         provides Store[State = Box[E = WIS]]\n    \
         operation peek(s: Box[E = WIS]) -> Int64 = 200\n  end"
    )
}

/// The alias fixes `State` to `Box[E = E]` with `E` the sort's own parameter, which a
/// clause writes as `Ref(E)` — the parameter dispatch generalizes over. Was: refused —
/// "ambiguous dispatch … on carrier `Box`": the provision was about the alias, so `Box`'s
/// own `peek` competed with `Special`'s.
#[test]
fn an_alias_fixing_a_parameter_provides_at_the_parameter() {
    for spec in ["Store[State = Box[E = E]]", "StoreOfBox"] {
        let src = program(&box_and_special(spec), "Store.peek(box(e: wis(n: 9)))");
        assert_eq!(run(&src), 200, "provides {spec}");
    }
}

/// … and so it is where the alias is written ABOVE the `sort E = ?` it names: the reading
/// resolves `E` by name, not by a variable the parameter has not published yet. Was:
/// refused, as above.
#[test]
fn an_alias_written_above_the_parameter_it_fixes_is_the_parameter() {
    let extra = "  sort Box
    sort StoreOfBox = Store[State = Box[E = E]]
    sort E = ?
    \
                 entity box(e: E)
    provides StoreOfBox
    \
                 operation peek(s: Box[E = E]) -> Int64 = 100
  end
  sort Special
    \
                 provides Store[State = Box[E = WIS]]
    \
                 operation peek(s: Box[E = WIS]) -> Int64 = 200
  end";
    assert_eq!(run(&program(extra, "Store.peek(box(e: wis(n: 9)))")), 200);
}

/// A tuple binding keeps its parameters as a directly written clause keeps them, so the two
/// spellings reach one verdict — here the same ambiguity between `Pairy` and `Special`.
/// Was: the provision was about the alias, `Special` alone provided, and the call ran.
#[test]
fn an_alias_binding_a_tuple_reads_as_the_tuple_written_directly() {
    for spec in ["Store[State = (A, Int64)]", "StoreOfPair"] {
        let extra = format!(
            "  sort Pairy\n    sort A = ?\n    sort StoreOfPair = Store[State = (A, Int64)]\n    \
             provides {spec}\n    operation peek(s: (A, Int64)) -> Int64 = 100\n  end\n  \
             sort Special\n    provides Store[State = (WIS, Int64)]\n    \
             operation peek(s: (WIS, Int64)) -> Int64 = 200\n  end"
        );
        assert_refused_naming(
            &load_errors(&program(&extra, "Store.peek((wis(n: 1), 5))")),
            &["ambiguous dispatch"],
            &format!("provides {spec}"),
        );
    }
}

/// A sort requiring the spec at its own parameter through `requirement`, and an operation
/// of it calling the spec's operation there.
fn user_requiring(requirement: &str) -> String {
    format!(
        "{}\n  sort User\n    sort S = ?\n    sort StoreOfS = Store[State = S]\n    \
         {requirement}\n    operation look(s: S) -> Int64 = Store.peek(s)\n  end",
        file_store("provides Store[State = WIS]")
    )
}

/// Was: refused — "missing `requires Store[State = …]` on enclosing sort": the requirement
/// was of the alias.
#[test]
fn a_sort_requirement_through_an_alias_fixing_a_parameter_is_supplied() {
    for requirement in ["requires Store[State = S]", "requires StoreOfS"] {
        let src = program(&user_requiring(requirement), "User.look(wis(n: 9))");
        assert_eq!(run(&src), 9, "{requirement}");
    }
}

/// A spec providing another through an alias of it at its own parameter — a CONVERSION,
/// which the loader forwards to every carrier of the first. Was: the provision was about
/// the alias, nothing was forwarded, and `Lo.lo` died at run time "operation has no body".
#[test]
fn a_conversion_through_an_alias_is_forwarded() {
    for spec in ["Lo[T = T]", "LoOfT"] {
        let extra = format!(
            "  sort Lo\n    sort T = ?\n    operation lo(x: T) -> Int64\n  end\n  \
             sort Hi\n    sort T = ?\n    sort LoOfT = Lo[T = T]\n    provides {spec}\n  end\n  \
             sort C\n    entity c(n: Int64)\n    provides Hi[T = C]\n    \
             operation lo(x: C) -> Int64 = x.n\n  end"
        );
        assert_eq!(
            run(&program(&extra, "Lo.lo(c(n: 5))")),
            5,
            "provides {spec}"
        );
    }
}

// ── an alias applied to the parameters it leaves open ──────────────────────────────────

/// `Spec2` over two parameters, the alias `S2A` fixing the first to `WIS`, and `Both`
/// answering `both` at `WIS` and `NoSp` — providing it through `spec`.
fn spec2(spec: &str) -> String {
    format!(
        "  sort Spec2\n    sort A = ?\n    sort B = ?\n    \
         operation both(a: A, b: B) -> Int64\n  end\n  sort S2A = Spec2[A = WIS]\n  \
         sort Both\n    provides {spec}\n    \
         operation both(a: WIS, b: NoSp) -> Int64 = a.n + b.n\n  end"
    )
}

/// Dispatch on `Spec2` at `WIS` and `NoSp`, which only a provision of `Spec2` there answers.
const BOTH: &str = "Spec2.both(wis(n: 4), nosp(n: 5))";

/// The alias's binding and the clause's together: `provides S2A[B = NoSp]` is `provides
/// Spec2[A = WIS, B = NoSp]`, and a positional binds the parameter the alias left open.
/// Was: loaded clean, and `Spec2.both` died "operation has no body".
#[test]
fn an_alias_fixing_one_parameter_is_applied_to_the_rest() {
    for spec in ["S2A[B = NoSp]", "S2A[NoSp]"] {
        assert_eq!(run(&program(&spec2(spec), BOTH)), 9, "provides {spec}");
    }
}

/// The control: the spec written directly, by name and by position.
#[test]
fn a_spec_of_two_parameters_named_directly_dispatches() {
    for spec in ["Spec2[A = WIS, B = NoSp]", "Spec2[WIS, NoSp]"] {
        assert_eq!(run(&program(&spec2(spec), BOTH)), 9, "provides {spec}");
    }
}

/// `Spec2` at `WIS` and a parameter `P`: directly — the controls, which pass either way by
/// design and come FIRST, so a back-out fails a row on an alias spelling after they have
/// passed — then through the alias by name and by position.
const SPEC2_AT_P: [&str; 4] = [
    "Spec2[A = WIS, B = P]",
    "Spec2[WIS, P]",
    "S2A[B = P]",
    "S2A[P]",
];

/// An operation requiring `Spec2` at `WIS` and its own `P` through `requirement`, beside
/// `Both`'s direct provision at `NoSp`.
fn op_requiring_spec2(requirement: &str, body: &str) -> String {
    format!(
        "{}\n  operation useBoth[P](a: WIS, b: P) -> Int64 requires {requirement} = {body}",
        spec2("Spec2[A = WIS, B = NoSp]")
    )
}

/// Was: refused — "missing `requires Spec2[B = …]` on enclosing sort": the requirement was
/// of the alias.
#[test]
fn an_operation_requirement_applying_an_alias_is_supplied() {
    for requirement in SPEC2_AT_P {
        let src = program(
            &op_requiring_spec2(requirement, "Spec2.both(a, b)"),
            "useBoth(wis(n: 4), nosp(n: 5))",
        );
        assert_eq!(run(&src), 9, "requires {requirement}");
    }
}

/// … and CHECKED at the call, binding what the alias left open: at `P = WIS` the
/// requirement is `Spec2[A = WIS, B = WIS]`, which nothing provides — the positional bound
/// `B`, not the `A` the alias fixed. Was: the call ran — the requirement was of the alias,
/// which nothing checked.
#[test]
fn an_operation_requirement_applying_an_alias_is_checked_at_the_call() {
    for requirement in SPEC2_AT_P {
        let src = program(
            &op_requiring_spec2(requirement, "1"),
            "useBoth(wis(n: 4), wis(n: 5))",
        );
        assert_refused_naming(
            &load_errors(&src),
            &[
                "expected a requirement suppliable at this call site",
                "Spec2[A = t.WIS, B = t.WIS]",
            ],
            &format!("an unmet `requires {requirement}`"),
        );
    }
}

/// A sort's requirement at its own parameter likewise. Was: refused — "missing `requires
/// Spec2[B = …]` on enclosing sort".
#[test]
fn a_sort_requirement_applying_an_alias_is_supplied() {
    for requirement in SPEC2_AT_P {
        let extra = format!(
            "{}\n  sort User2\n    sort P = ?\n    requires {requirement}\n    \
             operation look(a: WIS, b: P) -> Int64 = Spec2.both(a, b)\n  end",
            spec2("Spec2[A = WIS, B = NoSp]")
        );
        let src = program(&extra, "User2.look(wis(n: 4), nosp(n: 5))");
        assert_eq!(run(&src), 9, "requires {requirement}");
    }
}

/// An alias over an alias APPLIED to further bindings is refused where it is declared — a
/// type position applying bindings to a name that declares no parameters (WI-709's
/// `check_sort_type_args`) — which is what lets `alias_expansion` stop at such a link rather
/// than merge two binding lists. PASSES EITHER WAY: the refusal is the declaration's own and
/// stood before; this row pins the guard the reading relies on.
#[test]
fn an_alias_over_an_applied_alias_is_refused_where_it_is_declared() {
    let over_s2a = format!("  sort S2AB = S2A[B = NoSp]\n{}", spec2("S2AB"));
    let over_store_alias = format!(
        "  sort WisStore2 = StoreAlias[State = WIS]\n{}",
        file_store("provides WisStore2")
    );
    for (extra, token) in [
        (&over_s2a, "`t.S2A` has no type parameter named 'B'"),
        (
            &over_store_alias,
            "`t.StoreAlias` has no type parameter named 'State'",
        ),
    ] {
        assert_refused_naming(&load_errors(&program(extra, "1")), &[token], token);
    }
}

// ── the data-sort refusal an alias walked past ─────────────────────────────────────────

/// `Colour` has a constructor, so it is a DATA sort and nothing provides it (WI-1106) —
/// through an alias as directly. Was: the alias declared no constructors, so the clause
/// passed as a spec and the program RAN.
#[test]
fn an_alias_of_a_data_sort_is_refused_as_the_data_sort() {
    let extra = format!(
        "  sort Colour\n    entity red\n  end\n  sort ColourAlias = Colour\n{}",
        file_store("provides Store[State = WIS]\n    provides ColourAlias")
    );
    assert_refused_naming(
        &load_errors(&program(&extra, PEEK)),
        &["`provides t.Colour` cannot hold", "DATA sort"],
        "a provision naming a data sort through an alias",
    );
}

/// The control: the data sort named directly.
#[test]
fn a_data_sort_named_directly_is_refused_as_one() {
    let extra = format!(
        "  sort Colour\n    entity red\n  end\n{}",
        file_store("provides Store[State = WIS]\n    provides Colour")
    );
    assert_refused_naming(
        &load_errors(&program(&extra, PEEK)),
        &["`provides t.Colour` cannot hold", "DATA sort"],
        "a provision naming a data sort directly",
    );
}

// ── a spec named through its namespace ─────────────────────────────────────────────────

/// `qa` declares the spec, its alias and a data sort; `t` provides, naming them qualified,
/// with no import.
fn two_namespaces(clause: &str) -> String {
    format!(
        r#"
namespace qa
  import anthill.prelude.{{Int64}}
  sort Colour
    entity red
  end
  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
  end
  sort StoreAlias = Store
end
namespace t
  import anthill.prelude.{{Int64}}
  sort WIS
    entity wis(n: Int64)
  end
  sort FileStore
    {clause}
  end
  operation go() -> Int64 = qa.Store.peek(wis(n: 9))
end
"#
    )
}

const QA_PEEK: &str = "operation peek(s: WIS) -> Int64 = s.n";

/// Was: `provided_spec_symbol` resolved `Colour` alone in `t`, missed, and answered a bare
/// symbol that declares nothing — no constructors, so no refusal, and the program ran.
#[test]
fn a_data_sort_named_through_its_namespace_is_refused() {
    let src = two_namespaces(&format!(
        "provides qa.Store[State = WIS]\n    provides qa.Colour\n    {QA_PEEK}"
    ));
    assert_refused_naming(
        &load_errors(&src),
        &["`provides qa.Colour` cannot hold", "DATA sort"],
        "a provision naming a data sort through its namespace",
    );
}

/// The alias named through its namespace. Was: died like the ticket's program.
#[test]
fn an_alias_named_through_its_namespace_dispatches() {
    let src = two_namespaces(&format!(
        "provides qa.StoreAlias[State = WIS]\n    {QA_PEEK}"
    ));
    assert_eq!(run(&src), 9);
}

/// The control: the spec named through its namespace directly.
#[test]
fn a_spec_named_through_its_namespace_dispatches() {
    let src = two_namespaces(&format!("provides qa.Store[State = WIS]\n    {QA_PEEK}"));
    assert_eq!(run(&src), 9);
}

/// Was: the mark named the bare `Store`, a symbol with nothing behind it, and the load was
/// refused "nothing provides 'Store' at all".
#[test]
fn a_default_provision_named_through_its_namespace_dispatches() {
    let src = two_namespaces(&format!(
        "default provides qa.Store[State = WIS]\n    {QA_PEEK}"
    ));
    assert_eq!(run(&src), 9);
}

/// The reflect wrapper named as a spec, qualified or through an alias, is the DATA sort it
/// is (it has a constructor) and is refused as one — not a crash in the carrier pre-scan,
/// which reads a bare name now and found no base in a view with none. Was: the qualified
/// name resolved its last segment to nothing, and both spellings loaded and ran.
#[test]
fn the_reflect_view_named_as_a_spec_is_refused_as_a_data_sort() {
    for (decl, spec) in [
        ("", "anthill.reflect.SortView"),
        ("  sort SV = anthill.reflect.SortView\n", "SV"),
    ] {
        let extra = format!(
            "{decl}{}",
            file_store(&format!("provides Store[State = WIS]\n    provides {spec}"))
        );
        assert_refused_naming(
            &load_errors(&program(&extra, PEEK)),
            &[
                "`provides anthill.reflect.SortView` cannot hold",
                "DATA sort",
            ],
            &format!("provides {spec}"),
        );
    }
}

/// A bare provision names no carrier, qualified or not (WI-20260913-KXNEX). Was: qualified,
/// the carrier check asked about the bare `Store` and found no parameter to miss — the
/// clause loaded and ran.
#[test]
fn a_bare_provision_named_through_its_namespace_names_no_carrier() {
    let src = two_namespaces(&format!("provides qa.Store\n    {QA_PEEK}"));
    assert_refused_naming(
        &load_errors(&src),
        &["`provides qa.Store` in 't.FileStore' binds nothing"],
        "a bare qualified provision",
    );
}

/// Was: the `where` block resolved `Store` alone in `t`, and refused its own member as not
/// the spec's ("`Store` declares no operation `peek`").
#[test]
fn a_where_block_named_through_its_namespace_holds_the_spec_members() {
    let src = two_namespaces(&format!(
        "provides qa.Store[State = WIS] where\n      {QA_PEEK}\n    end"
    ));
    assert_eq!(run(&src), 9);
}

// ── a requirement ──────────────────────────────────────────────────────────────────────

/// An operation requiring the spec through `requirement`, beside the direct provision for
/// `WIS` — and none for `NoSp`. `WisStore` and `NoSpStore` fix `State` to each.
fn requiring_op(requirement: &str, body: &str) -> String {
    format!(
        "{}\n  sort WisStore = Store[State = WIS]\n  sort NoSpStore = Store[State = NoSp]\n  \
         operation usePeek[P](s: P) -> Int64 requires {requirement} = {body}",
        file_store("provides Store[State = WIS]")
    )
}

/// Bracketed and positional through the bare alias. Was: refused — "missing `requires
/// Store[State = …]` on enclosing sort", never naming the alias.
#[test]
fn an_operation_requirement_through_an_alias_is_supplied() {
    for requirement in ["StoreAlias[State = P]", "StoreAlias[P]"] {
        let src = program(
            &requiring_op(requirement, "Store.peek(s)"),
            "usePeek(wis(n: 9))",
        );
        assert_eq!(run(&src), 9, "requires {requirement}");
    }
}

/// The control: the requirement named directly.
#[test]
fn an_operation_requirement_named_directly_is_supplied() {
    let src = program(
        &requiring_op("Store[State = P]", "Store.peek(s)"),
        "usePeek(wis(n: 9))",
    );
    assert_eq!(run(&src), 9);
}

/// A requirement is CHECKED at the call through an alias as directly: nothing provides
/// `Store` at `NoSp` — asked through the argument's type, or fixed by a BARE alias. Was: the
/// requirement was of the alias, and with no call on `Store` in the body nothing read it —
/// the call ran.
#[test]
fn an_operation_requirement_through_an_alias_is_checked_at_the_call() {
    for requirement in [
        "Store[State = P]",
        "Store[State = NoSp]",
        "StoreAlias[State = P]",
        "NoSpStore",
    ] {
        let src = program(&requiring_op(requirement, "1"), "usePeek(nosp(n: 1))");
        assert_refused_naming(
            &load_errors(&src),
            &["expected a requirement suppliable at this call site"],
            &format!("an unmet `requires {requirement}`"),
        );
    }
}

/// A BARE alias carrying bindings is the whole requirement — `Store` at `WIS`, which
/// `FileStore` provides — so the call is supplied. PASSES EITHER WAY: before, the bare name
/// stayed the alias and the requirement went unchecked, so the call ran too; the row above
/// is the half that measures the change, the same spelling at `NoSp` refused.
#[test]
fn a_bare_alias_requirement_is_supplied_where_it_holds() {
    let src = program(&requiring_op("WisStore", "1"), "usePeek(wis(n: 9))");
    assert_eq!(run(&src), 1);
}

/// A sort requiring the spec at its own parameter, and an operation of it that calls the
/// spec's operation on that parameter.
fn requiring_sort(requirement: &str) -> String {
    format!(
        "{}\n  sort User\n    sort S = ?\n    {requirement}\n    \
         operation look(s: S) -> Int64 = Store.peek(s)\n  end",
        file_store("provides Store[State = WIS]")
    )
}

/// Plain and as a NAMED slot. Was: refused — "missing `requires Store[State = …]`" and
/// "expected a provider of StoreAlias".
#[test]
fn a_sort_requirement_through_an_alias_is_supplied() {
    for requirement in [
        "requires StoreAlias[State = S]",
        "requires O: StoreAlias[State = S]",
    ] {
        let src = program(&requiring_sort(requirement), "User.look(wis(n: 9))");
        assert_eq!(run(&src), 9, "{requirement}");
    }
}

/// The control: the sort requirement named directly.
#[test]
fn a_sort_requirement_named_directly_is_supplied() {
    let src = program(
        &requiring_sort("requires Store[State = S]"),
        "User.look(wis(n: 9))",
    );
    assert_eq!(run(&src), 9);
}

// ── a provision's condition ────────────────────────────────────────────────────────────

/// `Box[E = X]` provides `Store` exactly when `X` does — through `condition` — beside the
/// direct provision for `WIS`.
fn conditional(condition: &str) -> String {
    format!(
        "{}\n  sort Box\n    sort E = ?\n    sort ECond = Store[State = E]\n    \
         entity box(e: E)\n    provides Store[State = Box[E = E]] :- {condition}\n    \
         operation peek(s: Box[E = E]) -> Int64 = 100\n  end",
        file_store("provides Store[State = WIS]")
    )
}

/// The condition holds where its argument provides `Store`, and refuses the call where it
/// does not — through a bracketed alias, a bare alias fixing the parameter, and directly.
/// Was: through an alias the condition conditioned NOTHING — `Store.peek(box(e: nosp(n:
/// 1)))` ran to 100 although `NoSp` provides no `Store` — and the bare alias's variable
/// held nowhere.
#[test]
fn a_condition_through_an_alias_holds_and_binds() {
    for condition in ["Store[State = E]", "StoreAlias[State = E]", "ECond"] {
        let holds = program(&conditional(condition), "Store.peek(box(e: wis(n: 9)))");
        assert_eq!(run(&holds), 100, "`:- {condition}` where it holds");
        let fails = program(&conditional(condition), "Store.peek(box(e: nosp(n: 1)))");
        assert_refused_naming(
            &load_errors(&fails),
            &["no impl provides"],
            &format!("`:- {condition}` where it does not hold"),
        );
    }
}

// ── an alias a spec clause cannot read ─────────────────────────────────────────────────

/// A clause binding again what its alias fixes: a contradiction, not an override. Was:
/// loaded, about the alias.
#[test]
fn a_clause_rebinding_what_its_alias_fixes_is_refused() {
    let extra = format!(
        "  sort WisStore = Store[State = WIS]\n{}",
        file_store("provides WisStore[State = NoSp]")
    );
    assert_alias_refused(
        &load_errors(&program(&extra, "1")),
        "t.WisStore",
        &["already binds `State` to `WIS`, which the clause binds again"],
        "a clause re-binding an alias's parameter",
    );
}

/// A chain that comes back to itself stands for no type. Was: loaded, about the alias.
#[test]
fn a_cyclic_alias_is_refused_naming_its_chain() {
    let extra = format!(
        "  sort CA = CB\n  sort CB = CA\n{}",
        file_store("provides CA[State = WIS]")
    );
    assert_alias_refused(
        &load_errors(&program(&extra, "1")),
        "t.CA",
        &["its chain comes back to itself (t.CA = t.CB = t.CA)"],
        "a cyclic alias",
    );
}

/// … refused ONCE: the provision is not filed, so its `where` block's member is not
/// reported again as belonging to nothing. Was: one clause, then two diagnostics.
#[test]
fn a_where_block_over_a_refused_alias_reports_once() {
    let extra = "  sort CA = CB\n  sort CB = CA\n  sort FileStore\n    \
                 provides CA[State = WIS] where\n      \
                 operation peek(s: WIS) -> Int64 = s.n\n    end\n  end";
    let errs = load_errors(&program(extra, "1"));
    assert_alias_refused(&errs, "t.CA", &["comes back to itself"], "a cyclic alias");
    assert_eq!(errs.len(), 1, "the refusal alone: {errs:#?}");
}

/// … and a `default` mark over it is not refused a second time, as naming "no plain sort":
/// a refused alias files nothing, its mark included. Was: loaded, about the alias.
#[test]
fn a_default_mark_over_a_refused_alias_reports_once() {
    let extra = format!(
        "  sort CA = CB\n  sort CB = CA\n{}",
        file_store("default provides CA[State = WIS]")
    );
    let errs = load_errors(&program(&extra, "1"));
    assert_alias_refused(&errs, "t.CA", &["comes back to itself"], "a cyclic alias");
    assert_eq!(errs.len(), 1, "the refusal alone: {errs:#?}");
}

/// An alias of a tuple stands for no sort. Was: loaded, about the alias.
#[test]
fn an_alias_of_no_sort_is_refused() {
    let extra = format!(
        "  sort Tup = (Int64, Bool)\n{}",
        file_store("provides Store[State = WIS]\n    provides Tup")
    );
    assert_alias_refused(
        &load_errors(&program(&extra, "1")),
        "t.Tup",
        &["which is not a sort"],
        "an alias of a tuple",
    );
}

/// A name declared both as an alias and with members of its own has two readings, and a
/// clause does not pick one — not even the data-sort refusal, which would have read the
/// body. Kernel-language §5.2 records such a duplicate as loading.
#[test]
fn a_name_that_is_an_alias_and_more_is_refused() {
    let entry = format!(
        "  namespace StoreAlias\n    operation extra() -> Int64 = 1\n  end\n{}",
        file_store("provides StoreAlias[State = WIS]")
    );
    let body = format!(
        "  sort X\n    entity xe\n  end\n  sort X = WIS\n{}",
        file_store("provides Store[State = WIS]\n    provides X")
    );
    for (src, alias, what) in [
        (
            &entry,
            "t.StoreAlias",
            "an alias with a namespace entry at its address",
        ),
        (&body, "t.X", "a data sort declared as an alias too"),
    ] {
        let errs = load_errors(&program(src, PEEK));
        assert_alias_refused(
            &errs,
            alias,
            &["declared both as a type alias and with members of its own"],
            what,
        );
        assert!(
            !errs.iter().any(|e| e.contains("DATA sort")),
            "{what}: no reading is picked: {errs:#?}"
        );
    }
}

// ── a binding block ────────────────────────────────────────────────────────────────────

/// A binding block over `Stack`, spelled `spec`, whose `operation_map` realizes `Stack.size`.
fn binding_block(spec: &str) -> String {
    format!(
        r#"
namespace t
  import anthill.prelude.{{Int64}}
  sort Stack
    sort T = ?
    operation size(s: Stack) -> Int64 @[host_implemented]
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

/// A binding block does not read an alias — where its clauses land is decided at scan
/// time too, before any alias is known — and says so, naming the sort. Was: the block
/// loaded into the alias's empty scope and its `operation_map` was refused as naming
/// "`StackAlias.size`, which declares no operation `size`".
#[test]
fn a_binding_block_through_an_alias_is_refused() {
    assert_alias_refused(
        &load_errors(&binding_block("StackAlias")),
        "t.StackAlias",
        &["does not read an alias: write 't.Stack'"],
        "a binding block through an alias",
    );
}

/// The control: the block named directly loads.
#[test]
fn a_binding_block_named_directly_loads() {
    crate::common::expect_loaded(try_load_kb_with(&binding_block("Stack")));
}

// ── where an alias already meant its type ──────────────────────────────────────────────

/// An alias in a TYPE position — here a binding's value — was always the type it stands
/// for, and the provision is about `Store` at `WIS`.
#[test]
fn an_alias_in_a_binding_is_the_type_it_stands_for() {
    let extra = format!(
        "  sort WisAlias = WIS\n{}",
        file_store("provides Store[State = WisAlias]")
    );
    assert_eq!(run(&program(&extra, PEEK)), 9);
}
