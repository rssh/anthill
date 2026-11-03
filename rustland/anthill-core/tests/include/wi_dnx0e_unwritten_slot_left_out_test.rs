//! WI-20261020-DNX0E — A SLOT A CLAUSE LEAVES UNWRITTEN IS LEFT OUT OF IT, IN EVERY CLAUSE
//! KIND, SO A CLAUSE THAT NAMES ITS OWN SORT AT ITS OWN PARAMETER IS THAT SORT THERE.
//!
//! A slot a requirement leaves unwritten, or writes `?`, is any binding of it
//! (kernel-language §8.1). The loader held it as the required sort's own parameter in a sort's
//! `requires` (`Pairish[A = T]` stored `Pairish[A = T, B = Pairish.B]`) and as no binding in an
//! operation's `requires` and in a provision's condition, and the readers took the own
//! parameter for the open slot. That is also the term a clause written inside the sort at its
//! own parameter makes — `Mark[T = T]` inside `Mark` is `Mark[T = Mark.T]` — so such a clause
//! read as the sort at any type, and a condition leaving a slot unwritten had nothing open.
//! Now an unwritten slot is no binding in every clause kind, and only that is open
//! (`unwritten_requires_slots`).
//!
//! Measured on the parent (89500f50): (a) `tagAt[P = Int64]` ran to 5 through `Mark provides
//! Tag[T = T] :- Mark[T = T]` with no `Mark[T = Int64]` anywhere, and beside a second provider
//! of `Mark` the call was refused as naming `T` apart; (b) the contract `Named[T = Named.T]` of
//! `Named provides Shows[T = T]` was covered by the condition `Named[T = Foo]`; (c)
//! `Shows.show(dog)` through `:- Pairish[A = T]` was refused "unresolved: Pairish[A = Dog]",
//! and through `:- Pairish[A = T, B = ?]` too.
//!
//! ## What else leaving the slot out took
//!
//! A sort's clause now holds an unwritten member as an operation's always did, so what held
//! for an operation's alone holds for both:
//!
//! - **The member is the instance's unknown (WI-20261006-GVGSQ)**, at a body's call of the
//!   spec's own operation (`scope_clause_at_carrier`), now under a sort's clause too: returned
//!   as an `Int64`, given an `Int64`, given another carrier's `Key` — each refused, where the
//!   parent loaded them on a sort. And that unknown IS the projection the signature writes
//!   for it (`MintedParam::Member`'s `at`, read by the ζ arm): `-> P.Val = Storage.get(x, k)`
//!   loads, for an operation's clause too, which the parent refused.
//! - **Another declaration's clause is its own instance (`OmittedMembers::Unread`).** Read at
//!   the scope's carrier, it takes no member the scope's clause leaves open: `Callee.c(x,
//!   pebble())` inside `requires Pair[P = MT]` runs through `AnyPebble`, for an operation's
//!   clause too, which the parent refused.
//! - **A goal says which of its absent slots are open (`SortGoal::left_open`).** A slot a
//!   CALL's goal leaves out is one the call did not determine, which no scope entry decides
//!   (WI-826 leg 2); one a REQUIREMENT leaves open is any type, which a scope entry writing it
//!   covers (QGVB1). The placeholder told the two apart; now the goal does.
//!
//! ## Back-outs, one at a time
//!
//! Measured over this file and the suites the change reads through — `wi_qgvb1`, `wi826`,
//! `wi_gvgsq`, `wi841`, `wi_a3nnd`, `provision_written_through_alias`, `wi_0rp29_review9`,
//! `wi_sg16k` (199 rows).
//!
//! 1. **The loader fills an unwritten parameter with the spec's own again**
//!    (`resolve_requires_bindings`): 21 fail — the four rows here that read a slot left open,
//!    13 of `wi_qgvb1`, `wi826`'s partially-bound row, and the alias, review-9 and seal rows.
//! 2. **A binding at the spec's own parameter read as open too** (`requirement_goal`): 1 fails
//!    — `a_condition_naming_its_own_sort_…` (a).
//! 3. **No slot left out held open** (`requirement_goal`'s `left_open`): 19 fail — the three
//!    condition and member rows here, 13 of `wi_qgvb1`, and the alias, review-9 and seal rows.
//! 4. **The cover walk skipping a demand at the spec's own parameter**
//!    (`supply_covers_demanded_keys`): 1 fails — `a_contract_at_the_providers_own_…` (b).
//! 5. **A `?` in a condition kept** (`without_written_wildcards`): 2 fail — the two condition
//!    rows (c).
//! 6. **No ζ identity of a projection and the instance's member**
//!    (`projection_is_instance_member`): 4 fail — `a_member_a_clause_leaves_unwritten_…` and
//!    three of `wi_qgvb1`.
//! 7. **Another declaration's clause reading the scope instance's member**
//!    (`OmittedMembers::Unread` → `OfTheInstance`): 3 fail — `another_declarations_…`, `wi826`'s
//!    partially-bound row, and `wi_qgvb1`'s `an_open_slot_of_the_callers_requirement_…`.
//! 8. **Leg 2 ignoring what the goal holds open** (`requires_entry_covers_goal`): 1 fails —
//!    `wi_qgvb1`'s `a_parametric_carrier_whose_own_requirement_…`.
//! 9. **A goal built from a sort-shaped entry holding nothing open**
//!    (`goal_from_requires_entry`): 1 fails — `wi_qgvb1`'s `two_provisions_naming_an_open_slot_
//!    apart_are_refused_at_a_call`.
//! 10. **A projection saying every open slot, not its member alone**
//!     (`member_through_lending_requirement`): 1 fails — `a_projection_reads_its_member_…`.
//! 11. **The open-slot search discriminating on the held-open slots it does not ask**
//!     (`open_slots_said`): 11 fail — the member and projection rows here, 7 of `wi_qgvb1`, and
//!     the alias and review-9 rows.
//!
//! FAIL NO ROW, measured together over the whole `anthill-core` crate as well (10,562 passed,
//! 0 failed): `left_open` set by an operation's entry goal (`goal_from_op_requires_entry`), by
//! `dep_completed_at_carrier`'s `asked` and kept by `goal_completed_by_provisions` — no reader
//! reads it there, it is kept so the field means one thing at every producer; the tie account
//! reading `left_open` and not every absent key (`OpenSlotsNamedApart::of`) — a call's tie is
//! reported in the bracket's words at the dispatch either way (measured with the CLI); a
//! requirement writing no parameter leaving nothing open (`unwritten_requires_slots`) — the
//! parent's reading of a bare `requires Desc`, which nothing here distinguishes; an
//! operation's parameter matched through its bracket and not by qualified name (the ζ arm) —
//! it takes a value of a sort's parameter inside an operation whose own bracket shadows it;
//! a completed goal's binding order (`complete_open_slots_at_carrier`) — no verdict reads it,
//! the goal's `Eq`/`Hash` do; minted carriers excluded (`declared_carrier_param`) — no
//! projection off one resolves.
//!
//! Pass under every back-out, by design: the refused twins of (a), (b) and (c) — the same
//! clause on another sort, the contract on another spec, a carrier with no `Pairish` — and
//! the instance's own `Key` passed back to it.

use crate::common::{assert_refused_naming, interp_for, load_errors_of, run_int64};
use anthill_core::eval::Value;

/// `src` loads with no refusal.
#[track_caller]
fn assert_loads(src: &str, why: &str) {
    let errs = load_errors_of(src);
    assert!(errs.is_empty(), "{why} should load: {errs:#?}");
}

/// `src` is refused once, naming `expected` ([`assert_refused_naming`]).
#[track_caller]
fn assert_refused(src: &str, expected: &str, why: &str) {
    let errs = load_errors_of(src);
    assert_eq!(errs.len(), 1, "{why}: one refusal: {errs:#?}");
    assert_refused_naming(&errs, &[expected], why);
}

/// `Tag` provided through a condition on `Mark`, written on `owner` (`Mark` itself, or
/// `MarkTag`, a sort of its own), beside `Boom`, which provides `Mark` at `Boom` alone, and
/// `extra`. `main` asks `Tag[T = Int64]`.
fn mark_program(ns: &str, owner: &str, extra: &str) -> String {
    let provision = "provides Tag[T = T] :- Mark[T = T] where
      operation tag() -> Int64 = 5
    end";
    let (in_mark, in_mark_tag) = if owner == "Mark" { (provision, "") } else { ("", provision) };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.Int64
  sort Tag
    sort T = ?
    operation tag() -> Int64
  end
  sort Mark
    sort T = ?
    operation mark() -> Int64
    {in_mark}
  end
  sort MarkTag
    sort T = ?
    {in_mark_tag}
  end
  sort Boom
    provides Mark[T = Boom] where
      operation mark() -> Int64 = 1
    end
  end
  {extra}
  operation tagAt[P](n: Int64) -> Int64 requires Tag[T = P] = Tag.tag[T = P]()
  operation main() -> Int64 = tagAt[P = Int64](0)
end
"#
    )
}

/// (a) A condition naming its own sort at its own parameter is that sort at the provision's
/// binding, as the same condition written on another sort is: refused where nothing provides
/// `Mark[T = Int64]`, and run to 5 where `IntMark` does. The parent ran the refused program
/// on `Mark` to 5, and refused the running one there (`Boom` and `IntMark` "naming different
/// types" for `T`); the `MarkTag` rows had these verdicts on the parent too.
#[test]
fn a_condition_naming_its_own_sort_at_its_own_parameter_is_that_sort_there() {
    let int_mark = "sort IntMark
    provides Mark[T = Int64] where
      operation mark() -> Int64 = 2
    end
  end";
    for owner in ["Mark", "MarkTag"] {
        let ns = format!("wi_dnx0e.own.{}", owner.to_lowercase());
        assert_refused(
            &mark_program(&ns, owner, ""),
            &format!("`{ns}.Mark[T = anthill.prelude.Int64]` beneath it does not hold"),
            &format!("the condition on `{owner}` where nothing provides `Mark[T = Int64]`"),
        );
        let ns = format!("{ns}.held");
        assert_eq!(
            run_int64(&mark_program(&ns, owner, int_mark), &format!("{ns}.main")),
            Ok(5),
            "the condition on `{owner}` where `IntMark` provides `Mark[T = Int64]`",
        );
    }
}

/// `Named provides Shows[T = T] :- {condition}`, where `Shows requires {required}[T = T]`.
fn contract_program(ns: &str, required: &str, condition: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.String
  sort Foo
    entity foo
  end
  sort Other
    sort T = ?
    operation other(x: T) -> String
  end
  sort Shows
    sort T = ?
    requires {required}[T = T]
    operation show(x: T) -> String
  end
  sort Named
    sort T = ?
    operation name(x: T) -> String
    provides Shows[T = T] :- {condition} where
      operation show(x: T) -> String = "s"
    end
  end
end
"#
    )
}

/// (b) The contract a provision owes at the provider's own parameter, `Named[T = Named.T]`, is
/// owed at that parameter: a condition at `Foo` does not cover it, and the provision is
/// refused as the same contract on `Other` is. The parent loaded the `Named` row clean.
/// CONTROL, by design the same on the parent: the condition `Named[T = T]` covers it.
#[test]
fn a_contract_at_the_providers_own_parameter_is_owed_there() {
    for required in ["Named", "Other"] {
        let ns = format!("wi_dnx0e.contract.{}", required.to_lowercase());
        assert_refused(
            &contract_program(&ns, required, "Named[T = Foo]"),
            &format!("nothing provides `{ns}.{required}[T = {ns}.Named.T]`"),
            &format!("the contract `{required}[T = Named.T]` beside the condition `Named[T = Foo]`"),
        );
    }
    assert_loads(
        &contract_program("wi_dnx0e.contract.own", "Named", "Named[T = T]"),
        "the contract `Named[T = Named.T]` beside the condition `Named[T = T]`",
    );
}

/// `Wrap` provides `Shows` under `bound` (a sort-level `requires`) and `condition` (its
/// `:- …` tail), each over `Pairish`, which `Dog` provides at `B = Int64`; and `extra`.
fn wrap_program(ns: &str, bound: &str, condition: &str, extra: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Shows
    sort T = ?
    operation show(x: T) -> String
  end
  sort Pairish
    sort A = ?
    sort B = ?
    operation pa(x: A) -> String
  end
  sort Wrap
    sort T = ?
    {bound}
    provides Shows[T = T] {condition} where
      operation show(x: T) -> String = Pairish.pa(x)
    end
  end
  sort Dog
    entity dog
    provides Pairish[A = Dog, B = Int64] where
      operation pa(x: Dog) -> String = "dog-pa"
    end
  end
  sort Cat
    entity cat
  end
  {extra}
  operation main() -> String = Shows.show(dog)
end
"#
    )
}

/// The three ways to write `Wrap`'s bound on `Pairish` at `A = T` alone: the sort-level
/// `requires`, which ran on the parent, and the two conditions, which were refused there.
const BOUNDS: [(&str, &str, &str); 3] = [
    ("requires", "requires Pairish[A = T]", ""),
    ("condition", "", ":- Pairish[A = T]"),
    ("wildcard", "", ":- Pairish[A = T, B = ?]"),
];

/// (c) A condition that leaves a slot unwritten — or writes `?` — is its spec at any binding of
/// it, said by the provision answering the rest, as the same bound written at sort level is:
/// `Shows.show(dog)` answers "dog-pa" each way.
#[test]
fn a_condition_leaving_a_slot_unwritten_is_its_spec_at_any_binding_of_it() {
    for (tag, bound, condition) in BOUNDS {
        let ns = format!("wi_dnx0e.open.{tag}");
        let mut interp = interp_for(&wrap_program(&ns, bound, condition, ""));
        match interp.call(&format!("{ns}.main"), &[]) {
            Ok(Value::Str(s)) => assert_eq!(s, "dog-pa", "{tag}"),
            other => panic!("{tag}: `main` should answer \"dog-pa\", got {other:?}"),
        }
    }
}

/// (c)'s refusals, each way to write the bound alike: a second provision of `Pairish` at `A =
/// Dog` naming `B` otherwise leaves the bound saying neither, and a carrier with no `Pairish`
/// meets none. On the parent the two conditions were refused here too, as matching no
/// provision.
#[test]
fn a_condition_leaving_a_slot_unwritten_is_refused_as_its_sort_level_twin() {
    let any_dog = "sort AnyDog
    provides Pairish[A = Dog, B = String] where
      operation pa(x: Dog) -> String = \"any\"
    end
  end";
    for (tag, bound, condition) in BOUNDS {
        let ns = format!("wi_dnx0e.apart.{tag}");
        assert_refused(
            &wrap_program(&ns, bound, condition, any_dog),
            &format!(
                "the requirement leaves `B` unwritten, and `{ns}.Dog` and `{ns}.AnyDog` answer \
                 `{ns}.Pairish[A = {ns}.Dog]` naming different types for it"
            ),
            &format!("{tag}: two provisions naming `B` apart"),
        );
    }
    for (tag, bound, condition) in BOUNDS {
        let ns = format!("wi_dnx0e.unprovided.{tag}");
        let src = wrap_program(&ns, bound, condition, "").replace(
            "operation main() -> String = Shows.show(dog)",
            "operation main() -> String = Shows.show(cat)",
        );
        assert_refused(
            &src,
            &format!("unresolved: {ns}.Pairish[A = {ns}.Cat] (no impl provides {ns}.Pairish"),
            &format!("{tag}: a carrier with no `Pairish`"),
        );
    }
}

// ── the member a clause leaves unwritten, now that a sort's clause leaves it out too ──────

/// `Storage`, provided at `MemStore`, beside `decl` — a declaration under a requirement of
/// `Storage` that writes its carrier alone — and `main`.
fn storage_program(ns: &str, decl: &str, main: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Storage
    sort C = ?
    sort Key = ?
    sort Val = ?
    operation get(s: C, k: Key) -> Val
    operation take(s: C, k: Key) -> Int64
    operation key(s: C) -> Key
  end
  sort MemStore
    entity memStore
    provides Storage[C = MemStore, Key = String, Val = Int64]
    operation get(s: MemStore, k: String) -> Int64 = 7
    operation take(s: MemStore, k: String) -> Int64 = 8
    operation key(s: MemStore) -> String = "k"
  end
{decl}
  operation main() -> Int64 = {main}
end
"#
    )
}

/// `body` under `requires Storage[C = P]` — and `Storage[C = Q]` beside it where `params`
/// names a `Q` — written on a sort `Sp` (as its operation `g`) and on the operation `g[P]`
/// itself. `params` are `g`'s parameters past `x: P`, `ret` its result.
fn both_clause_kinds(ns: &str, params: &str, ret: &str, body: &str) -> [(String, String); 2] {
    let two = params.contains(": Q");
    let (sort_q, sort_req_q, op_params, op_req_q) = if two {
        ("\n    sort Q = ?", "\n    requires Storage[C = Q]", "P, Q", ", Storage[C = Q]")
    } else {
        ("", "", "P", "")
    };
    [
        (
            format!("{ns}.sort"),
            format!(
                "  sort Sp\n    sort P = ?{sort_q}\n    requires Storage[C = P]{sort_req_q}\n    \
                 operation g(x: P{params}) -> {ret} = {body}\n  end"
            ),
        ),
        (
            format!("{ns}.op"),
            format!(
                "  operation g[{op_params}](x: P{params}) -> {ret} requires Storage[C = \
                 P]{op_req_q} = {body}"
            ),
        ),
    ]
}

/// The member a requirement leaves unwritten is the projection the signature writes for it:
/// `-> P.Val = Storage.get(x, k)` under `requires Storage[C = P]` loads, and runs to 7 at
/// `MemStore`, the requirement on the sort and on the operation alike. The parent refused the
/// operation's, "expected P.Val, got Storage[C = P].Val" (the member minted as an unknown of
/// its own); the sort's ran.
#[test]
fn a_member_a_clause_leaves_unwritten_is_the_projection_the_signature_writes() {
    for (ns, decl) in both_clause_kinds("wi_dnx0e.member", ", k: P.Key", "P.Val", "Storage.get(x, k)") {
        let call = if ns.ends_with(".sort") { "Sp.g" } else { "g" };
        let src = storage_program(&ns, &decl, &format!("{call}(memStore, \"k\") * 6"));
        assert_eq!(run_int64(&src, &format!("{ns}.main")), Ok(42), "{ns}");
    }
}

/// And it is that instance's unknown, conforming to no other type (WI-20261006-GVGSQ), on a
/// sort's requirement as on an operation's: returned as an `Int64`, given an `Int64`, given
/// the `Key` of the instance at another carrier — each refused. The parent loaded each on the
/// sort, the slot held as the spec's own parameter read past by the call; the operation's it
/// refused as here. CONTROL, by design the same on the parent: the instance's own `Key`
/// passed back to it runs to 8.
#[test]
fn a_member_a_sort_clause_leaves_unwritten_is_the_instances_as_an_operations_is() {
    let refused = [
        ("as_int", ", k: P.Key", "Int64", "Storage.get(x, k)", "expected Int64, got Storage[C = P].Val"),
        ("int_key", "", "Int64", "Storage.take(x, 5)", "expected Storage[C = P].Key, got Int64"),
        (
            "other_key",
            ", y: Q",
            "Int64",
            "Storage.take(x, Storage.key(y))",
            "expected Storage[C = P].Key, got Storage[C = Q].Key",
        ),
    ];
    for (tag, params, ret, body, refusal) in refused {
        for (ns, decl) in both_clause_kinds(&format!("wi_dnx0e.instance.{tag}"), params, ret, body) {
            assert_refused(&storage_program(&ns, &decl, "0"), refusal, &ns);
        }
    }
    for (ns, decl) in both_clause_kinds("wi_dnx0e.instance.own", "", "Int64", "Storage.take(x, Storage.key(x))") {
        let call = if ns.ends_with(".sort") { "Sp.g" } else { "g" };
        let src = storage_program(&ns, &decl, &format!("{call}(memStore)"));
        assert_eq!(run_int64(&src, &format!("{ns}.main")), Ok(8), "{ns}");
    }
}

/// Another declaration's requirement, asked at the scope's carrier, is an instance of its own,
/// which a provision may answer at a member the scope's requirement leaves open: inside
/// `requires Pair[P = MT]`, `Callee.c(x, pebble())` asks `Pair[P = MT, Q = Pebble]`, which
/// `AnyPebble` answers, and runs to 8 — on an operation's requirement as on a sort's
/// (`wi826_cover_walk_orientation_test::partially_bound_entry_leaves_the_omitted_param_open`).
/// The parent refused the operation's, "expected Pair[P = MT].Q, got Pebble", the member read
/// as the scope instance's.
#[test]
fn another_declarations_requirement_is_its_own_instance_at_a_member_left_open() {
    let src = r#"
namespace wi_dnx0e.callee
  import anthill.prelude.Int64
  sort Leaf
    entity leaf
  end
  sort Pebble
    entity pebble
  end
  sort Pair
    sort P = ?
    sort Q = ?
    operation pd(a: P, b: Q) -> Int64
  end
  sort AnyPebble
    sort X = ?
    provides Pair[P = X, Q = Pebble]
    operation pd(a: X, b: Pebble) -> Int64 = 8
  end
  sort Callee
    sort CP = ?
    sort CQ = ?
    requires Pair[P = CP, Q = CQ]
    operation c(a: CP, b: CQ) -> Int64 = Pair.pd(a, b)
  end
  operation p[MT](x: MT) -> Int64 requires Pair[P = MT] = Callee.c(x, pebble())
  operation main() -> Int64 = p(leaf)
end
"#;
    assert_eq!(run_int64(src, "wi_dnx0e.callee.main"), Ok(8));
}

/// A projection off an operation's parameter reads the member it names through the
/// requirement that lends it — where no provision OF the carrier does, so `Bag`'s come from
/// witnesses — whatever the provisions answering the requirement say of its OTHER slots:
/// `W1` provides `Storage` at `Bag` with `Key = String, Val = Int64`, and `AnyVal` at every
/// carrier with `Key = String, Val = Bool`, so at `X = Bag` the two say `Key` alike and name
/// `Val` apart. `X.Key` is `String`: `f(bag, "k")` runs to 1 (the dictionary is `W1`'s, the
/// more specific), and `f(bag, 5)` is refused at the argument. The parent refused both, "`X.Key`
/// does not read at this call": saying `Key` alone, it read the unwritten `Val` as a slot the
/// goal omits, which no provision matched.
#[test]
fn a_projection_reads_its_member_whatever_the_provisions_say_of_another() {
    let program = |ns: &str, key: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool}}
  sort Storage
    sort C = ?
    sort Key = ?
    sort Val = ?
    operation get(s: C, k: Key) -> Val
  end
  sort Bag
    entity bag
  end
  sort W1
    provides Storage[C = Bag, Key = String, Val = Int64] where
      operation get(s: Bag, k: String) -> Int64 = 7
    end
  end
  sort AnyVal
    sort X = ?
    provides Storage[C = X, Key = String, Val = Bool] where
      operation get(s: X, k: String) -> Bool = true
    end
  end
  operation f[X](x: X, k: X.Key) -> Int64 requires Storage[C = X] = 1
  operation main() -> Int64 = f(bag, {key})
end
"#
        )
    };
    assert_eq!(
        run_int64(&program("wi_dnx0e.lent.string", "\"k\""), "wi_dnx0e.lent.string.main"),
        Ok(1)
    );
    assert_refused(
        &program("wi_dnx0e.lent.int", "5"),
        "expected String, got Int64",
        "`X.Key` given an `Int64`",
    );
}
