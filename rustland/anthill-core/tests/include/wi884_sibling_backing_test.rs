//! WI-884 — the SIBLING AUDIT of WI-881: `Int64`'s bounds and `String`'s search/edit
//! surface are BACKED, and `string.anthill`'s six equations are settled one by one.
//!
//! THE PRE-FIX MEASUREMENT, taken by driving every operation the four primitive sorts
//! declare, before any change. Eight died `OperationBodyMissing { … }` on a program
//! that LOADED CLEAN — `Int64.minValue`/`maxValue`, and `String.isEmpty`/`contains`/
//! `indexOf`/`replace`/`trim`/`split` — and every other declared operation of `Int64`,
//! `String` and `BigInt` answered. That is WI-881's defect exactly: declared on the
//! sort, exempt from the load-time backing check because the carrier is a host
//! `Implementation.target` (WI-880), backed by nothing.
//!
//! `Bool` was outside WI-881's audit and is checked here: `and`/`or`/`not` answer, and
//! `ite` is not an operation — WI-887 deleted the declaration, leaving the functor its
//! two `[simp]` rules introduce. See
//! [`bool_is_audited_and_ite_is_not_one_of_its_operations`] and
//! [`ite_reduces_under_both_spellings`]; `bool.anthill` carries the why.
//!
//! TWO SEMANTICS DECISIONS carry the weight, and both are driven rather than argued:
//! [`index_of_agrees_with_substring_and_length`] pins the INDEX UNIT (the byte answer
//! the host primitive gives is a different, wrong function), and
//! [`split_keeps_its_empty_pieces_so_it_round_trips`] pins what the EMPTY pattern
//! means for the operations that return structure.
//!
//! STDLIB LOADS: TEN, which is the number of interpreters the trap discipline and the
//! per-claim naming actually force — `crate::common::interp_for` parses and loads all
//! ~76 stdlib and binding files each time (~0.5s), so this is the file's whole cost.
//! One per `#[test]` that drives `DRIVER`, plus one extra wherever a call is expected
//! to TRAP (a trapped call poisons every LATER call on that interpreter, so a trapping
//! call goes LAST and only a second trap needs a second interpreter). The rule and the
//! reason are `wi876_operation_mapping_test`'s `eval_all`; WI-881 recorded breaking it.
//!
//! Reference: `stdlib/anthill/prelude/{int64,string,bool}.anthill`,
//! `rustland/anthill-stl/anthill/{int64,string}.anthill` (`operation_map`), WI-881
//! (the same defect on `Float`, and the per-law settlement method), WI-876 (the
//! channel), WI-880 (the host-carrier exemption that hid all of these).

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId, Var};
use smallvec::SmallVec;

/// One driver sort per carrier, one entry per operation under test. Everything is
/// qualified so a call names the carrier's own member.
const DRIVER: &str = r#"
namespace wi884.siblings
  import anthill.prelude.{Int64, String, Bool, List}
  -- WI-894: `ite` is a rule-introduced functor SCOPED to `Bool`, so the
  -- `ite_reduces` rule below names it by an explicit import rather than by the
  -- bare global name it used to ride. Without this the load is REFUSED (measured:
  -- "unknown functor"), which is the point — the old globality failed silently.
  import anthill.prelude.Bool.{ite}

  sort I
    import anthill.prelude.{Int64, String, Bool}
    import anthill.prelude.Int64.{minValue, maxValue}
    operation dMinValue(n: Int64) -> Int64 = Int64.minValue()
    operation dMaxValue(n: Int64) -> Int64 = Int64.maxValue()
    -- the BARE nullary spelling, which `int64.anthill`'s own `in_bounds` constraint
    -- uses and which a `[simp]` equation would not have reached (WI-881 on `tau`)
    operation dMinBare(n: Int64) -> Int64 = minValue
    operation dMaxBare(n: Int64) -> Int64 = maxValue
  end

  sort S
    import anthill.prelude.{Int64, String, Bool, List}
    import anthill.prelude.Numeric.{add}
    operation dContains(s: String, sub: String) -> Bool = String.contains(s, sub)
    operation dIndexOf(s: String, sub: String) -> Int64 = String.indexOf(s, sub)
    operation dReplace(s: String, old: String) -> String = String.replace(s, old, "-")
    operation dTrim(s: String) -> String = String.trim(s)
    operation dSplit(s: String, sep: String) -> List[T = String] = String.split(s, sep)

    -- isEmpty in all three call forms; see `is_empty_reaches_every_call_form`.
    operation dEmptyQualified(s: String) -> Bool = String.isEmpty(s)
    operation dEmptyDot(s: String) -> Bool = s.isEmpty()
    operation dEmptyLiteralDot(n: Int64) -> Bool = "".isEmpty()

    -- THE AGREEMENT LAW between the three position-addressing operations:
    -- `substring(s, i, i + length(sub))` recovers `sub` when `i = indexOf(s, sub)`.
    -- False under a BYTE index for any `s` with a multi-byte prefix.
    operation dRoundTrip(s: String, sub: String) -> String =
      let i = String.indexOf(s, sub)
      String.substring(s, i, add(i, String.length(sub)))
  end

  sort B
    import anthill.prelude.{Int64, Bool}
    operation dAnd(n: Int64) -> Bool = Bool.and(true, false)
    operation dOr(n: Int64) -> Bool = Bool.or(true, false)
    operation dNot(n: Int64) -> Bool = Bool.not(true)
    -- no `ite`: it is not an operation, and `if`/`then`/`else` is the form here
  end

  -- `ite` at RULE level, where it does resolve, with a control that isolates the
  -- goal machinery from the functor under test.
  rule ite_reduces(?x)  :- holds(ite(true, 10, 20)), ?x = 1
  rule control_pred(?x) :- holds(10), ?x = 1
  fact holds(10)
end
"#;

/// `Int64`'s two bounds, in BOTH nullary call forms.
///
/// The bare spelling is not decoration: `int64.anthill`'s own
/// `constraint in_bounds: gte(?n, minValue), lte(?n, maxValue)` writes it that way,
/// and it is the form a `[simp]` equation would have left dead — a `[simp]` head is
/// an APPLICATION, so it matches `minValue()` and not the `var_ref` a bare name
/// lowers to (WI-881 measured that on `Float.tau`, which is why these are host-backed).
#[test]
fn int64_bounds_answer_in_both_nullary_call_forms() {
    let mut interp = crate::common::interp_for(DRIVER);
    for (entry, want) in [
        ("wi884.siblings.I.dMinValue", i64::MIN),
        ("wi884.siblings.I.dMaxValue", i64::MAX),
        ("wi884.siblings.I.dMinBare", i64::MIN),
        ("wi884.siblings.I.dMaxBare", i64::MAX),
    ] {
        match interp.call(entry, &[Value::Int(0)]) {
            Ok(Value::Int(n)) => assert_eq!(n, want, "{entry}"),
            other => panic!("call {entry}: expected an Int64, got {other:?}"),
        }
    }
}

type Interp = anthill_core::eval::Interpreter;

/// Call a `sort S` entry with `String` arguments. Every one of them succeeds — the
/// calls expected to TRAP are matched explicitly, on their own interpreter.
///
/// `Value` has no `PartialEq`, so the three typed wrappers below unwrap to the Rust
/// scalar through the `Value` accessor and the assertion compares those. That also
/// makes a wrong-CARRIER answer (a `Bool` where an `Int64` was declared) a named
/// failure rather than a silent inequality.
fn call_s(interp: &mut Interp, entry: &str, args: &[&str]) -> Value {
    let vals: Vec<Value> = args.iter().map(|s| Value::Str((*s).to_string())).collect();
    interp
        .call(&format!("wi884.siblings.S.{entry}"), &vals)
        .unwrap_or_else(|e| panic!("call {entry}{args:?}: {e:?}"))
}
fn call_bool(interp: &mut Interp, entry: &str, args: &[&str]) -> bool {
    let v = call_s(interp, entry, args);
    v.as_bool().unwrap_or_else(|| panic!("{entry}{args:?}: expected a Bool, got {v:?}"))
}
fn call_int(interp: &mut Interp, entry: &str, args: &[&str]) -> i64 {
    let v = call_s(interp, entry, args);
    v.as_int().unwrap_or_else(|| panic!("{entry}{args:?}: expected an Int64, got {v:?}"))
}
fn call_str(interp: &mut Interp, entry: &str, args: &[&str]) -> String {
    let v = call_s(interp, entry, args);
    v.as_str().unwrap_or_else(|| panic!("{entry}{args:?}: expected a String, got {v:?}")).to_string()
}

/// The headline: the five host-backed `String` operations run. Each answered
/// `OperationBodyMissing` before this ticket.
#[test]
fn the_string_search_and_edit_surface_evaluates() {
    let mut interp = crate::common::interp_for(DRIVER);
    for (args, want) in [
        (["abc", "b"], true),
        (["abc", "z"], false),
        // the empty pattern, which this sort's own law already fixes at `true`
        (["abc", ""], true),
    ] {
        assert_eq!(
            call_bool(&mut interp, "dContains", &args),
            want,
            "contains{args:?}"
        );
    }
    for (args, want) in [(["abc", "b"], 1), (["abc", "z"], -1), (["abc", ""], 0)] {
        assert_eq!(
            call_int(&mut interp, "dIndexOf", &args),
            want,
            "indexOf{args:?}"
        );
    }
    for (args, want) in [
        (["abcb", "b"], "a-c-"),   // EVERY occurrence, not the first
        (["aaa", "aa"], "-a"),     // non-overlapping, scanned LEFT TO RIGHT
        (["abc", ""], "-a-b-c-"),  // the empty pattern occurs at every boundary
    ] {
        assert_eq!(
            call_str(&mut interp, "dReplace", &args),
            want,
            "replace{args:?}"
        );
    }
    for (arg, want) in [
        (" \t\n a \n", "a"),
        ("ab", "ab"),
        // UNICODE whitespace, not the ASCII subset: U+00A0 NO-BREAK SPACE.
        ("\u{00a0}a\u{00a0}", "a"),
    ] {
        assert_eq!(
            call_str(&mut interp, "dTrim", &[arg]),
            want,
            "trim({arg:?})"
        );
    }
}

/// THE INDEX UNIT, settled by the round trip rather than by argument.
///
/// `length` counts Unicode scalars and `substring` slices by them; the host primitive
/// behind `indexOf` answers in BYTES. Under a byte answer this test fails on the very
/// first non-ASCII case — `indexOf("éb", "b")` would be 2, and `substring("éb", 2, 3)`
/// is the empty string, not `"b"`. The ASCII rows are the control that shows the
/// harness itself is sound (a byte index passes those).
#[test]
fn index_of_agrees_with_substring_and_length() {
    let mut interp = crate::common::interp_for(DRIVER);
    for (s, sub) in [
        ("abc", "b"),
        ("abcdef", "cde"),
        ("éb", "b"),          // one multi-byte scalar before the match
        ("ééb", "b"),         // two
        ("日本語text", "text"), // three, and a wider one
        ("日本語", "本"),
    ] {
        assert_eq!(
            call_str(&mut interp, "dRoundTrip", &[s, sub]),
            sub,
            "substring(s, indexOf(s, sub), +length(sub)) must recover sub for \
             ({s:?}, {sub:?}) — a BYTE index would not"
        );
    }
    // And the index itself is the CHARACTER count of the prefix, which is what the
    // round trip depends on: `"éb".find("b")` is 2 bytes and 1 character.
    assert_eq!(
        call_int(&mut interp, "dIndexOf", &["éb", "b"]),
        1,
        "indexOf answers in Unicode scalars, not bytes",
    );
}

/// `split` BUILDS a `List[T = String]` — the one host function here that returns
/// structure rather than a scalar — and KEEPS its empty pieces.
///
/// The empty pieces are what make the operation invertible: rejoining the result with
/// `sep` reproduces `s` for every row below, the three degenerate ones included.
/// Dropping the empty ends (which is what "split, but tidy" would do) breaks that on
/// `""`, on a leading/trailing separator, and on the empty separator alike — so the
/// round trip is asserted, not just the piece list.
#[test]
fn split_keeps_its_empty_pieces_so_it_round_trips() {
    let mut interp = crate::common::interp_for(DRIVER);
    for (s, sep, want) in [
        ("a,b,c", ",", vec!["a", "b", "c"]),
        (",a,", ",", vec!["", "a", ""]),
        ("", ",", vec![""]),
        ("abc", ",", vec!["abc"]),
        ("a::b", "::", vec!["a", "b"]),
        // the empty separator: every boundary, both ends included
        ("abc", "", vec!["", "a", "b", "c", ""]),
    ] {
        let got = call_s(&mut interp, "dSplit", &[s, sep]);
        let pieces: Vec<String> = crate::common::list_heads(&got)
            .into_iter()
            .map(|v| v.as_str().expect("a split piece is a String").to_string())
            .collect();
        assert_eq!(pieces, want, "split({s:?}, {sep:?})");
        assert_eq!(pieces.join(sep), s, "split({s:?}, {sep:?}) must round-trip");
    }
}

/// `isEmpty` in all three call forms — qualified, dot on a bound parameter, dot on a
/// literal. Written when `isEmpty` was `[simp]`-backed, where every spelling had to be
/// driven because INLINING IS NOT DISPATCH (this is the test `Float.tau` failed); kept
/// now that it is host-backed, as the guard that no form lost its answer in the move.
#[test]
fn is_empty_reaches_every_call_form() {
    let mut interp = crate::common::interp_for(DRIVER);
    for entry in ["dEmptyQualified", "dEmptyDot"] {
        assert!(call_bool(&mut interp, entry, &[""]), "{entry}(\"\")");
        assert!(!call_bool(&mut interp, entry, &["ab"]), "{entry}(\"ab\")");
    }
    match interp.call("wi884.siblings.S.dEmptyLiteralDot", &[Value::Int(0)]) {
        Ok(Value::Bool(true)) => {}
        other => panic!("\"\".isEmpty() must answer true; got {other:?}"),
    }
}

/// `Bool` — the sort WI-881's audit did not reach. All three of its operations answer,
/// and `ite` reduces at SLD, which is the one position it has.
///
/// Driven in one test because a stdlib load is ~0.5s and the `ite` half needs a KB
/// anyway. `and`/`or`/`not` are also driven by `wi529_boolean_operator_split_test`;
/// they are here so the audit's own record is complete rather than split across a
/// suite that is about something else.
///
/// THE SLD ARM NEEDS BOTH HALVES OF ITS SETUP, and WI-887 got there by having each
/// half wrong in turn. (1) The redex must be nested in a COMPOUND goal: under the `eq`
/// builtin it never reduces, because `eq` short-circuits ahead of the rule-candidate
/// path that hosts the rewrite — that shape yields zero for any `[simp]` redex, and
/// reading its zero as a fact about `ite` is what sent WI-884 looking for a missing
/// implementation. (2) It needs `ResolveConfig.simplify`, which is NOT the default
/// (`resolve.rs` sets `simplify: false`), so the same goal yields zero under
/// `ResolveConfig::default()` for a reason that has nothing to do with `ite` either.
/// Both configs are driven below so neither cause can masquerade as the other.
#[test]
fn bool_is_audited_and_ite_is_not_one_of_its_operations() {
    // The SLD half FIRST, off a KB this test then hands to the interpreter — one
    // stdlib load serves both halves.
    let mut kb = crate::common::load_kb_with(DRIVER);
    {
        let mut solutions = |goal: &str, simplify: bool| {
            let sym = kb.try_resolve_symbol(goal).unwrap_or_else(|| panic!("{goal} not in KB"));
            let name = kb.intern("X");
            let vid = kb.fresh_var(name);
            let v: TermId = kb.alloc(Term::Var(Var::Global(vid)));
            let g = kb.alloc(Term::Fn {
                functor: sym,
                pos_args: SmallVec::from_slice(&[v]),
                named_args: SmallVec::new(),
            });
            kb.resolve(&[g], &ResolveConfig { simplify, ..Default::default() }).len()
        };
        for (goal, simplify, want, why) in [
            ("control_pred", false, 1, "the control must answer, or nothing below proves anything"),
            ("ite_reduces", true, 1, "a nested redex rewrites once `simplify` is on"),
            ("ite_reduces", false, 0, "`simplify` is off by default, so no equation fires"),
        ] {
            let qn = format!("wi884.siblings.{goal}");
            assert_eq!(solutions(&qn, simplify), want, "{goal} (simplify={simplify}): {why}");
        }
    }

    let mut interp = Interp::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    for (entry, want) in [
        ("wi884.siblings.B.dAnd", false),
        ("wi884.siblings.B.dOr", true),
        ("wi884.siblings.B.dNot", false),
    ] {
        match interp.call(entry, &[Value::Int(0)]) {
            Ok(Value::Bool(b)) => assert_eq!(b, want, "{entry}"),
            other => panic!("call {entry}: expected a Bool, got {other:?}"),
        }
    }
}

/// `ite` IS NOT AN OPERATION — the half of WI-887's decision that a reducing rule
/// cannot show. It reduces because two `[simp]` rule heads DEFINE it, and the typer's
/// `[simp]` pass inlines it before dispatch, even in an operation body.
///
/// THE TWO SPELLINGS NO LONGER DIVERGE, and that reversal is WI-894. This test used to
/// assert that `Bool.ite(...)` "names nothing — a rule head introduces a functor, not a
/// qualified operation symbol", and that was true only because a rule-introduced functor
/// was ONE BARE GLOBAL NAME with no qualified identity to name. WI-894 scopes it to its
/// declaring sort, so `anthill.prelude.Bool.ite` now EXISTS and both spellings reach the
/// same symbol and the same `[simp]` rules. The member arm is kept, inverted: it is the
/// regression guard for the naming path this ticket added.
///
/// The un-imported REFUSAL — the negative control that makes the scoping safe — lives in
/// `wi894_rule_functor_scope_test`, which owns that claim; this file drives the positive
/// twin only.
///
/// An earlier cut of this test asserted BOTH spellings were refused. That was written
/// off a program in which a comment line above `ite_true` had silently eaten its
/// `[simp]` (WI-893), leaving the bare form genuinely dead — half-backed looking
/// backed, from the parser.
///
/// ONE LOAD serves both spellings: neither call traps, so both sorts ride one source and
/// one interpreter.
#[test]
fn ite_reduces_under_both_spellings() {
    const SPELLINGS: &str = r#"
namespace wi887.spellings
  import anthill.prelude.{Int64, Bool}
  sort R
    import anthill.prelude.{Int64, Bool}
    import anthill.prelude.Bool.{ite}
    operation viaBare(n: Int64) -> Int64 = ite(true, 1, 2)
  end
  -- WI-894: the qualified spelling resolves to the same scoped symbol, so it inlines
  -- identically — no import needed, since the name is written out in full.
  sort Q
    import anthill.prelude.{Int64, Bool}
    operation viaMember(n: Int64) -> Int64 = Bool.ite(true, 1, 2)
  end
end
"#;
    let mut interp = crate::common::interp_for(SPELLINGS);
    for (entry, why) in [
        ("R.viaBare", "an imported bare `ite` must inline to its then-branch"),
        ("Q.viaMember", "`Bool.ite` must name the scoped rule functor and inline"),
    ] {
        let path = format!("wi887.spellings.{entry}");
        match interp.call(&path, &[Value::Int(0)]) {
            Ok(Value::Int(1)) => {}
            other => panic!("{why}; got {other:?}"),
        }
    }
}

/// THE LIMIT OF A REWRITE, driven rather than argued: a `[simp]` head is matched
/// STRUCTURALLY, so `ite(true, ?t, ?_)` has a redex only where the condition is
/// already a LITERAL. `mixed` below is the other case — a computed condition, the
/// shape `ordered.anthill`'s own `max` law writes — and it does not reduce.
///
/// WI-887 accepted that limit. It costs nothing because no shipped use wants the
/// reduction: smt-gen lowers the functor to SMT-LIB `(ite c t e)` with the condition
/// left SYMBOLIC, and the stdlib's two spellings are specification.
#[test]
fn a_simp_ite_reaches_only_a_literal_condition() {
    const CONTROL: &str = r#"
namespace wi884.iteLaw
  import anthill.prelude.{Int64, Bool}

  sort C
    import anthill.prelude.{Int64, Bool}
    operation myIte(cond: Bool, then: Int64, else: Int64) -> Int64
    rule myIte(true, ?t, ?_) <=> ?t [simp]
    rule myIte(false, ?_, ?e) <=> ?e [simp]

    operation literal(n: Int64) -> Int64 = myIte(true, 10, 20)
    operation mixed(a: Int64, b: Int64) -> Int64 = myIte(Int64.gte(a, b), 10, 20)
  end
end
"#;
    let mut interp = crate::common::interp_for(CONTROL);
    match interp.call("wi884.iteLaw.C.literal", &[Value::Int(0)]) {
        Ok(Value::Int(10)) => {}
        other => panic!("a literal condition must inline; got {other:?}"),
    }
    // Same interpreter: a trap poisons every LATER call, and this is the last one.
    match interp.call("wi884.iteLaw.C.mixed", &[Value::Int(2), Value::Int(1)]) {
        Err(anthill_core::eval::EvalError::OperationBodyMissing { name, .. }) => {
            assert_eq!(name, "wi884.iteLaw.C.myIte")
        }
        other => panic!("a computed condition has no redex to inline; got {other:?}"),
    }
}

/// THE FIRST DIAGNOSIS OF `ite` WAS WRONG, and this is what refuted it.
///
/// `bool.anthill`'s case laws are written `ite_true: ite(true, ?t, ?_) = ?t`, and the
/// spec says an equational rule's head connective is `<=>` and NOT `=` — "`=` is a
/// semantic equality *test* that never binds" (kernel-language.md §5.3). That reads
/// like the explanation for [`ite_does_not_reduce_at_sld_either`], and it was written
/// down as one before being driven. It is false: the four rows below vary the
/// connective and the attribute independently, and the ANSWER TRACKS THE ATTRIBUTE
/// ALONE. `=` with `[simp]` fires; `<=>` without it is dead.
///
/// The implementation is not ambiguous about this once located — `is_equational_head`
/// (kb/load.rs) classifies through `is_equality_connective_functor`, which matches the
/// `eq` symbol OR the `unify` symbol, i.e. both spellings. So the spec states a
/// distinction the loader does not make, and a reader who trusts §5.3 will
/// misdiagnose exactly as this ticket did. That divergence is WI-888; this test is
/// what pins today's behaviour so the fix has to choose a side rather than drift.
///
/// It also re-states WI-881's headline in a second file: `[simp]` IS THE ENABLEMENT,
/// not the direction. Every untagged equation in the stdlib is inert, whichever
/// connective it is spelled with.
#[test]
fn the_head_connective_is_not_what_enables_an_equation() {
    const ROWS: [(&str, &str, &str, Option<i64>); 4] = [
        ("eqSimp", "=", " [simp]", Some(10)),
        ("unifySimp", "<=>", " [simp]", Some(10)),
        ("eqBare", "=", "", None),
        ("unifyBare", "<=>", "", None),
    ];
    // All four namespaces in ONE source, so the whole matrix costs two stdlib loads
    // rather than four: the two firing rows and the FIRST trapping row share an
    // interpreter (a trap poisons only LATER calls), and the last row gets a fresh one.
    let src: String = ROWS
        .iter()
        .map(|(ns, connective, attribute, _)| {
            format!(
                r#"
namespace wi884.{ns}
  import anthill.prelude.{{Int64, Bool}}
  sort C
    import anthill.prelude.{{Int64, Bool}}
    operation pick(cond: Bool, then: Int64, else: Int64) -> Int64
    rule pick(true, ?t, ?_) {connective} ?t{attribute}
    rule pick(false, ?_, ?e) {connective} ?e{attribute}
    operation drive(n: Int64) -> Int64 = pick(true, 10, 20)
  end
end
"#
            )
        })
        .collect();

    let mut interp = crate::common::interp_for(&src);
    for (i, (ns, connective, attribute, expected)) in ROWS.iter().enumerate() {
        // The last row also traps, so it needs an interpreter the third row has not
        // poisoned.
        if i == ROWS.len() - 1 {
            interp = crate::common::interp_for(&src);
        }
        let got = interp.call(&format!("wi884.{ns}.C.drive"), &[Value::Int(0)]);
        let label =
            format!("`{connective}`{}", if attribute.is_empty() { " bare" } else { " [simp]" });
        match (expected, got) {
            (Some(want), Ok(Value::Int(n))) => assert_eq!(n, *want, "{label}"),
            (None, Err(anthill_core::eval::EvalError::OperationBodyMissing { name, .. })) => {
                assert_eq!(name, format!("wi884.{ns}.C.pick"), "{label}")
            }
            (_, other) => panic!(
                "{label}: expected {}, got {other:?}",
                match expected {
                    Some(n) => n.to_string(),
                    None => "OperationBodyMissing".to_string(),
                }
            ),
        }
    }
}
