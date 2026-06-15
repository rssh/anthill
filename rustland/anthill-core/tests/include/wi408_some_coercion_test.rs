//! WI-408 — some-coercion INSERTION pass: a value of type `T` flowing into
//! an `Option[T]` slot (entity field or operation argument) gets a
//! synthesized `some(...)` inserted, so the value is PROPERLY Option-typed
//! at runtime. Replaces WI-385's bare-`T`-vs-`Option[T]` FIELD lenient-accept
//! interim (under which the value stayed bare in memory) and lifts the
//! restriction that operation arguments stayed strict.
//!
//! Three legs:
//!  - TYPER (op bodies): `check_apply_iter` / `check_constructor_iter`
//!    record the coercion during WI-385 validation and reassemble the
//!    apply/constructor with a synthesized `some(child)` (WI-283 tree
//!    production; the root reaches the stored body via `set_op_body_node`).
//!  - LOADER (term world): `wrap_bare_option_value` wraps a bare value
//!    supplied for an Option-typed entity field at `convert_term` time —
//!    on-disk facts AND rule-body entity atoms, so a bare-list rule pattern
//!    keeps matching the now-wrapped facts.
//!  - A bare value at BOTH depths of a nested `Option[Option[T]]` is
//!    rejected loudly (one wrap is inserted, never a guessed double-wrap).

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::parse;

/// Call a nullary op and expect an Int result.
fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

fn make_var(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

// ── TYPER leg: entity FIELD in an op body ────────────────────────────────

/// THE acceptance shape: `Box(v: 5)` against `entity Box(v: Option[T =
/// Int64])` builds a runtime `some(5)` — the `some(x)` match arm fires and
/// reads 5 back out. Pre-WI-408 the interim accepted the field but left the
/// value BARE (the `some/none` match would have failed).
#[test]
fn field_bare_value_coerced_to_some_at_eval() {
    let src = r#"
namespace wi408.field
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{some, none}

  entity Box(v: Option[T = Int64])

  operation make_bare() -> Box = Box(v: 5)
  operation make_explicit() -> Box = Box(v: some(7))
  operation make_none() -> Box = Box(v: none())

  -- positional pattern: named constructor sub-patterns do not BIND in the
  -- typer env yet (pre-existing gap, filed separately)
  operation get(b: Box) -> Int64 =
    match b
      case Box(some(x)) -> x
      case Box(none()) -> 0 - 1

  operation t_bare() -> Int64 = get(make_bare())
  operation t_explicit() -> Int64 = get(make_explicit())
  operation t_none() -> Int64 = get(make_none())
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi408.field.t_bare"), 5, "bare field coerced to some(5)");
    assert_eq!(run_int(&mut interp, "wi408.field.t_explicit"), 7, "explicit some untouched");
    assert_eq!(run_int(&mut interp, "wi408.field.t_none"), -1, "explicit none untouched");
}

// ── TYPER leg: operation ARGUMENT ────────────────────────────────────────

/// Operation arguments were STRICT under WI-385 (no interim); WI-408 inserts
/// the coercion there too: `pick(42)` against `pick(o: Option[T = Int64])`
/// loads AND evaluates — the callee's `some(x)` arm sees `some(42)`.
#[test]
fn arg_bare_value_coerced_to_some_at_eval() {
    let src = r#"
namespace wi408.arg
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{some, none}

  operation pick(o: Option[T = Int64]) -> Int64 =
    match o
      case some(x) -> x
      case none() -> 0 - 1

  operation t_bare() -> Int64 = pick(42)
  operation t_explicit() -> Int64 = pick(some(11))
  operation t_none() -> Int64 = pick(none())
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "bare arg in Option param must load (coerced): {errs:?}");
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi408.arg.t_bare"), 42, "bare arg coerced to some(42)");
    assert_eq!(run_int(&mut interp, "wi408.arg.t_explicit"), 11);
    assert_eq!(run_int(&mut interp, "wi408.arg.t_none"), -1);
}

/// The reflect-Term inner type (`description`-shape): a bare String into an
/// `Option[T = Term]` field wraps and the payload rides the value→Term
/// reflection boundary.
#[test]
fn field_option_term_takes_bare_string() {
    let src = r#"
namespace wi408.term
  import anthill.prelude.{Int64, Option, String}
  import anthill.reflect.{Term}
  import anthill.prelude.Option.{some, none}

  entity Note(text: Option[T = Term])

  operation make() -> Note = Note(text: "hello")
  operation has_text(n: Note) -> Int64 =
    match n
      case Note(some(_)) -> 1
      case Note(none()) -> 0

  operation t() -> Int64 = has_text(make())
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi408.term.t"), 1, "bare String in Option[Term] coerced");
}

// ── Nested Option: no silent double-wrap ─────────────────────────────────

/// A bare `5` into `Option[T = Option[T = Int64]]` would need TWO insertions
/// — rejected loudly; the explicit inner `some(5)` (one insertion) loads.
#[test]
fn nested_option_bare_rejected_explicit_inner_accepted() {
    let bare = r#"
namespace wi408.nested
  import anthill.prelude.{Int64, Option}
  entity N(v: Option[T = Option[T = Int64]])
  operation bad() -> N = N(v: 5)
end
"#;
    let errs = load_errors(&[bare]);
    assert!(
        errs.iter().any(|e| e.contains("mismatch") || e.contains("expected")),
        "doubly-bare value under nested Option must be rejected: {errs:?}"
    );

    let inner = r#"
namespace wi408.nested2
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{some, none}
  entity N2(v: Option[T = Option[T = Int64]])
  operation ok() -> N2 = N2(v: some(5))
end
"#;
    let errs = load_errors(&[inner]);
    assert!(errs.is_empty(), "explicit inner some needs only ONE wrap: {errs:?}");
}

// ── LOADER leg: on-disk facts + rule patterns ────────────────────────────

/// A fact supplying a bare value for an Option field is wrapped at LOAD, so
/// an explicit `some(...)` rule pattern matches it; a bare CONSTRUCTOR
/// pattern in the same slot wraps identically, so it keeps matching too.
/// A var pattern binds the WHOLE option (the `some(...)` envelope).
#[test]
fn fact_fields_wrap_and_rule_patterns_align() {
    let src = r#"
namespace wi408.facts
  import anthill.prelude.{Int64, Option, String, List}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.List.{cons, nil}

  entity Item(name: String, deps: Option[T = List[T = String]])

  fact Item(name: "a", deps: ["x", "y"])
  fact Item(name: "b", deps: none)

  -- explicit some pattern: matches the loader-wrapped fact
  rule first_dep_explicit(?d)
    :- Item(name: "a", deps: some(cons(head: ?d, tail: ?)))

  -- bare cons pattern in the Option slot: wraps at load, matches the same
  rule first_dep_bare(?d)
    :- Item(name: "a", deps: cons(head: ?d, tail: ?))

  -- var pattern binds the whole Option value
  rule deps_of(?n, ?o) :- Item(name: ?n, deps: ?o)
end
"#;
    let kb = &mut crate::common::load_kb_with(src);
    let config = ResolveConfig { max_solutions: 4, ..ResolveConfig::default() };

    for rule in ["first_dep_explicit", "first_dep_bare"] {
        let rule_sym = kb.resolve_symbol(&format!("wi408.facts.{rule}"));
        let var_d = make_var(kb, "d");
        let goal = kb.alloc(Term::Fn {
            functor: rule_sym,
            pos_args: smallvec::SmallVec::from_elem(var_d, 1),
            named_args: smallvec::SmallVec::new(),
        });
        let solutions = kb.resolve(&[goal], &config);
        assert!(!solutions.is_empty(), "{rule} should match the wrapped fact");
        let d_tid = kb.reify(var_d, &solutions[0].subst).expect_term();
        match kb.get_term(d_tid).clone() {
            Term::Const(anthill_core::kb::term::Literal::String(s)) => {
                assert_eq!(s, "x", "{rule}: first dep is \"x\"");
            }
            other => panic!("{rule}: expected String dep, got {other:?}"),
        }
    }

    // deps_of("a", ?o): ?o binds the WRAPPED value — functor is Option.some.
    let rule_sym = kb.resolve_symbol("wi408.facts.deps_of");
    let name_term = kb.alloc(Term::Const(anthill_core::kb::term::Literal::String("a".into())));
    let var_o = make_var(kb, "o");
    let goal = kb.alloc(Term::Fn {
        functor: rule_sym,
        pos_args: smallvec::SmallVec::from_slice(&[name_term, var_o]),
        named_args: smallvec::SmallVec::new(),
    });
    let solutions = kb.resolve(&[goal], &config);
    assert!(!solutions.is_empty(), "deps_of should match");
    let o_tid = kb.reify(var_o, &solutions[0].subst).expect_term();
    match kb.get_term(o_tid).clone() {
        Term::Fn { functor, .. } => {
            let qn = kb.qualified_name_of(functor).to_string();
            assert_eq!(qn, "anthill.prelude.Option.some", "fact slot wrapped in some(...)");
        }
        other => panic!("expected some(...) envelope, got {other:?}"),
    }

    // The explicit `none` fact stays none (no wrap around some/none heads).
    let name_b = kb.alloc(Term::Const(anthill_core::kb::term::Literal::String("b".into())));
    let var_o2 = make_var(kb, "o2");
    let goal = kb.alloc(Term::Fn {
        functor: rule_sym,
        pos_args: smallvec::SmallVec::from_slice(&[name_b, var_o2]),
        named_args: smallvec::SmallVec::new(),
    });
    let solutions = kb.resolve(&[goal], &config);
    assert!(!solutions.is_empty(), "deps_of(b) should match");
    let o_tid = kb.reify(var_o2, &solutions[0].subst).expect_term();
    let functor = match kb.get_term(o_tid) {
        Term::Fn { functor, .. } => *functor,
        Term::Ref(f) | Term::Ident(f) => *f,
        other => panic!("expected none head, got {other:?}"),
    };
    assert_eq!(
        kb.qualified_name_of(functor),
        "anthill.prelude.Option.none",
        "explicit none stays none — no wrap around Option heads"
    );
}


