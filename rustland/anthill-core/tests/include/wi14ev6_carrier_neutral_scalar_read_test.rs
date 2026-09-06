//! WI-20260827-14EV6 — a scalar reaching a Console handler is read on WHATEVER
//! CARRIER it arrived on.
//!
//! THE DEFECT. `Value` carried inherent `as_str` / `as_int` / `as_bool` that matched
//! their own native variant and answered `None` for every other carrier. The last two
//! production readers of that family were the two Console write handlers
//! (`eval/effects.rs`), each `args.get(1).and_then(Value::as_str)`. So a `println`
//! whose String rode as a hash-consed `Value::Term` or as a `Value::Node` over
//! `Expr::Const` raised
//!
//!     TypeMismatch { expected: "String", got: "missing or non-String argument" }
//!
//! about a value that WAS a string. The message was wrong twice: it named
//! "non-String" for a String, and it blamed the argument for the reader's blindness.
//!
//! IT IS REACHABLE FROM THE LANGUAGE, not only from a host `interp.call`.
//! WI-20260827-3ZNBC stopped normalizing relation columns into native values — a
//! column is now the bound value on the carrier the search proved it on — so
//! `println(c, person_name.head.n)` hands the handler a `Value::Term`. That is
//! `a_relation_column_prints`, and it is the row that matters most: nothing in the
//! test harness puts that carrier there, the language does.
//!
//! ── CONTROL ─────────────────────────────────────────────────────────────
//!
//! `a_native_string_prints` is the control and PASSES EITHER WAY BY DESIGN. It is the
//! same operation, the same effect row, the same registered handler and the same
//! namespace as the failing rows — only the carrier differs. Without it, every way of
//! breaking the fixture (an unregistered handler, a mis-typed effect row, a namespace
//! that does not load) reproduces the same empty buffer as the defect does.
//!
//! WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT. MEASURED, not asserted, and the
//! RECIPE MATTERS — it must narrow ONLY the read, keeping `console_text`'s two
//! `ok_or_else` arms apart. In `console_text`, replace the `str_operand_opt` call with
//!
//!     match arg { Value::Str(s) => Some(Cow::Borrowed(s.as_str())), _ => None }
//!
//! and EXACTLY THREE of the eight fail: `a_term_carried_string_prints`,
//! `a_node_carried_string_prints`, `a_relation_column_prints`.
//!
//! A COARSER BACK-OUT MEASURES SOMETHING ELSE, which /code-review caught in an earlier
//! draft of this header: collapsing the whole helper to
//! `args.get(1).and_then(…)` ALSO deletes the absent-argument arm, so
//! `the_second_argument_is_still_required` and `a_non_string_argument_names_what_it_got`
//! fail too — and then the row list no longer isolates the carrier question from the
//! diagnostic split. Two changes in one back-out credit neither.
//!
//! THE OTHER FIVE PASS EITHER WAY, BY DESIGN, and each says why at its own site:
//!   * `a_native_string_prints` — the control described above;
//!   * `the_second_argument_is_still_required` / `a_non_string_argument_names_what_it_got`
//!     — these pin the SPLIT this ticket put into the diagnostic rather than the carrier.
//!     "no argument at index 1" and "denotes no string" are different bugs in the caller,
//!     and the old message merged them into one "missing or non-String";
//!   * `an_int64_reads_the_same_on_every_carrier` / `a_bool_reads_the_same_on_every_carrier`
//!     — the `Int64` and `Bool` halves of the deleted family, which had NO production
//!     reader left to drive them through. They guard `TermView`'s scalar arms, not this
//!     ticket's diff. See the section above them.

use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::term::{Literal, Term};
use anthill_core::span::{SourceId, SourceSpan};

use crate::common::{buffered_console, interp_for};

/// One operation, one `String` parameter, printed. The parameter is what lets the
/// caller choose the carrier — a fixture that printed a literal could not.
const SRC: &str = r#"
namespace test.wi14ev6
  import anthill.prelude.{Console, Unit, String}
  import anthill.prelude.Console.{console, println, ConsoleOutput}

  operation shout(c: Console, s: String) -> Unit effects ConsoleOutput = println(c, s)
end
"#;

fn span() -> SourceSpan {
    SourceSpan::new(SourceId::from_raw(0), 0, 5)
}

/// A fresh interpreter over [`SRC`] with a capturing `ConsoleOutput` handler, plus the
/// `Console` receiver value the operation takes.
fn fixture() -> (Interpreter, std::rc::Rc<std::cell::RefCell<String>>, Value) {
    let mut interp = interp_for(SRC);
    let (buf, handler) = buffered_console();
    interp
        .register_effect_handler("anthill.prelude.Console.ConsoleOutput", handler)
        .expect("register the ConsoleOutput handler");
    let console_sym = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Console.console")
        .expect("Console.console symbol");
    let console = Value::Entity {
        functor: console_sym,
        pos: Vec::new().into(),
        named: Vec::new().into(),
    };
    (interp, buf, console)
}

/// Run `shout` with `s`. The handler's buffer is what the caller then reads.
fn shout(interp: &mut Interpreter, console: Value, s: Value) {
    interp
        .call("test.wi14ev6.shout", &[console, s])
        .unwrap_or_else(|e| panic!("shout must run: {e:?}"));
}

/// THE CONTROL. Passes with the change backed out, and says so: the fixture loads, the
/// handler is registered against the right effect sort, and `println` reaches it.
#[test]
fn a_native_string_prints() {
    let (mut interp, buf, console) = fixture();
    shout(&mut interp, console, Value::Str("hello".into()));
    assert_eq!(
        buf.borrow().as_str(),
        "hello\n",
        "a native Value::Str must print — if this fails the fixture is broken, not the read"
    );
}

/// The hash-consed carrier. Fails on a back-out.
#[test]
fn a_term_carried_string_prints() {
    let (mut interp, buf, console) = fixture();
    let tid = interp
        .kb_mut()
        .alloc(Term::Const(Literal::String("hello".into())));
    shout(&mut interp, console, Value::term(tid));
    assert_eq!(
        buf.borrow().as_str(),
        "hello\n",
        "the SAME string hash-consed must print the same text as the native one"
    );
}

/// The occurrence carrier. Fails on a back-out.
#[test]
fn a_node_carried_string_prints() {
    let (mut interp, buf, console) = fixture();
    let occ = Value::node(NodeOccurrence::new_expr(
        Expr::Const(Literal::String("hello".into())),
        span(),
        None,
    ));
    shout(&mut interp, console, occ);
    assert_eq!(
        buf.borrow().as_str(),
        "hello\n",
        "the SAME string as a rule-body occurrence must print the same text"
    );
}

/// THE ROW THAT MATTERS: no host hands the carrier in here. A relation column carries
/// its value on whatever carrier the search proved it on (WI-20260827-3ZNBC), so this
/// `println` receives a `Value::Term` because the LANGUAGE put one there.
///
/// The `theName` assertion beside it is not decoration: it shows the column reaches the
/// body and denotes `"ada"`, so a failure of the `println` row cannot be read as "the
/// relation was empty" or "the field access missed".
#[test]
fn a_relation_column_prints() {
    let src = r#"
namespace test.wi14ev6rel
  import anthill.prelude.{Console, Unit, String, Error, EmptyStream}
  import anthill.prelude.Console.{console, println, ConsoleOutput}

  sort P
    entity person(name: String)
  end

  fact person(name: "ada")

  rule person_name(?n) :- person(name: ?n)

  operation announce(c: Console) -> Unit
      effects {ConsoleOutput, Error, Error[T = EmptyStream]} =
    println(c, person_name.head.n)

  operation theName() -> String effects {Error, Error[T = EmptyStream]} =
    person_name.head.n
end
"#;

    let mut interp = interp_for(src);
    let column = interp
        .call("test.wi14ev6rel.theName", &[])
        .expect("the column must reach the body");
    assert_eq!(
        crate::common::scalar_str(interp.kb(), &column).as_deref(),
        Some("ada"),
        "the column denotes \"ada\"; got {column:?}"
    );

    let mut interp = interp_for(src);
    let (buf, handler) = buffered_console();
    interp
        .register_effect_handler("anthill.prelude.Console.ConsoleOutput", handler)
        .expect("register the ConsoleOutput handler");
    let console_sym = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Console.console")
        .expect("Console.console symbol");
    let console = Value::Entity {
        functor: console_sym,
        pos: Vec::new().into(),
        named: Vec::new().into(),
    };
    interp
        .call("test.wi14ev6rel.announce", &[console])
        .unwrap_or_else(|e| panic!("printing a relation column must run: {e:?}"));
    assert_eq!(
        buf.borrow().as_str(),
        "ada\n",
        "a String column printed straight out of a relation"
    );
}

/// The OTHER half of the old merged message, kept apart. A handler bound to an
/// operation of the wrong arity gets no argument at all, and that is a different bug
/// from being handed a non-string — so it must not read as one. Passes either way by
/// design: it pins the split, not the carrier.
#[test]
fn the_second_argument_is_still_required() {
    let (mut interp, _buf, _console) = fixture();
    let op_sym = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Console.println")
        .expect("Console.println symbol");
    let err = interp
        .invoke_effect_handler("anthill.prelude.Console.ConsoleOutput", op_sym, &[])
        .expect_err("a handler called with no arguments must refuse");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("no argument at index 1"),
        "an ABSENT argument names itself, rather than reading as a non-String; got {msg}"
    );
}

/// And the non-string case keeps its own wording, naming the carrier it could not read
/// a string out of. Passes either way by design — the narrow read refused this too.
#[test]
fn a_non_string_argument_names_what_it_got() {
    let (mut interp, _buf, _console) = fixture();
    let op_sym = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.Console.println")
        .expect("Console.println symbol");
    let err = interp
        .invoke_effect_handler(
            "anthill.prelude.Console.ConsoleOutput",
            op_sym,
            &[Value::Unit, Value::Int(7)],
        )
        .expect_err("an Int64 is not a String on any carrier");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("denotes no string") && msg.contains("Int64"),
        "a value that is not a string must say so and name what it was; got {msg}"
    );
}

// ── The other two scalar types ───────────────────────────────────────────
//
// The ticket asked for all THREE deleted accessors driven on all three carriers.
// `String` is driven above, through the only production reader the family had left.
// `Int64` and `Bool` had NO production reader left at all — WI-20260827-3ZNBC had
// already moved every one of them — so there is no operation to drive them through,
// and the rows below drive their replacements directly instead.
//
// WHAT THIS IS AND IS NOT EVIDENCE FOR, stated rather than implied. It fails under NO
// back-out of this ticket: nothing here reads code WI-20260827-14EV6 wrote. It is a
// regression guard for the property the deletion made load-bearing — that
// `literal_int64` / `literal_bool` answer the same value on every carrier — which
// until now was asserted only indirectly, through consumers that happened to see one
// carrier each. It fails if `impl TermView for Value`'s scalar arms or `occ_head`'s
// `Expr::Const` arm stop mapping onto `ViewHead::Const`.

/// One `Int64`, three carriers, one answer.
#[test]
fn an_int64_reads_the_same_on_every_carrier() {
    use anthill_core::kb::term_view::TermView;
    let mut interp = interp_for(SRC);
    let tid = interp.kb_mut().alloc(Term::Const(Literal::Int(42)));

    let native = Value::Int(42);
    let termed = Value::term(tid);
    let noded = Value::node(NodeOccurrence::new_expr(
        Expr::Const(Literal::Int(42)),
        span(),
        None,
    ));

    let kb = interp.kb();
    assert_eq!(native.literal_int64(kb), Some(42), "native");
    assert_eq!(termed.literal_int64(kb), Some(42), "hash-consed");
    assert_eq!(noded.literal_int64(kb), Some(42), "occurrence");

    // And a value that is NOT an Int64 stays `None` on every carrier — the read widens
    // which CARRIER is accepted, never which VALUE.
    assert_eq!(
        Value::Str("42".into()).literal_int64(kb),
        None,
        "a String does not read as an Int64 just because it spells one"
    );
}

/// One `Bool`, three carriers, one answer.
#[test]
fn a_bool_reads_the_same_on_every_carrier() {
    use anthill_core::kb::term_view::TermView;
    let mut interp = interp_for(SRC);
    let tid = interp.kb_mut().alloc(Term::Const(Literal::Bool(true)));

    let native = Value::Bool(true);
    let termed = Value::term(tid);
    let noded = Value::node(NodeOccurrence::new_expr(
        Expr::Const(Literal::Bool(true)),
        span(),
        None,
    ));

    let kb = interp.kb();
    assert_eq!(native.literal_bool(kb), Some(true), "native");
    assert_eq!(termed.literal_bool(kb), Some(true), "hash-consed");
    assert_eq!(noded.literal_bool(kb), Some(true), "occurrence");
    assert_eq!(
        Value::Int(1).literal_bool(kb),
        None,
        "an Int64 does not read as a Bool"
    );
}
