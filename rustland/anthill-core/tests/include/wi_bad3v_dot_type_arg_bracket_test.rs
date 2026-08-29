//! WI-20260829-BAD3V — WHERE A CALL-SITE TYPE-ARG BRACKET MAY BE WRITTEN.
//!
//! `application`'s base is a `name`, so before this the bracket `f[T = X](…)` was
//! admitted exactly where the callee's receiver chain was a pure NAME PATH — which is
//! exactly where the call is NOT a dot call but a QUALIFIED one. Every value-receiver
//! dot refused it in the GRAMMAR, with a misleading error: the `[` was taken as the
//! declaration's `meta_block`, so the reported syntax error landed on the `=` inside a
//! binding it had misread as a `meta_entry`.
//!
//! THE TICKET'S TABLE, RE-MEASURED HERE. Rows B/C/D/E/H are its failing rows, A/F/G/I
//! its controls. Two rows the ticket did NOT have are the ones that say what the rule
//! really was:
//!
//!   * `?xs.map[Dst = Int64](f)` — the FIRST hop, over a variable receiver, was already
//!     a syntax error. So "a chained hop cannot take one" understates it: NO dot call
//!     could, at any depth.
//!   * `xs.map[Dst = Int64](f)` (row A) parses only because `xs.map` is a dotted NAME,
//!     which the converter reads as the qualified functor `xs.map` — not as a dot call
//!     on the value `xs` at all. So the bracket was never admitted ON a dot; it was
//!     admitted on the one spelling that is not one.
//!
//! WHAT THIS DELIVERS. The grammar now admits `dot_application` — the bracket on a dot
//! CALLEE — and the CONVERTER decides what it means:
//!
//!   * QUALIFIED companion receiver (`Map[K = String].empty[T = Int64]()`): the bracket
//!     is this call's type arguments, riding the same `type_args` channel the bare
//!     `Map.empty[T = Int64]()` spelling already fed. NEW capability, driven below.
//!   * VALUE receiver (`?xs.map[Dst = Int64](f)`): REFUSED with a located error naming
//!     the applicative spelling. `Expr::DotApply` carries no `type_args` field — "a dot
//!     is bracket-less by construction" is the WI-842 premise the typer's tier-1
//!     reasoning rests on, and WI-443 already declined to fake a channel by re-routing
//!     a bracketed identifier-receiver call. A parse error that pointed at a
//!     misconstrued meta block becomes an error that names the move.
//!
//! WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT (grammar.js's `dot_application` +
//! `push_fn_term`'s routing):
//!
//!   * `every_value_receiver_dot_shape_reaches_the_converters_refusal` — RED. Every row
//!     goes back to `syntax error near …`.
//!   * `a_companion_receiver_call_reads_its_bracket_as_type_arguments` — RED (both the
//!     parse assertion and the driven one: the fixture stops loading).
//!   * `the_bracket_less_spellings_are_unchanged` — GREEN EITHER WAY, by design. These
//!     are the ticket's A/F/G/I controls plus J/K/M; they measure that admitting the new
//!     shape did not disturb the old ones.
//!   * `a_meta_block_after_a_dot_head_is_still_a_meta_block` and
//!     `a_bare_bracket_off_a_call_is_still_a_syntax_error` — GREEN against the
//!     backed-out grammar, and that is not what they are for: they are the DESIGN
//!     controls, and both go RED against the design this one was chosen over. See
//!     `a_meta_block_after_a_dot_head_is_still_a_meta_block` for the measurement.
//!
//! NOTHING THAT ALREADY EXISTED WOULD HAVE CAUGHT THE REJECTED DESIGN: measured, the
//! tree-sitter corpus stayed 214/214 green under it, and so did the Rust suite's parse
//! tests. The new `dot_type_args.txt` rows do fail there — but only because they name the
//! `dot_application` node that design has not got, so they pin THIS shape rather than
//! arbitrating between the two. The arbitration is `a_meta_block_after_a_dot_head_is_still_a_meta_block`.

use anthill_core::eval::Value;
use anthill_core::kb::term::Term;
use anthill_core::parse;
use anthill_core::parse::ir::Item;

use crate::common::interp_for;

/// The refusal's own words, so the rows below assert the SAME error and a reworded
/// message is one edit.
const DOT_REFUSAL: &str = "call-site type arguments are not supported on a dot call";

fn errors_for(src: &str) -> Vec<String> {
    match parse::parse(src) {
        Ok(_) => Vec::new(),
        Err(es) => es.into_iter().map(|e| e.message).collect(),
    }
}

/// Rows B, C, D, E, H of the ticket's table, plus the two it did not have (a variable
/// receiver, a literal receiver). Each is a VALUE-receiver dot call wearing a type-arg
/// bracket: it must now REACH THE CONVERTER — the failure is the located refusal, not a
/// syntax error — which is exactly the grammar hole the ticket is about.
#[test]
fn every_value_receiver_dot_shape_reaches_the_converters_refusal() {
    let rows: &[(&str, &str)] = &[
        ("B  chained hop", "fact xs.map(f).map[Dst = Int64](g)\n"),
        (
            "C  parenthesized receiver",
            "fact (xs.map(f)).map[Dst = Int64](g)\n",
        ),
        (
            "D  unqualified-call receiver",
            "fact map(xs, f).map[Dst = Int64](g)\n",
        ),
        (
            "E  qualified-call receiver",
            "fact Iterable.map(xs, f).map[Dst = Int64](g)\n",
        ),
        (
            "H  bracket on both hops",
            "fact xs.map[Dst = Int64](f).map[Dst = Int64](g)\n",
        ),
        (
            "L  variable receiver, FIRST hop",
            "fact ?xs.map[Dst = Int64](f)\n",
        ),
        (
            "N  literal receiver",
            "fact [1, 2].map[Dst = Int64](f)\n",
        ),
    ];
    for (label, src) in rows {
        let errs = errors_for(src);
        assert_eq!(
            errs.len(),
            1,
            "{label}: expected exactly the converter's refusal, got {errs:?}"
        );
        assert!(
            errs[0].contains(DOT_REFUSAL),
            "{label}: expected the dot refusal, got `{}`",
            errs[0]
        );
        assert!(
            !errs[0].contains("syntax error"),
            "{label}: the grammar must ADMIT this shape — a syntax error means the \
             `dot_application` production did not fire; got `{}`",
            errs[0]
        );
        // The message must name the move, not only the refusal: the ticket's whole
        // complaint was a diagnostic that sent the author to a spelling the grammar
        // would not follow. It names a SHAPE and no POSITION — see
        // `the_refusal_prescribes_no_position` for why the position half came out.
        assert!(
            errs[0].contains("The applicative spelling"),
            "{label}: the refusal must name the applicative spelling; got `{}`",
            errs[0]
        );
    }
}

/// The refusal is located ON THE BINDING, not on the whole declaration — the span the
/// old syntax error could not produce, because it had misparsed the bracket as a
/// `meta_block` and reported the `=` inside it.
#[test]
fn the_refusal_is_located_on_the_binding() {
    let src = "fact ?xs.map[Dst = Int64](f)\n";
    let errs = parse::parse(src).expect_err("a dot call may not carry the bracket");
    assert_eq!(errs.len(), 1, "{errs:?}");
    let span = errs[0].span;
    assert_eq!(
        &src[span.start as usize..span.end as usize],
        "Dst = Int64",
        "the error must point at the binding it refuses"
    );
}

/// THE CONTROLS — the ticket's A/F/G/I plus the two spellings its corrections named
/// (J unqualified, K qualified) and the bracket-less dot M. **These pass either way**:
/// they are here to show that admitting `dot_application` disturbed neither the
/// qualified-call bracket nor the bracket-less dot chain.
#[test]
fn the_bracket_less_spellings_are_unchanged() {
    let rows: &[(&str, &str)] = &[
        ("A  dotted-NAME callee", "fact xs.map[Dst = Int64](f)\n"),
        ("F  chained dot, no bracket", "fact xs.map(f).map(g)\n"),
        ("G  call receiver, no bracket", "fact map(xs, f).map(g)\n"),
        (
            "I  bracket on hop ONE only",
            "fact xs.map[Dst = Int64](f).map(g)\n",
        ),
        ("J  unqualified call", "fact map[Dst = Int64](xs, f)\n"),
        (
            "K  qualified call",
            "fact Iterable.map[Dst = Int64](xs, f)\n",
        ),
        ("M  variable receiver, no bracket", "fact ?xs.map(f)\n"),
    ];
    for (label, src) in rows {
        assert!(
            parse::parse(src).is_ok(),
            "{label}: must still parse clean, got {:?}",
            errors_for(src)
        );
    }
}

/// THE DESIGN CONTROL. A `[` after a dot head is ALSO how a `meta_block` opens, and
/// nothing local separates the two — the separator is the `(` two reductions later. The
/// shipped production lives only in `fn_term`'s callee slot and a declared GLR conflict
/// lets the continuation decide, so `[simp]` with no call after it can only be the meta
/// block.
///
/// GREEN against the backed-out grammar. THE MEASUREMENT THAT MAKES IT A CONTROL is
/// against the design this one was chosen over — widening `application`'s own `name`
/// field to admit a `field_access`, with `dot_application` and its conflict dropped.
/// Built and run:
///
///   * It does not even GENERATE as written. `application` is reachable from `_type`, so
///     the widening ripples into TYPE positions: three further GLR conflicts had to be
///     declared before `tree-sitter generate` succeeded, two of them nothing to do with
///     dots (`_non_name_atom_term`/`_spec_instantiation` at `requires (?x, …)`,
///     `_type_literal`/`_non_name_atom_term` at `requires (k: "s", …)`).
///   * With those added, `rule dr: ?x.m [simp]` parses as
///     `application(field_access(?x, m), sort_binding(simple_type(simp)))` and the rule's
///     `meta` is NONE — the attribute is silently eaten and the equation goes INERT. Same
///     for `fact ?x.m [simp]`. That is the WI-881 trap, extended from nullary NAME heads
///     to every dot head. THIS TEST FAILS THERE.
///   * So do three of its neighbours, for a different reason worth recording: the
///     bracketed value-receiver dot becomes a bare `application` TERM rather than a
///     `fn_term` callee, so `push_fn_term`'s refusal never runs and the shape loads as
///     something else entirely. (`every_value_receiver_dot_shape_reaches_the_converters_refusal`,
///     `the_refusal_is_located_on_the_binding`, `a_bare_bracket_off_a_call_is_still_a_syntax_error`.)
///   * The tree-sitter corpus stayed 214/214 green throughout.
#[test]
fn a_meta_block_after_a_dot_head_is_still_a_meta_block() {
    for src in [
        "rule dr: ?x.m [simp]\n",
        "fact ?x.m [simp]\n",
        "rule dr2: ?x.m(?y) [simp]\n",
    ] {
        let parsed = parse::parse(src).unwrap_or_else(|e| panic!("{src:?}: {e:?}"));
        let meta = match &parsed.items[0] {
            Item::Rule(r) => &r.meta,
            Item::Fact(f) => &f.meta,
            other => panic!("{src:?}: unexpected item {:?}", std::mem::discriminant(other)),
        };
        let meta = meta
            .as_ref()
            .unwrap_or_else(|| panic!("{src:?}: the `[simp]` must still be the META BLOCK"));
        let keys: Vec<String> = meta
            .entries
            .iter()
            .map(|e| {
                e.key
                    .segments
                    .iter()
                    .map(|s| parsed.symbols.local_name(*s).to_string())
                    .collect::<Vec<_>>()
                    .join(".")
            })
            .collect();
        assert_eq!(keys, vec!["simp".to_string()], "{src:?}");
    }
}

/// THE NARROWNESS, pinned. The bracket is admitted on a dot CALLEE, never on a bare dot
/// projection: `?x.field[T = Int]` has no call after the `]`, so nothing kills the
/// `meta_block` reading and admitting it is what would reopen the ambiguity the test
/// above controls for. Green either way — it says what was deliberately NOT widened.
#[test]
fn a_bare_bracket_off_a_call_is_still_a_syntax_error() {
    let errs = errors_for("fact ?x.field[T = Int]\n");
    assert!(
        errs.iter().any(|e| e.contains("syntax error")),
        "a bracket with no call after it stays a syntax error; got {errs:?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains(DOT_REFUSAL)),
        "it must not reach the converter at all; got {errs:?}"
    );
}

/// THE SECOND ROUTE TO A DOT CALL, refused in the LOADER rather than the converter.
/// `xs.map[Dst = Int64](f)` where `xs` names a LOCAL BINDING is written with a bare NAME
/// callee — it is never a `dot_application` node, so `push_fn_term` structurally cannot
/// see it — and becomes a dot call only when `try_identifier_dot_call` (WI-443) resolves
/// the head segment to a binder. Found by /code-review on the first cut of this ticket,
/// where it was still live: the bracket made WI-443 decline the re-route, the call
/// flattened to the functor `xs.map`, and the author read the typer's verdict on THAT —
/// "expected an operation, which declares the type parameters a call-site `[…]` bracket
/// binds, got a callee with no type-parameter list" — which names a callee they never
/// wrote. That is the misleading-diagnostic class this ticket exists to close, so it is
/// closed on this route too.
///
/// THE CONTROL IS THE SAME PROGRAM WITHOUT THE BRACKET, and it is what makes the row
/// measure the refusal rather than the fixture: `control` loads CLEAN, so the one error
/// on `via_ident` is the bracket and nothing else. Backing out the loader change reddens
/// this test twice over — the message becomes the typer's, and the count becomes 2, since
/// dropping the re-route also leaves the flattened call to fail on its own.
#[test]
fn an_identifier_receiver_dot_call_is_refused_in_the_loader() {
    let stream_ty = "MappedStream[Source = List[T = Int64], Src = Int64, T = Int64,                      ES = {}, EF = {}]";
    let program = |body: &str| {
        format!(
            "namespace test.bad3v_ident
                 import anthill.prelude.{{List, Int64, MappedStream}}
                 operation via(xs: List[T = Int64]) -> {stream_ty} = {body}
end
"
        )
    };

    // CONTROL: the identical call with no bracket loads clean.
    crate::common::expect_loaded(crate::common::try_load_kb_with(&program(
        "xs.map(lambda x -> x)",
    )));

    let errs = match crate::common::try_load_kb_with(&program("xs.map[Dst = Int64](lambda x -> x)"))
    {
        Ok(_) => panic!("an identifier-receiver dot call may not carry the bracket"),
        Err(es) => es.iter().map(|e| e.to_string()).collect::<Vec<_>>(),
    };
    assert_eq!(
        errs.len(),
        1,
        "exactly the refusal — the bracket is dropped once it has been refused, so the          rest of the call still type-checks and reports nothing: {errs:?}"
    );
    assert!(
        errs[0].contains(DOT_REFUSAL),
        "the loader route must give the SAME sentence as the converter route: {}",
        errs[0]
    );
    assert!(
        !errs[0].contains("no type-parameter list"),
        "the flattened-functor diagnosis is what this closes: {}",
        errs[0]
    );
}

/// The refusal names a SHAPE and no POSITION. An earlier wording ended "… in an operation
/// body", which WI-839 had already learned is wrong for a rule head — it prescribes a move
/// a rule head has not got, and the applicative rewrite it names would itself be refused
/// there (`CallTypeArgsPosition::RuleHead`). Found by /code-review. Green either way on the
/// grammar change; it fails against the first cut's wording.
#[test]
fn the_refusal_prescribes_no_position() {
    for src in [
        "rule dr: ?x.m[T = Int64](?y) <=> ?y [simp]
",
        "fact ?x.m[T = Int64](?y)
",
    ] {
        let errs = errors_for(src);
        assert_eq!(errs.len(), 1, "{src:?}: {errs:?}");
        assert!(errs[0].contains(DOT_REFUSAL), "{src:?}: {}", errs[0]);
        assert!(
            !errs[0].contains("operation body"),
            "{src:?}: a rule/fact head has no operation body to move into: {}",
            errs[0]
        );
        assert!(
            !errs[0].contains("receiver, "),
            "{src:?}: a companion receiver takes no receiver ARGUMENT, so the shape the              message names must not spell one: {}",
            errs[0]
        );
    }
}

/// THE NEW CAPABILITY, at the parse IR. `Map[K = String, V = Int64].empty[T = Int64](x)`
/// is a QUALIFIED companion call (form (3) of proposal 035) wearing a type-arg bracket.
/// The receiver's own bindings are erased into the functor exactly as the bracket-less
/// spelling erases them, and the OUTER bracket becomes this call's `type_args` — so the
/// result is indistinguishable from `Map.empty[T = Int64](x)`, which is the reading it
/// should have had all along.
#[test]
fn a_companion_receiver_call_reads_its_bracket_as_type_arguments() {
    let shape = |src: &str| -> (String, Vec<String>) {
        let parsed = parse::parse(src).unwrap_or_else(|e| panic!("{src:?}: {e:?}"));
        let Item::Fact(f) = &parsed.items[0] else {
            panic!("{src:?}: expected a fact")
        };
        let Term::Fn {
            functor,
            named_args,
            ..
        } = parsed.terms.get(f.term)
        else {
            panic!("{src:?}: expected a call")
        };
        let type_args = named_args
            .iter()
            .filter(|(s, _)| parsed.symbols.local_name(*s) == "type_args")
            .map(|(_, tid)| format!("{:?}", parsed.terms.get(*tid)))
            .collect::<Vec<_>>();
        (
            parsed.symbols.local_name(*functor).to_string(),
            type_args,
        )
    };

    let (functor, type_args) = shape("fact Map[K = String, V = Int64].empty[T = Int64](x)\n");
    assert_eq!(functor, "Map.empty", "the receiver's bindings erase, as they do bracket-less");
    assert_eq!(type_args.len(), 1, "the OUTER bracket is the call's type args");
    assert!(
        type_args[0].contains("SortBindings"),
        "the bracket rides the `type_args` ParseAux channel: {}",
        type_args[0]
    );

    // The bracket-less companion form is the CONTROL for the functor half: it has always
    // flattened to `Map.empty`, and adding the bracket must not change that.
    let (plain_functor, plain_type_args) = shape("fact Map[K = String, V = Int64].empty(x)\n");
    assert_eq!(plain_functor, "Map.empty");
    assert!(plain_type_args.is_empty());
}

/// THE NEW CAPABILITY, DRIVEN. `Box[E = Int64].ty[T = String]()` must call `Box.ty` with
/// `T` bound to `String` — the same answer the already-admitted `Box.ty[T = String]()`
/// gives. The two brackets bind DIFFERENT parameters to DIFFERENT sorts on purpose: if
/// the receiver's `E = Int64` were the one read, or if the outer bracket were dropped,
/// the body's `Cell[V = T]` would come back as something other than `Cell[V = String]`.
///
/// `via_plain` is the control — it is the pre-existing `application` spelling and answers
/// the same either way. `via_companion` does not load at all with the change backed out.
#[test]
fn a_companion_receiver_call_drives_its_type_argument() {
    let src = r#"
namespace test.bad3v
  import anthill.prelude.{Cell, Int64, String, Type}

  sort Box
    sort E = ?
    operation ty[T]() -> Type = Cell[V = T]
  end

  operation via_companion() -> Type = Box[E = Int64].ty[T = String]()
  operation via_plain() -> Type = Box.ty[T = String]()
end
"#;
    let mut interp = interp_for(src);

    let bound_sort = |interp: &mut anthill_core::eval::Interpreter, op: &str| -> String {
        let v = interp
            .call(&format!("test.bad3v.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e:?}"));
        let id = match v {
            Value::Term { id, .. } => id,
            other => panic!("{op}: expected a Term-carried type, got {other:?}"),
        };
        let named = match interp.kb().get_term(id).clone() {
            Term::Fn { named_args, .. } => named_args,
            other => panic!("{op}: expected `Cell[V = …]`, got {other:?}"),
        };
        assert_eq!(named.len(), 1, "{op}: one type argument (V)");
        match interp.kb().get_term(named[0].1).clone() {
            Term::Ref(s) | Term::Ident(s) => interp.kb().local_name_of(s).to_string(),
            other => panic!("{op}: V must bind a sort ref, got {other:?}"),
        }
    };

    assert_eq!(
        bound_sort(&mut interp, "via_companion"),
        "String",
        "the OUTER bracket's `T = String` is the call's type argument — not the \
         receiver's `E = Int64`, and not a dropped binding"
    );
    assert_eq!(
        bound_sort(&mut interp, "via_plain"),
        "String",
        "control: the bare-name spelling answers the same"
    );
}
