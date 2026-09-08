//! WI-20260902-EQG4F — AN OBLIGATION NEEDS A RESULT VARIABLE.
//!
//! `render_upper_bound_with` interpolates `result_var` unguarded, so a head that binds
//! none emitted `(assert (not (<=  5.0)))` — invalid SMT-LIB handed back as `Ok`, which a
//! solver runner reports as "not unsat" rather than as an error. Found by `/code-review`
//! on this ticket's scaland half and measured HERE before porting the guard: all three
//! rows below returned `Ok` with that document.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! Delete the `result_var.is_empty()` arm in `emit_obligation_with`: ALL THREE rows below
//! fail, each with the same malformed document. Three rows because three DIFFERENT head
//! shapes leave `result_var` empty, and the guard is keyed on the emptiness rather than on
//! any of them — a shape-keyed guard would have to name all three and would miss the next.
//! `a function-like head still emits` passes either way BY DESIGN: it is the control that
//! says the guard is not simply "refuse every obligation".
//!
//! PARITY: scaland's `emitObligationWith` carries the same guard and message shape.

use anthill_smt_gen::{emit_obligation, Obligation};

const SRC: &str = r#"
namespace test.eqg4f.oblig
  import anthill.prelude.{Float}
  import anthill.prelude.Numeric.{add}
  entity Params(base: Float)
  entity Marker(tag: Float)

  -- `Bottom` via the nullary carrier (WI-20260902-CZJ2N's `classify_head` arm).
  rule flagR :- Params(base: ?b)
  -- `Bottom` via a named-arg-only `Term::Fn` head — the shape that says the hole is
  -- OLDER than that arm, because it reached the renderer the same way before it.
  rule entityHeadR(base: 3.0) :- Params(base: ?b)
  -- `Predicate` — an ENTITY functor is what `classify_head` reads as one. It heads its
  -- OWN entity (`Marker`), not `Params`: a bodied rule on `Params` would make WI-772
  -- refuse the fact harvest and the control below would fail for that reason instead.
  rule Marker(tag: ?t) :- Params(base: ?t)
  -- The control: a function-like head, which is what an obligation is FOR.
  rule boundR(?r) :- Params(base: ?b), ?r = add(?b, 1.0)

  fact Params(base: 2.0)
end
"#;

#[test]
fn an_obligation_on_a_head_that_binds_no_result_variable_is_refused() {
    let kb = crate::common::load_kb_with(SRC);
    // COLLECTED, NOT SHORT-CIRCUITED: the header claims all THREE rows fail on a back-out,
    // and a loop that panics on the first would only ever have measured one of them.
    let mut bad: Vec<String> = Vec::new();
    for qn in [
        "test.eqg4f.oblig.flagR",
        "test.eqg4f.oblig.entityHeadR",
        "test.eqg4f.oblig.Marker",
    ] {
        match emit_obligation(
            &kb,
            &Obligation {
                rule_qn: qn.to_string(),
                upper_bound: 5.0,
            },
        ) {
            Err(e) if format!("{e:?}").contains("binds no result variable") => {}
            Err(e) => bad.push(format!("{qn}: wrong refusal: {e:?}")),
            Ok(doc) => bad.push(format!(
                "{qn}: must be refused; got a document Z3 cannot parse:\n{doc}"
            )),
        }
    }
    assert!(bad.is_empty(), "{} of 3 rows wrong:\n{}", bad.len(), bad.join("\n"));
}

/// THE CONTROL: a function-like head is what an obligation is for, and it still emits.
#[test]
fn a_function_like_head_still_emits() {
    let kb = crate::common::load_kb_with(SRC);
    let doc = emit_obligation(
        &kb,
        &Obligation {
            rule_qn: "test.eqg4f.oblig.boundR".to_string(),
            upper_bound: 5.0,
        },
    )
    .unwrap_or_else(|e| panic!("a function-like head must emit, got: {e:?}"));
    assert!(
        doc.contains("(check-sat)"),
        "the emitted document must be well-formed:\n{doc}"
    );
}
