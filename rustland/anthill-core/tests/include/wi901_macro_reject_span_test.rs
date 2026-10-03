//! WI-901 — an anthill-written macro can reject at an occurrence it names.
//!
//! WI-757 already pins both controls in `wi757_macro_diagnostic_test`:
//! `an_anthill_macro_rejects_by_raising` proves a spanless `Error.raise` remains
//! located at the whole redex, and `a_macro_that_is_not_applicable_still_declines_quietly`
//! proves the decline path remains distinct. This file drives only the new third
//! route: `anthill.reflect.reject(message, at)` carries `at.span` through the
//! existing `MacroRejected` channel.

use crate::common::try_load_kb_with;

#[test]
fn anthill_macro_rejects_at_the_occurrence_it_names() {
    const DETAIL: &str = "the second argument is not accepted";
    const SRC: &str = r#"
namespace test.wi901
  import anthill.prelude.{Int64}
  import anthill.prelude.Numeric.{add}
  import anthill.reflect.{NodeOccurrence, reject}

  operation reject_second(ok: NodeOccurrence, bad: NodeOccurrence) -> NodeOccurrence =
    reject("the second argument is not accepted", bad)

  operation trigger(ok: Int64, bad: Int64) -> Int64 = ok
  rule trigger(?ok, ?bad) <=> reject_second(?ok, ?bad) @[simp]

  operation consumer() -> Int64 = add(trigger(1, 99), 1)
end
"#;

    let errs = try_load_kb_with(SRC)
        .err()
        .unwrap_or_else(|| panic!("the macro must reject its second argument:\n{SRC}"));
    let rejections: Vec<&String> = errs
        .iter()
        .filter(|e| e.contains(DETAIL))
        .collect();
    let [rejection] = rejections[..] else {
        panic!("expected exactly one rejection carrying the macro's words, got: {errs:?}");
    };
    assert!(
        rejection.contains("compile-time macro `test.wi901.reject_second`")
            && rejection.contains(DETAIL),
        "the rejection must use the ordinary WI-757 channel: {rejection}",
    );

    let body_line = SRC
        .lines()
        .position(|line| line.contains("add(trigger(1, 99)"))
        .expect("the fixture has the consumer body")
        + 1;
    let line_text = SRC.lines().nth(body_line - 1).unwrap();
    let bad_col = line_text.find("99").unwrap() + 1;
    let redex_col = line_text.find("trigger").unwrap() + 1;
    assert_ne!(bad_col, redex_col, "the control needs distinct spans");
    assert!(
        rejection.starts_with(&format!("{body_line}:{bad_col}:")),
        "the rejection must point at the named `99` occurrence, not the whole redex at \
         {body_line}:{redex_col}; got: {rejection}",
    );
}
