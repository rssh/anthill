//! `anthill.prelude.Time.now` — wall-clock builtin used by WI-009
//! mutating commands to stamp `at:` fields on Feedback / status
//! transitions in the legacy `YYYY-MM-DDTHH:MM:SSZ` form.


use anthill_core::eval::Value;
use crate::common::interp_for;

#[test]
fn time_now_returns_iso_z_timestamp() {
    let mut interp = interp_for("namespace test.time_now end\n");
    let v = interp.call("anthill.prelude.Time.now", &[]).expect("Time.now");
    let s = match v {
        Value::Str(s) => s,
        other => panic!("expected Str, got {other:?}"),
    };
    // Shape: 4-2-2 T 2:2:2 Z, no fractional seconds, no offset.
    assert_eq!(s.len(), 20, "unexpected length: {s:?}");
    assert_eq!(&s[4..5], "-");
    assert_eq!(&s[7..8], "-");
    assert_eq!(&s[10..11], "T");
    assert_eq!(&s[13..14], ":");
    assert_eq!(&s[16..17], ":");
    assert_eq!(&s[19..20], "Z");
}

#[test]
fn time_now_callable_from_anthill_source() {
    let src = r#"
namespace test.time_now_src
  import anthill.prelude.Time.{now}
  operation when() -> String = now()
end
"#;
    let mut interp = interp_for(src);
    let r = interp.call("test.time_now_src.when", &[]).expect("call when");
    match r {
        Value::Str(s) => assert!(s.ends_with('Z') && s.len() == 20,
            "expected RFC3339-Z timestamp, got {s:?}"),
        other => panic!("expected Str, got {other:?}"),
    }
}
