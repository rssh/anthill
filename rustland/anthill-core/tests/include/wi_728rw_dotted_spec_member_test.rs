//! WI-728RW: a dotted spec head uses the same member reading as an imported head.
//! Open-member refusals, alias execution and dotted diagnostics fail backed out.
//! Fixed-member and ordinary qualified-name execution are controls.
use crate::common::{assert_refused_naming, load_errors_of, run_int64};

const DECLS: &str = r#"
namespace probe.ns
  import anthill.prelude.{Int64, String, Error}
  sort Outer
    sort Y
      sort C = ?
      effects E = ?
      operation yo(self: C) -> Int64 effects {E}
    end
    sort Z
      sort C = ?
      effects E = ?
      operation zo(self: C) -> Int64 effects {E}
    end
  end
  sort AliasOuter
    sort SX = Outer.Y
  end
  sort Fixed
    sort C = Int64
  end
  sort FixedOuter
    sort SX = Fixed
  end
  sort A
    entity a
    provides Outer.Y[C = A, E = {}]
    operation yo(self: A) -> Int64 = 1
    provides Outer.Z[C = A, E = {}]
    operation zo(self: A) -> Int64 = 10
  end
  import probe.ns.A.a
"#;

fn program(body: &str) -> String {
    format!("{DECLS}\n{body}\nend")
}

#[test]
fn dotted_open_members_require_a_provision() {
    for head in ["Outer.Y", "probe.ns.Outer.Y", "AliasOuter.SX"] {
        let src = program(&format!(
            "operation f(b: {head}.C) -> Int64 = 1\noperation main() -> Int64 = f(5)"
        ));
        assert_refused_naming(
            &load_errors_of(&src),
            &[
                "cannot be supplied",
                "probe.ns.Outer.Y[C = anthill.prelude.Int64]",
            ],
            head,
        );
    }
}

#[test]
fn dotted_open_members_dispatch_through_the_provider() {
    for head in ["Outer.Y", "probe.ns.Outer.Y", "AliasOuter.SX"] {
        let src = program(&format!("operation f(b: {head}.C) -> Int64 effects {{{head}.E}} = {head}.yo(b)\noperation main() -> Int64 = f(a())"));
        assert_eq!(run_int64(&src, "probe.ns.main"), Ok(1), "{head}");
    }
}

#[test]
fn dotted_member_return_shares_its_argument_requirement() {
    for head in ["Outer.Y", "probe.ns.Outer.Y", "AliasOuter.SX"] {
        let src = program(&format!("operation identity(b: {head}.C) -> {head}.C = b\noperation main() -> Int64 = Outer.Y.yo(identity(a()))"));
        assert_eq!(run_int64(&src, "probe.ns.main"), Ok(1), "{head}");
        let src = program(&format!("operation identity(b: {head}.C) -> {head}.C = b\noperation main() -> Int64 = identity(5)"));
        assert_refused_naming(
            &load_errors_of(&src),
            &[
                "cannot be supplied",
                "probe.ns.Outer.Y[C = anthill.prelude.Int64]",
            ],
            head,
        );
    }
}

#[test]
fn dotted_effect_members_are_printed_as_written() {
    let src = program(
        r#"
  operation fails() -> Int64 effects {Error}
  operation two(a: Outer.Y.C, b: Outer.Z.C) -> Int64 effects {Outer.Y.E, Outer.Z.E} = fails()
"#,
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &[
            "expected declared: [Outer.Y.E, Outer.Z.E]",
            "undeclared effect: Error",
        ],
        "distinct dotted members",
    );
}

#[test]
fn dotted_effect_members_run_through_distinct_requirements() {
    let src = program(
        r#"
  operation two(x: Outer.Y.C, y: Outer.Z.C) -> Int64 effects {Outer.Y.E, Outer.Z.E} = Outer.Y.yo(x) + Outer.Z.zo(y)
  operation main() -> Int64 = two(a(), a())
"#,
    );
    assert_eq!(run_int64(&src, "probe.ns.main"), Ok(11));
}

#[test]
fn fixed_nested_alias_member_remains_the_fixed_type() {
    for member in ["Fixed.C", "FixedOuter.SX.C", "probe.ns.FixedOuter.SX.C"] {
        let body = format!("operation f(b: {member}) -> Int64 = b");
        assert_eq!(
            run_int64(
                &program(&format!("{body}\noperation main() -> Int64 = f(5)")),
                "probe.ns.main"
            ),
            Ok(5),
            "{member}"
        );
        assert_refused_naming(
            &load_errors_of(&program(&format!(
                "{body}\noperation main() -> Int64 = f(\"s\")"
            ))),
            // The member is the alias `sort C = Int64`, and an alias written where a type
            // is expected is that type (WI-20261009-ZY11J; it printed `expected C`). The
            // message names both: the alias as written, then the type it is.
            &["f.b (op-arg)", "expected C (Int64)", "got String"],
            member,
        );
    }
}

#[test]
fn ordinary_qualified_types_and_constructors_still_execute() {
    let src = program(
        r#"
  sort Enum
    entity value(n: Int64)
  end
  sort DataOuter
    sort Inner
      entity inner(n: Int64)
    end
  end
  operation valueOf(v: probe.ns.Enum) -> Int64 = match v case probe.ns.Enum.value(n) -> n
  operation innerOf(v: DataOuter.Inner) -> Int64 = match v case DataOuter.Inner.inner(n) -> n
  operation main() -> Int64 = valueOf(Enum.value(5)) + innerOf(DataOuter.Inner.inner(6))
"#,
    );
    assert_eq!(run_int64(&src, "probe.ns.main"), Ok(11));
}
