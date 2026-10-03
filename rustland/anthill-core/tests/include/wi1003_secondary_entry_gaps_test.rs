//! WI-1003 / proposal 059 — the gaps a production-by-production check of R3 found,
//! and the visibility consequence of R2's "one scope" that 059 had not stated.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! Both back-outs applied and run over this file:
//!
//!   * **Contract targets** — drop the clause-keyword peel at the top of
//!     `SecondaryEntryPass::target_names_this_entry`. [`a_contract_proof_of_the_entrys_own_operation_is_admitted`]
//!     FAILS: `proof show.ensures` reads `show` as a foreign PREFIX and is refused,
//!     though `show` is this entry's own member.
//!   * **Header descriptions** — drop the `ns.descriptions` arm in
//!     `SecondaryEntryPass::enter_scope`. [`an_entrys_own_description_block_is_refused`]
//!     FAILS: the block loads clean and writes a `DescriptionInfo` onto the TYPE.
//!
//! ── PASS EITHER WAY, BY DESIGN ───────────────────────────────────────────────
//!
//!   * [`a_contract_proof_of_the_main_entrys_operation_stays_refused`] — the refusal
//!     the peel must not loosen. Before the peel it was refused for the wrong reason
//!     (the prefix), after it for the right one (the operation is the main entry's).
//!   * the controls inside [`an_entrys_own_description_block_is_refused`] — the same
//!     header block on an ORDINARY namespace, and on the main entry, both load.
//!   * [`internal_members_are_shared_by_every_entry`] — states what `internal` means
//!     under R2's one scope; nothing in this ticket changed it.

use anthill_core::eval::{self, Interpreter, Value};
use anthill_core::kb::proof_verify::{verify_proofs, ProofVerdict};

fn r3_errors(srcs: &[&str]) -> Vec<String> {
    crate::common::try_load_kb_with_files(srcs)
        .err()
        .unwrap_or_default()
        .into_iter()
        .filter(|e| e.contains("is not allowed in a secondary entry"))
        .collect()
}

fn eval_int(srcs: &[&str], op: &str) -> Result<i64, String> {
    let kb = crate::common::try_load_kb_with_files(srcs)
        .unwrap_or_else(|errs| panic!("fixture must load clean; got {errs:#?}"));
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp).expect("register eval builtins");
    match interp.call(op, &[]) {
        Ok(Value::Int(n)) => Ok(n),
        Ok(other) => Err(format!("expected Int, got {}", other.type_name())),
        Err(e) => Err(format!("{e}")),
    }
}

/// `proof` target is the only thing that varies between the contract rows.
fn contract_fixture(proof_target: &str) -> String {
    format!(
        r#"
namespace test.wi1003.contract
  import anthill.prelude.PartialEq.{{eq}}
  sort Rec
    entity rec(n: Int64)
    operation other(x: Int64) -> Rec
      ensures eq(result.n, x)
      = rec(n: x)
  end
  namespace Rec
    operation show(x: Int64) -> Rec
      ensures eq(result.n, x)
      = rec(n: x)
    proof {proof_target} by derivation end
  end
end
"#
    )
}

/// A CONTRACT proof (`<op>.ensures`, proposal 025) is about the OPERATION, so the
/// entry that declares the operation may prove its contract — bare or qualified
/// against the entry's own address. Driven to a verdict, not merely loaded: the
/// proof is verified and discharges.
#[test]
fn a_contract_proof_of_the_entrys_own_operation_is_admitted() {
    for target in ["show.ensures", "Rec.show.ensures"] {
        let src = contract_fixture(target);
        assert!(
            r3_errors(&[&src]).is_empty(),
            "`proof {target}` proves a contract of this entry's own operation: {:?}",
            r3_errors(&[&src])
        );
        let mut kb = crate::common::try_load_kb_with(&src)
            .unwrap_or_else(|errs| panic!("must load clean; got {errs:#?}"));
        let report = verify_proofs(&mut kb);
        let verdict = report
            .iter()
            .find(|r| r.rule_qn.ends_with("show.ensures"))
            .unwrap_or_else(|| panic!("no report entry for `{target}`"))
            .verdict
            .clone();
        assert_eq!(
            verdict,
            ProofVerdict::Discharged,
            "the entry's body establishes its own postcondition"
        );
    }
}

/// The other side of the peel: a contract of an operation the MAIN entry declares is
/// a foreign target, refused naming what a proof writes.
#[test]
fn a_contract_proof_of_the_main_entrys_operation_stays_refused() {
    let src = contract_fixture("other.ensures");
    let errs = r3_errors(&[&src]);
    assert!(
        errs.iter()
            .any(|e| e.contains("`proof` 'other.ensures'") && e.contains("set_proof_result")),
        "a contract of a main-entry operation is another entry's; got {errs:#?}"
    );
}

const MAIN: &str = r#"
namespace test.wi1003.desc
  sort Rec
    entity rec(n: Int64)
  end
end
"#;

/// A `namespace X` header block describes the symbol at `X` — at a sort's address,
/// the TYPE, which a secondary entry does not declare. Refused like a foreign-target
/// `describe`, in a separate file exactly as in the main entry's own.
#[test]
fn an_entrys_own_description_block_is_refused() {
    let entry = r#"
namespace test.wi1003.desc
  {< a third party describes Rec >}
  namespace Rec
    operation g(r: Rec) -> Int64 = 1
  end
end
"#;
    let errs = r3_errors(&[MAIN, entry]);
    assert!(
        errs.len() == 1 && errs[0].contains("`description block`"),
        "the entry's header block targets the type and is refused once; got {errs:#?}"
    );

    // CONTROL — the identical text with no sort at the address is an ORDINARY
    // namespace, which nothing in R3 reaches.
    let ordinary = entry.replace("namespace Rec", "namespace Elsewhere");
    let ordinary = ordinary.replace("(r: Rec)", "(r: Int64)");
    assert!(
        crate::common::try_load_kb_with_files(&[MAIN, &ordinary]).is_ok(),
        "an ordinary namespace keeps its header block"
    );

    // CONTROL — the type's own declaration describing itself.
    let own = r#"
namespace test.wi1003.desc
  {< the author describes Rec >}
  sort Rec
    entity rec(n: Int64)
  end
end
"#;
    assert!(
        crate::common::try_load_kb_with(own).is_ok(),
        "the main entry describes its own type"
    );

    // A block carried by a declaration the entry MAKES is the inert one R3 allows.
    let member = r#"
namespace test.wi1003.desc
  namespace Rec
    {< documents this entry's own member >}
    operation g(r: Rec) -> Int64 = 1
  end
end
"#;
    assert!(
        r3_errors(&[MAIN, member]).is_empty(),
        "a member's own block is this entry's: {:?}",
        r3_errors(&[MAIN, member])
    );
}

/// R2'S ONE SCOPE REACHES `internal` TOO. `internal` hides a name from outside the
/// declaring scope (§8.6), and every entry declares into ONE scope — so a secondary
/// entry in another file reads the main entry's internal member, the main entry
/// reads the entry's, and code outside `Rec` reads neither.
#[test]
fn internal_members_are_shared_by_every_entry() {
    let main = r#"
namespace test.wi1003.iv
  sort Rec
    entity rec(n: Int64)
    internal operation secret(r: Rec) -> Int64 = 5
    operation viaMain() -> Int64 = hidden(rec(n: 1))
  end
end
"#;
    let entry = r#"
namespace test.wi1003.iv
  namespace Rec
    operation peek() -> Int64 = secret(rec(n: 1))
    operation peekDot() -> Int64 = rec(n: 1).secret()
    internal operation hidden(r: Rec) -> Int64 = 7
  end
end
"#;
    assert_eq!(eval_int(&[main, entry], "test.wi1003.iv.Rec.peek"), Ok(5));
    assert_eq!(eval_int(&[main, entry], "test.wi1003.iv.Rec.peekDot"), Ok(5));
    assert_eq!(eval_int(&[main, entry], "test.wi1003.iv.Rec.viaMain"), Ok(7));

    let outside = r#"
namespace test.wi1003.ivout
  import test.wi1003.iv.Rec
  operation a() -> Int64 = Rec.hidden(Rec.rec(n: 1))
  operation b() -> Int64 = Rec.secret(Rec.rec(n: 1))
end
"#;
    let errs = crate::common::try_load_kb_with_files(&[main, entry, outside])
        .err()
        .unwrap_or_default();
    for name in ["hidden", "secret"] {
        assert!(
            errs.iter()
                .any(|e| e.contains(&format!("'Rec.{name}' is internal to"))),
            "outside the scope `{name}` stays hidden; got {errs:#?}"
        );
    }
}
