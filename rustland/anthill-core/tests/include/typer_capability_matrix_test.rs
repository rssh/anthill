//! WI-20260829-ARQ5X — A TYPER CAPABILITY MATRIX: sweep one construct across its hosts.
//!
//! THE SUITE IS ALL REGRESSION AND NO DISCOVERY. 499 of 544 files under
//! `anthill-core/tests/include/` pin one already-discovered defect each, and none sweeps
//! one construct across several host operations — so a gap is found only when someone
//! writes ordinary code and it breaks. Ten of the twelve most recently filed items are
//! typer gaps found exactly that way. This file is the sweep: every cell is a one-liner
//! over one shared fixture, and the cell's VERDICT is the assertion.
//!
//! EVERY CELL CARRIES ITS OWN CONTROL, and that is not decoration — it is the whole
//! reason the file is shaped this way. The four hand-written probes that motivated this
//! ticket reported `xs.filter(lambda r -> r.flag)` REFUSED and concluded the callback dot
//! was broken there. Re-measured with the dot-free control beside it:
//!
//!   List.length(xs.filter(lambda r -> r.flag))  REFUSED -- expected List, got FilteredStream
//!   List.length(xs.filter(lambda r -> true))    REFUSED -- expected List, got FilteredStream
//!
//! Byte-identical. The dot was never what was refused; a lazy stream cannot feed an eager
//! consumer. Three separate probe sets (two in the tickets, one in my first attempt to
//! re-measure them) made that same misattribution, because none ran the dull row next to
//! the interesting one. So [`Body::Constant`] is a row of this matrix, not a footnote: a
//! RED cell means a capability is missing only if its control is GREEN.
//!
//! THE THREE VERDICTS, and the third is the point:
//!   * [`Verdict::Loads`]        the capability works
//!   * [`Verdict::RefusesLocated`] rejected, with a message naming a span
//!   * [`Verdict::KnownGap`]     rejected TODAY and should not be — cites a WI, and
//!                               FAILS WHEN THE GAP CLOSES, so whoever fixes it is told
//!                               to flip the verdict and close the ticket in one commit
//!
//! WHAT THIS SLICE COVERS: callback binders. Hosts {find, filter, map, foldLeft,
//! foldRight} crossed with call spellings {dot, unqualified, qualified} crossed with
//! callback body forms {constant, identity, field dot, match destructure, nested call,
//! dot call} — 84 cells, the 6 remaining combinations being identity under a PREDICATE
//! host, which the language cannot express and which the sweep reports as skipped rather
//! than dropping. Plus three tables the sweep needs to mean anything: `lazy_stream_-
//! consumption` (the measured gap, each cell paired with its dot-free control),
//! `refusals_that_should_stand` (the third verdict — refusals the repo INTENDS, so a
//! future silent accept reds a cell), and `every_verdict_fails_when_it_should` (the
//! harness's own controls).
//!
//! WHY THESE AXES. Spelling, because WI-20260828-N2FHM's defect existed in the named
//! spelling and not the dot one. Body form, because that is what N2FHM was about.
//! `foldRight`, because its callback binds `(x, acc)` — the REVERSE of `foldLeft`'s
//! `(acc, x)` — so a defect keyed on binder ORDER shows there and nowhere else. And the
//! constant row, because it is the control for every other row at the same host and
//! spelling.
//!
//! ONE AXIS WAS TRIED AND DROPPED, with the reason recorded rather than the axis silently
//! absent: a label-parameterized receiver (`Msg[Trust]` with a `Txt[Trust]` field, the
//! guardians shape) changes no verdict in any spelling. See
//! `a_label_parameterized_receiver_changes_no_verdict`, which also records the
//! mis-measurement that made it look necessary.
//!
//! WHAT A CELL CAN AND CANNOT WITNESS. A verdict here is about LOADING, and a sweep is
//! the only thing that can ask 84 questions cheaply — but `LOADS` is not `works`, and
//! this file must not be read as if it were. Driving each capability to a value is the
//! per-WI files''' job, and `wi_n2fhm_find_callback_dot_test` does exactly that for the
//! `find` callback dot (`first_flagged_name` asserts the selected row). A cell that goes
//! green here without a driven test somewhere is evidence that the program type-checks
//! and nothing more.
//!
//! NOT A REWRITE OF THE PER-WI FILES. A matrix cell says a capability holds; a WI file
//! says why one specific defect was possible, and that is what keeps a fix from
//! regressing for its original reason.

use std::fmt::Write as _;

/// What a cell asserts. See the module note — `KnownGap` is the one that does work
/// beyond regression.
#[derive(Clone, Copy, PartialEq)]
enum Verdict {
    Loads,
    /// Refused, and the message is located (`line:col:`). The `&str` is a fragment the
    /// message must contain, so a cell cannot silently start failing for a new reason.
    RefusesLocated(&'static str),
    /// Refused today and should not be. Cites the WI that tracks it. FAILS when the gap
    /// closes — a cell that starts loading tells you to flip it here and close the WI.
    KnownGap {
        wi: &'static str,
        expect: &'static str,
    },
}

/// The shared fixture: one two-field entity, plus the helper operations the `nested call`
/// and `dot call` body forms need. Everything every cell shares lives here, so a cell
/// differs from its neighbours in exactly one axis.
const FIXTURE: &str = r#"
  sort Row
    import anthill.prelude.{Int64, Bool}
    entity row(a: Int64, flag: Bool)
    operation a_of(r: Row) -> Int64 = match r case row(x, f) -> x
    operation is_set(r: Row) -> Bool = match r case row(x, f) -> f
  end
"#;

/// A callback-taking operation, with everything a cell needs to spell a call to it.
struct Host {
    name: &'static str,
    /// Sort to name in the QUALIFIED spelling. `find`/`map`/`filter` are declared on
    /// `Iterable`; the folds moved to `FiniteCollection` (WI-589) and `List` supplies them.
    qualifier: &'static str,
    /// Arguments between the receiver and the callback (`foldLeft`'s seed).
    seed: &'static str,
    /// The callback's binder list — `foldLeft`'s takes the accumulator too.
    binder: &'static str,
    /// Whether the callback must return `Bool` (a predicate) or `Int64` (a value).
    predicate: bool,
    /// How `Body::Identity` is spelled for this host — the element for `map`, the
    /// ACCUMULATOR for the folds. Empty where the form is not expressible.
    identity: &'static str,
}

const HOSTS: &[Host] = &[
    Host { name: "find",      qualifier: "Iterable", seed: "",    binder: "r",        predicate: true,  identity: "" },
    Host { name: "filter",    qualifier: "Iterable", seed: "",    binder: "r",        predicate: true,  identity: "" },
    Host { name: "map",       qualifier: "Iterable", seed: "",    binder: "r",        predicate: false, identity: "r" },
    Host { name: "foldLeft",  qualifier: "List",     seed: "0, ", binder: "(acc, r)", predicate: false, identity: "acc" },
    // WI-20260829-ARQ5X named `foldRight` in the first slice and the first cut dropped it
    // (found by /code-review). It is the host that most earns its row: its callback binds
    // `(x: Element, acc: Acc)` — the REVERSE of `foldLeft`'s `(acc, x)` — so a defect that
    // keys on binder ORDER shows here and nowhere else in this table. `list.anthill:75`,
    // `finite_collection.anthill:50`.
    Host { name: "foldRight", qualifier: "List",     seed: "0, ", binder: "(r, acc)", predicate: false, identity: "acc" },
];

/// How the call is written. N2FHM's gap lived in the named spellings and not the dot one,
/// so this is an axis rather than a detail.
#[derive(Clone, Copy)]
enum Spelling {
    /// `xs.host(f)`
    Dot,
    /// `host(xs, f)` — the short name, reached through the import
    Unqualified,
    /// `Sort.host(xs, f)`
    Qualified,
}

impl Spelling {
    fn name(self) -> &'static str {
        match self {
            Spelling::Dot => "dot",
            Spelling::Unqualified => "unqualified",
            Spelling::Qualified => "qualified",
        }
    }
    fn call(self, h: &Host, cb: &str) -> String {
        match self {
            Spelling::Dot => format!("xs.{}({}{})", h.name, h.seed, cb),
            Spelling::Unqualified => format!("{}(xs, {}{})", h.name, h.seed, cb),
            Spelling::Qualified => format!("{}.{}(xs, {}{})", h.qualifier, h.name, h.seed, cb),
        }
    }
}

/// What sits in the callback body. `Constant` is the CONTROL for every other form at the
/// same host and spelling — see the module note on why it is a row and not a footnote.
#[derive(Clone, Copy)]
enum Body {
    Constant,
    /// The binder returned UNCHANGED. Named in the ticket's first slice and dropped by
    /// the first cut (found by /code-review). It is a second control, weaker than
    /// `Constant` and differently placed: it uses the binder without asking anything of
    /// its type, so `Constant` green + `Identity` red would say the binder does not bind
    /// at all, while `Identity` green + `FieldDot` red says it binds untyped.
    Identity,
    FieldDot,
    MatchDestructure,
    NestedCall,
    DotCall,
}

impl Body {
    fn name(self) -> &'static str {
        match self {
            Body::Constant => "constant (CONTROL)",
            Body::Identity => "identity (CONTROL)",
            Body::FieldDot => "field dot",
            Body::MatchDestructure => "match destructure",
            Body::NestedCall => "nested call",
            Body::DotCall => "dot call",
        }
    }
    /// The body expression, in the flavour the host's callback must return — or `None`
    /// where the form is NOT EXPRESSIBLE for this host, which is a fact about the language
    /// and not a gap. `Identity` is the only such form: returning the binder unchanged
    /// requires the callback's return to be the element's own sort, which a `Bool`
    /// predicate's is not. Skipping is recorded and counted by the sweep rather than
    /// quietly dropped, and it is NOT spelled as `a_of(r)` — that is exactly
    /// `Body::NestedCall`, so a cell built that way would duplicate a row and look like a
    /// second control while measuring the first one twice.
    fn expr(self, predicate: bool) -> Option<&'static str> {
        Some(match (self, predicate) {
            (Body::Constant, true) => "true",
            (Body::Constant, false) => "7",
            // The binder, unchanged. For the folds that is the ACCUMULATOR (returning the
            // element would not type against `Acc`); for `map` it is the element, and
            // `Dst` is free enough to take it.
            (Body::Identity, true) => return None,
            (Body::Identity, false) => "IDENTITY",
            (Body::FieldDot, true) => "r.flag",
            (Body::FieldDot, false) => "r.a",
            (Body::MatchDestructure, true) => "match r case row(x, f) -> f",
            (Body::MatchDestructure, false) => "match r case row(x, f) -> x",
            (Body::NestedCall, true) => "is_set(r)",
            (Body::NestedCall, false) => "a_of(r)",
            (Body::DotCall, true) => "r.is_set()",
            (Body::DotCall, false) => "r.a_of()",
        })
    }
}

const BODIES: &[Body] = &[
    Body::Constant,
    Body::Identity,
    Body::FieldDot,
    Body::MatchDestructure,
    Body::NestedCall,
    Body::DotCall,
];

/// Wrap a body expression in a program. The result is bound by an UNANNOTATED `let` and
/// dropped: nothing downstream hints the callback binder, and nothing consumes the
/// result — so a cell measures the CALL, not what someone does with its value. The
/// consumption table below is where the value's fate is the subject.
fn program(body: &str) -> String {
    format!(
        r#"
namespace capmatrix
  import anthill.prelude.{{List, Int64, Bool, Stream, Option, Iterable}}
  import anthill.prelude.Iterable.{{find, filter, map}}
  import anthill.prelude.List.{{foldLeft, foldRight, length}}
  import capmatrix.Row.{{row, a_of, is_set}}
{FIXTURE}
  operation cell(xs: List[T = Row]) -> Int64 =
    let s = {body}
    42
end
"#
    )
}

/// Load one cell and check it against its verdict. Returns a one-line report either way,
/// and the failure message says what to do rather than only what happened.
fn check(label: &str, body: &str, want: Verdict) -> Result<String, String> {
    let src = program(body);
    // PARSE FIRST, and turn a parse failure into a LABELLED error. `try_load_kb_with`
    // panics on unparseable source (`expect("parse user source")`) — only LOAD errors come
    // back as `Err` — so a syntax slip in one generated cell would abort the whole table
    // naming neither the cell nor the host, and discard every other verdict. That would
    // silently void `run`'s promise to report every failure (found by /code-review).
    if let Err(errs) = anthill_core::parse::parse(&src) {
        let msgs: Vec<String> = errs.iter().map(|e| e.message.clone()).collect();
        return Err(format!(
            "{label}\n  the generated program does not PARSE — this is a bug in the table, \
             not a verdict about the typer:\n    {}\n  source:\n{src}",
            msgs.join("\n    "),
        ));
    }
    let errs = match crate::common::try_load_kb_with(&src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    };
    match want {
        Verdict::Loads => {
            if errs.is_empty() {
                Ok(format!("{label:<52} LOADS"))
            } else {
                Err(format!(
                    "{label}\n  expected LOADS, got {} error(s):\n    {}\n  \
                     If this is a real regression, fix it. If the capability is genuinely \
                     gone, change this cell to Verdict::KnownGap and file the WI.",
                    errs.len(),
                    errs.join("\n    "),
                ))
            }
        }
        Verdict::RefusesLocated(frag) => {
            if errs.is_empty() {
                return Err(format!("{label}\n  expected a REFUSAL, but it loaded clean."));
            }
            let located = errs.iter().any(|e| {
                let mut it = e.splitn(3, ':');
                matches!((it.next(), it.next()), (Some(l), Some(c))
                    if l.trim().parse::<u32>().is_ok() && c.trim().parse::<u32>().is_ok())
            });
            if !located {
                return Err(format!(
                    "{label}\n  refused, but no message carries a `line:col:` span:\n    {}",
                    errs.join("\n    "),
                ));
            }
            if !errs.iter().any(|e| e.contains(frag)) {
                return Err(format!(
                    "{label}\n  refused, but for a DIFFERENT reason than this cell records.\n  \
                     expected a message containing {frag:?}, got:\n    {}",
                    errs.join("\n    "),
                ));
            }
            Ok(format!("{label:<52} REFUSES, located"))
        }
        Verdict::KnownGap { wi, expect } => {
            if errs.is_empty() {
                return Err(format!(
                    "{label}\n  THIS GAP HAS CLOSED — it now loads clean.\n  \
                     That is good news: change this cell's verdict to Verdict::Loads and \
                     close {wi} in the same commit.",
                ));
            }
            if !errs.iter().any(|e| e.contains(expect)) {
                return Err(format!(
                    "{label}\n  still refused, but not with the message {wi} records.\n  \
                     expected a message containing {expect:?}, got:\n    {}\n  \
                     Either the gap moved or a second defect is in front of it.",
                    errs.join("\n    "),
                ));
            }
            Ok(format!("{label:<52} KNOWN GAP ({wi})"))
        }
    }
}

/// Run a table of cells, reporting EVERY failure rather than the first — a sweep whose
/// point is to show which cells moved is useless if it stops at cell one.
fn run(cells: Vec<(String, String, Verdict)>) {
    let mut report = String::new();
    let mut failures: Vec<String> = Vec::new();
    for (label, body, want) in cells {
        match check(&label, &body, want) {
            Ok(line) => {
                let _ = writeln!(report, "  {line}");
            }
            Err(e) => failures.push(e),
        }
    }
    if !failures.is_empty() {
        panic!(
            "{} matrix cell(s) disagree with their recorded verdict:\n\n{}\n\nCells that held:\n{}",
            failures.len(),
            failures.join("\n\n"),
            report,
        );
    }
    println!("{report}");
}

// ── THE CALLBACK-BINDER SWEEP ────────────────────────────────────────────────

const MAP_MATCH_GAP: Verdict = Verdict::KnownGap {
    wi: "WI-20260829-9TGP7",
    expect: "expected ?Dst",
};

/// 60 cells: {find, filter, map, foldLeft} x {dot, unqualified, qualified} x
/// {constant, field dot, match destructure, nested call, dot call}.
///
/// 57 GREEN, 3 RED. The green is a CHARACTERIZATION rather than a null result: it is the
/// statement that WI-20260828-N2FHM's repair reached every one of these hosts in every
/// spelling, which is exactly what nobody could say when `find` was fixed and `filter`
/// was believed broken. The 3 red are `MAP_MATCH_GAP`, which this sweep FOUND — the
/// discovery the ticket was written to get, on the first run. Any cell that moves names
/// the host, the spelling and the body form that moved.
/// `Iterable.map`'s RESULT type parameter is not reconciled against a match arm's type.
///
/// THE SWEEP LOCALIZED THIS; IT DID NOT DISCOVER IT, and the first version of this note
/// claimed otherwise (found by /code-review). WI-20260829-9TGP7's original description,
/// written before this file existed, already records the cell verbatim —
/// `msgs.map(lambda m -> match m case message(i,f,r,s,b) -> b)` → "expected ?Dst, got
/// Text[Trust = ?_]". What is new here is the NEIGHBOURHOOD, which is what a sweep can
/// give and a single probe cannot:
///
///   map / {dot, unqualified, qualified} / match destructure   RED, `expected ?Dst, got Int64`
///   map / {…} / {constant, field dot, nested call, dot call}  GREEN  ⇒ not the callback binder
///   foldLeft / {…} / match destructure                        GREEN  ⇒ not "has a result param"
///                                                                      (`foldLeft[Acc]` has one)
///   find, filter / every body                                 GREEN  ⇒ not callbacks at large
///
/// THAT SET ANSWERS WI-20260829-9TGP7'S OPEN QUESTION. Its spelling (b),
/// `msgs.map(lambda m -> match m case message(…) -> b)` → "expected ?Dst, got
/// Text[Trust = ?_]", is the same cell. The ticket asks whether (b) is a CONSEQUENCE of
/// (a) — "if `Element` never grounds, the match arm has nothing to reconcile `?Dst`
/// against" — or independent. It is INDEPENDENT: `Element` grounds fine here, which the
/// green `map / field dot` cell says directly, and `?Dst` still fails. The two must be
/// fixed separately.
/// ONE TEST PER HOST rather than one for the table, so libtest runs them on separate
/// threads: every cell is an independent full-stdlib load, and 84 of them serialized cost
/// ~55s of wall time that nothing needed to be serial (found by /code-review). A failure
/// still names host / spelling / body, and `run` still reports every failing cell within
/// a host rather than stopping at the first.
fn sweep_host(host: &str) {
    let h = HOSTS
        .iter()
        .find(|h| h.name == host)
        .unwrap_or_else(|| panic!("no such host in the matrix: {host}"));
    let mut cells = Vec::new();
    // Cells the language cannot express, reported rather than silently absent — a sweep
    // that quietly drops what it cannot ask looks complete and is not.
    let mut skipped: Vec<String> = Vec::new();
    {
        for sp in [Spelling::Dot, Spelling::Unqualified, Spelling::Qualified] {
            for b in BODIES {
                let Some(raw) = b.expr(h.predicate) else {
                    skipped.push(format!("{} / {} / {}", h.name, sp.name(), b.name()));
                    continue;
                };
                let body_expr = if raw == "IDENTITY" { h.identity } else { raw };
                let cb = format!("lambda {} -> {}", h.binder, body_expr);
                // THE ONE RED ROW, and this sweep is what localized it. See
                // `MAP_MATCH_GAP` above.
                let want = match (h.name, b) {
                    ("map", Body::MatchDestructure) => MAP_MATCH_GAP,
                    _ => Verdict::Loads,
                };
                cells.push((
                    format!("{} / {} / {}", h.name, sp.name(), b.name()),
                    sp.call(h, &cb),
                    want,
                ));
            }
        }
    }
    // 3 spellings x 6 bodies, less the identity cells a PREDICATE host cannot express.
    let want_cells = if h.predicate { 15 } else { 18 };
    assert_eq!(
        cells.len(),
        want_cells,
        "{host}: 3 spellings x 6 bodies, less {} inexpressible",
        skipped.len()
    );
    if !skipped.is_empty() {
        println!("  not expressible ({}): {}", skipped.len(), skipped.join(", "));
    }
    run(cells);
}

#[test]
fn sweep_find() {
    sweep_host("find");
}

#[test]
fn sweep_filter() {
    sweep_host("filter");
}

#[test]
fn sweep_map() {
    sweep_host("map");
}

#[test]
fn sweep_fold_left() {
    sweep_host("foldLeft");
}

#[test]
fn sweep_fold_right() {
    sweep_host("foldRight");
}

/// THE TABLE IS THE POPULATION, and this is what says so: if a host is added to `HOSTS`
/// and no `sweep_*` test names it, its cells are never run and the sweep silently covers
/// less than it claims. Cheap, and it is the failure mode this whole file exists to
/// prevent one level up.
#[test]
fn every_host_has_a_sweep() {
    let swept = ["find", "filter", "map", "foldLeft", "foldRight"];
    let missing: Vec<&str> = HOSTS
        .iter()
        .map(|h| h.name)
        .filter(|n| !swept.contains(n))
        .collect();
    assert!(
        missing.is_empty(),
        "these hosts are in HOSTS but no sweep_* test runs them, so their cells never \
         execute: {missing:?} — add a `#[test] fn sweep_<host>()` and list it here",
    );
}

// ── THE CONSUMPTION TABLE ────────────────────────────────────────────────────

/// WHERE THE MEASURED GAP IS, and it is not where the tickets put it. `map` and `filter`
/// return the lazy `MappedStream` / `FilteredStream` carriers, so an EAGER consumer
/// refuses them — `xs.map(f).length()` is ordinary code that does not work. The four
/// probes behind WI-20260829-ARQ5X and WI-20260829-9TGP7 hit exactly this and read it as
/// a callback-dot defect, because they never ran the constant-callback row next to the
/// field-dot one.
///
/// SO EVERY GAP CELL HERE IS PAIRED WITH ITS CONTROL, and the pair is the finding: both
/// members refuse with the same message, which is what says the callback body is not
/// implicated. The two `let`-bound rows at the end are the other half — the same call,
/// unconsumed, loads.
#[test]
fn lazy_stream_consumption() {
    // WI-20260829-N01PY and NOT WI-20260829-ARQ5X, which is the item that DELIVERS this
    // file. A `KnownGap` contracts to fail when the gap closes so its WI can be closed in
    // the same commit; pointed at the delivering ticket it would name something already
    // Delivered, and the live defect would be tracked by nothing (found by /code-review).
    const GAP: Verdict = Verdict::KnownGap {
        wi: "WI-20260829-N01PY",
        expect: "expected List",
    };
    run(vec![
        (
            "length(map(...)) / field dot".into(),
            "length(xs.map(lambda r -> r.a))".into(),
            GAP,
        ),
        (
            "length(map(...)) / constant (CONTROL — same refusal ⇒ the dot is not it)".into(),
            "length(xs.map(lambda r -> 7))".into(),
            GAP,
        ),
        (
            "length(filter(...)) / field dot".into(),
            "length(xs.filter(lambda r -> r.flag))".into(),
            GAP,
        ),
        (
            "length(filter(...)) / constant (CONTROL)".into(),
            "length(xs.filter(lambda r -> true))".into(),
            GAP,
        ),
        // The contrast that localizes the gap to CONSUMPTION: the identical calls,
        // unconsumed, load clean. Without these two the table above would be
        // consistent with "map and filter are broken", which is what was believed.
        (
            "map(...) unconsumed (CONTRAST)".into(),
            "xs.map(lambda r -> r.a)".into(),
            Verdict::Loads,
        ),
        (
            "filter(...) unconsumed (CONTRAST)".into(),
            "xs.filter(lambda r -> r.flag)".into(),
            Verdict::Loads,
        ),
        // `find` is eager and returns an Option, so it composes with a consumer. It is
        // what attributes the gap to the LAZY carriers rather than to callbacks at large.
        (
            "find(...) into a consumer (CONTROL — eager host composes)".into(),
            "match xs.find(lambda r -> r.flag) case some(v) -> a_of(v) case none() -> 0".into(),
            Verdict::Loads,
        ),
    ]);
}

// ── THE HARNESS'S OWN CONTROLS ───────────────────────────────────────────────

/// EVERY VERDICT MUST BE ABLE TO FAIL, and nothing above proves that: the two tables are
/// all-passing by construction, so a `check` that returned `Ok` unconditionally — or a
/// `KnownGap` arm that forgot the closed-gap branch — would leave all 67 cells vacuous
/// and green forever. That is precisely the failure this file exists to prevent, so it
/// would be an odd thing to ship inside it.
///
/// Each case below hands `check` a verdict that is WRONG for its body and asserts it
/// rejects, and on the fragment of guidance the failure is supposed to carry. The
/// closed-gap case is the load-bearing one: it is the only thing that makes a `KnownGap`
/// cell tell the person who fixed the bug to flip the verdict and close the ticket,
/// which is the ticket's whole reason for having a third verdict.
#[test]
fn every_verdict_fails_when_it_should() {
    // A PERMANENTLY ILL-TYPED body, for every case below that needs one. It must not be
    // a program that fails because of a gap this file TRACKS: `length(xs.map(...))` was
    // used here first, and on the day WI-20260829-N01PY is fixed these controls would
    // have started failing with "a Loads cell whose program refuses must fail" — blaming
    // the harness, in the same run where the gap cells correctly report themselves
    // (found by /code-review). `nosuchname` is refused by construction and by nothing
    // anyone will ever repair.
    const ALWAYS_REFUSED: &str = "nosuchname(xs)";

    // A body that LOADS, recorded as a gap ⇒ "the gap closed, flip it".
    let closed = check(
        "self-test",
        "xs.map(lambda r -> r.a)",
        Verdict::KnownGap { wi: "WI-FAKE", expect: "unknown" },
    )
    .expect_err("a KnownGap whose program loads MUST fail — otherwise every gap cell is vacuous");
    assert!(
        closed.contains("THIS GAP HAS CLOSED") && closed.contains("WI-FAKE"),
        "a closed gap must say so and name its WI, got: {closed}"
    );

    // A body that REFUSES, recorded as loading ⇒ ordinary regression report.
    let regressed = check("self-test", ALWAYS_REFUSED, Verdict::Loads)
        .expect_err("a Loads cell whose program refuses must fail");
    assert!(
        regressed.contains("expected LOADS"),
        "got: {regressed}"
    );

    // A body that LOADS, recorded as refusing ⇒ the refusal went away.
    let no_refusal = check(
        "self-test",
        "xs.map(lambda r -> r.a)",
        Verdict::RefusesLocated("expected List"),
    )
    .expect_err("a RefusesLocated cell whose program loads must fail");
    assert!(no_refusal.contains("but it loaded clean"), "got: {no_refusal}");

    // A body that refuses for a DIFFERENT reason than recorded ⇒ not silently accepted.
    let wrong_reason = check(
        "self-test",
        ALWAYS_REFUSED,
        Verdict::RefusesLocated("a fragment that appears in no message"),
    )
    .expect_err("a cell must not accept a refusal it does not recognize");
    assert!(
        wrong_reason.contains("DIFFERENT reason"),
        "got: {wrong_reason}"
    );

    // And the positive control: a correctly-recorded cell still passes, so the four
    // rejections above are the verdicts doing their job and not `check` refusing
    // everything put in front of it.
    check("self-test", "xs.map(lambda r -> r.a)", Verdict::Loads)
        .expect("a correctly-recorded Loads cell must pass");
}

// ── REFUSALS THAT ARE CORRECT, AND THE AXIS THAT TURNED OUT NOT TO MATTER ────

/// A capability matrix that only ever records LOADS and KNOWN GAP is half a matrix: the
/// third verdict, "refused and it SHOULD be", is what stops a future change from
/// quietly accepting these — and until now no cell used it (found by /code-review), so
/// `Verdict::RefusesLocated` was exercised only by the harness self-test.
///
/// Each row is a refusal the repo INTENDS, with the located message that carries it. A
/// green row here means the refusal still fires AND still names a span; a red one means
/// either it stopped refusing (a silent-accept regression) or the diagnostic lost its
/// location, which is the difference between a usable error and `<unresolved receiver>`.
#[test]
fn refusals_that_should_stand() {
    run(vec![
        (
            "callback returns the wrong sort (predicate host fed a value)".into(),
            "xs.filter(lambda r -> r.a)".into(),
            Verdict::RefusesLocated("type mismatch"),
        ),
        (
            "callback reads a field the element does not have".into(),
            "xs.map(lambda r -> r.nosuchfield)".into(),
            Verdict::RefusesLocated("no such member"),
        ),
        (
            "host called with no callback at all".into(),
            "xs.map()".into(),
            Verdict::RefusesLocated("map"),
        ),
    ]);
}

/// THE AXIS THE TICKET ASKED FOR, MEASURED AND FOUND NOT TO SEPARATE ANYTHING — recorded
/// because "say what nothing covers" applies to axes as much as to guards.
///
/// WI-20260829-ARQ5X's feedback ended "the red cell has to come from the
/// label-parameterized receiver", on the strength of a guardians probe of mine that
/// reported `Iterable.map(msgs, lambda m -> m.body)` refused with `<unresolved
/// receiver>.body ... no such member`. THAT PROBE WAS WRONG: `good.anthill` imports
/// `{List, Error, External}` and not `Iterable`, so the qualified call named a sort the
/// file does not import and the refusal was about the missing import. With `Iterable`
/// imported the same substitution gives the ordinary consumption error
/// (WI-20260829-N01PY). /code-review caught it and measured the axis independently.
///
/// So the rows below carry the label parameter the guardians `Message[Trust]` has, and
/// they LOAD — in every spelling, exactly as the plain `Row` fixture does. The label
/// parameter separates nothing, which is why the main table does not carry it as an axis.
/// The one red cell it does produce is `map` + match destructure, which is already in the
/// sweep under the plain fixture — the same gap, not a new one.
#[test]
fn a_label_parameterized_receiver_changes_no_verdict() {
    const SRC: &str = r#"
namespace capmatrix_labelled
  import anthill.prelude.{String, Int64, List, Stream, Option, Iterable}
  import anthill.prelude.Iterable.{map, filter, find}
  enum Level
    entity Lo
    entity Hi
  end
  enum Txt
    import anthill.prelude.{String}
    sort Trust = ?
    entity txt(raw: String)
  end
  enum Msg
    import capmatrix_labelled.{Txt}
    sort Trust = ?
    entity message(body: Txt[Trust])
  end
  operation cell(ms: List[T = Msg[Trust = Lo]]) -> Int64 =
    let a = ms.map(lambda m -> m.body)
    let b = map(ms, lambda m -> m.body)
    let c = Iterable.map(ms, lambda m -> m.body)
    let d = ms.filter(lambda m -> true)
    let e = find(ms, lambda m -> true)
    42
end
"#;
    match crate::common::try_load_kb_with(SRC) {
        Ok(_) => {}
        Err(errs) => panic!(
            "a label-parameterized receiver must type its callback binder exactly as a \
             plain one does, in every spelling; got {} error(s):\n  {}",
            errs.len(),
            errs.join("\n  "),
        ),
    }
}
