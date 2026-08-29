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
//! THE VERDICTS. The ticket named three; two more were forced by cells that none of the
//! three could describe honestly, and each of the five FAILS when its state changes, so
//! the person who changes it is told to flip the cell and close the ticket in one commit:
//!   * [`Verdict::Loads`]             the capability works
//!   * [`Verdict::RefusesLocated`]    rejected, correctly, with a message naming a span
//!   * [`Verdict::RefusesUnlocated`]  rejected correctly, but the message has NO span —
//!                                    a usable refusal and an unusable diagnostic are not
//!                                    the same state (WI-20260829-6RBPD)
//!   * [`Verdict::KnownGap`]          rejected TODAY and should not be
//!   * [`Verdict::SilentlyAccepted`]  ACCEPTED today and should not be — the most
//!                                    dangerous kind, because a refusal that never comes
//!                                    is invisible. WI-20260828-N2FHM was this shape: it
//!                                    loaded clean and died at eval uncatchably.
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
//! SLICE 2 — WHAT SITS IN THE POSITION x HOW ITS TYPE IS REACHED, the ticket's other axis
//! pair. Slice 1 swept one POSITION (a lambda callback) across its hosts; slice 2 sweeps
//! one position kind across the ROUTES its type can arrive by. The bare operation name
//! goes first because three delivered items live in that row — WI-20260828-2TMB5, -5NSZY,
//! -8Q0Q5 — each having found ONE route by hand, none able to say what the others did.
//! `a_bare_operation_name_across_its_routes` is those three plus the routes nobody had
//! asked about, and `a_hinted_literal_never_checks_its_elements` is the other side of its
//! two red cells: the hint they need cannot be supplied while the literal OVERWRITES its
//! elements instead of checking them (WI-20260826-7JDWY).
//!
//! WHAT SLICE 2 TURNED UP that no ticket had: a lambda cannot appear inside a list
//! literal AT ALL (it does not parse, with or without parentheses — so "write a lambda
//! instead" is not available as the repair for the bare-name cells), and every op-return
//! type mismatch is UNLOCATED while op-arg and dot-dispatch mismatches are located
//! (WI-20260829-6RBPD, found by a cell of mine failing an assertion I expected to hold).
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
    /// Refused, CORRECTLY, but the diagnostic carries no `line:col` span. The refusal is
    /// right and the message is not usable — a distinct state from all of the above, and
    /// the reason it is a verdict rather than a relaxed `RefusesLocated`: silently
    /// dropping the located requirement for the one path that cannot meet it would let
    /// every other path quietly lose its span too. FAILS when a span appears, which is
    /// the signal to flip the cell to `RefusesLocated` and close the WI.
    RefusesUnlocated {
        wi: &'static str,
        /// A fragment the message must contain. Every OTHER refusing verdict carries one
        /// so a cell cannot silently start failing for a new reason; without it this
        /// variant asserted only "≥1 error, none located", which any span-less refusal
        /// satisfies (found by /code-review).
        expect: &'static str,
    },
    /// ACCEPTED today and should NOT be — a SILENT HOLE. The ticket's three verdicts have
    /// no way to say this, and it is the most dangerous cell kind there is: a refusal that
    /// never comes is invisible, where a refusal that should not have come at least tells
    /// somebody. WI-20260828-N2FHM was exactly this shape — a program that loaded clean and
    /// died at eval with an `Internal` no handler could catch.
    ///
    /// Asserts the program LOADS, so it fails the day the hole is closed and the cell can
    /// be flipped to `RefusesLocated` with the WI closed in the same commit.
    SilentlyAccepted {
        wi: &'static str,
        /// What the loader SHOULD have said, for whoever closes it.
        should_say: &'static str,
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
    /// Sort to name in the QUALIFIED spelling.
    ///
    /// THIS IS NOT THE DECLARATION THE DOT SPELLING REACHES, and the difference is the
    /// point of `each_spelling_resolves_to_a_named_declaration`: `xs.map(f)` resolves to
    /// `FiniteCollection.map` while `map(xs, f)` and `Iterable.map(xs, f)` both reach
    /// `Iterable.map`, and `xs.find(f)` reaches `Stream.find` where the named forms reach
    /// `Iterable.find`. So the spelling axis co-varies with WHICH OPERATION is measured,
    /// and a defect confined to one declaration would present as a spelling defect —
    /// exactly the mis-attribution this file exists to prevent (found by /code-review).
    /// The resolution is pinned per cell so the confound is measured rather than hidden.
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

/// Does a rendered diagnostic carry a `line:col` prefix?
///
/// FORMAT-COUPLED ON PURPOSE, and the coupling is narrow: `try_load_kb_with` builds
/// path-less `ParsedFile`s, so `render_located` emits `line:col: message` with no `path:`
/// in front. A table that moved to `try_load_kb_with_named_files` would see `path:line:col`
/// and this would read every located error as unlocated — so if a cell ever loads from a
/// named file, this predicate is what has to change with it.
fn is_located(msg: &str) -> bool {
    let mut it = msg.splitn(3, ':');
    matches!(
        (it.next(), it.next()),
        (Some(l), Some(c)) if l.trim().parse::<u32>().is_ok() && c.trim().parse::<u32>().is_ok()
    )
}

/// Load one cell and check it against its verdict. Returns a one-line report either way,
/// and the failure message says what to do rather than only what happened.
fn check(label: &str, body: &str, want: Verdict) -> Result<String, String> {
    check_src(label, &program(body), want)
}

/// The verdict logic, over an already-built program — shared by the slice-1 tables (which
/// build through [`program`]) and the slice-2 ones (through [`route_program`]), so a
/// verdict means the same thing in both and there is one place to change it.
fn check_src(label: &str, src: &str, want: Verdict) -> Result<String, String> {
    let src = src.to_string();
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
            // ONE error must satisfy BOTH, not one each. Checked separately, a cell stays
            // green when the diagnostic it is ABOUT loses its span and some unrelated
            // follow-on error happens to carry one — which is precisely the state
            // `RefusesUnlocated` exists to distinguish (found by /code-review).
            if errs.iter().any(|e| e.contains(frag) && is_located(e)) {
                return Ok(format!("{label:<52} REFUSES, located"));
            }
            if !errs.iter().any(|e| is_located(e)) {
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
            Err(format!(
                "{label}\n  the message this cell records and the LOCATED message are \
                 different errors — the diagnostic under test has lost its span:\n    {}",
                errs.join("\n    "),
            ))
        }
        Verdict::RefusesUnlocated { wi, expect } => {
            if errs.is_empty() {
                return Err(format!("{label}\n  expected a REFUSAL, but it loaded clean."));
            }
            // CORRELATED, for the same reason the `RefusesLocated` arm above is: asked
            // over ALL errors, an unrelated located companion diagnostic would trip this
            // and tell the reader to close {wi} — a live ticket — on the strength of a
            // message that is not the one under test (found by /code-review, which had
            // already caught the same asymmetry one arm up; I fixed the site it named and
            // left this one).
            if errs.iter().any(|e| e.contains(expect) && is_located(e)) {
                return Err(format!(
                    "{label}\n  THIS DIAGNOSTIC IS NOW LOCATED:\n    {}\n  \
                     That is good news: change this cell's verdict to \
                     Verdict::RefusesLocated with a message fragment, and close {wi} in \
                     the same commit.",
                    errs.join("\n    "),
                ));
            }
            if !errs.iter().any(|e| e.contains(expect)) {
                return Err(format!(
                    "{label}\n  refused and unlocated, but for a DIFFERENT reason than \
                     this cell records.\n  expected a message containing {expect:?}, got:\n    {}",
                    errs.join("\n    "),
                ));
            }
            Ok(format!("{label:<52} REFUSES, unlocated ({wi})"))
        }
        Verdict::SilentlyAccepted { wi, should_say } => {
            if errs.is_empty() {
                return Ok(format!("{label:<52} SILENTLY ACCEPTED ({wi})"));
            }
            Err(format!(
                "{label}\n  THIS HOLE HAS CLOSED — it is now refused:\n    {}\n  \
                 That is good news: this cell recorded that the loader should say \
                 {should_say:?}. Change its verdict to Verdict::RefusesLocated and close \
                 {wi} in the same commit.",
                errs.join("\n    "),
            ))
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
    run_with(cells, program)
}

/// [`run`] over an arbitrary program builder — the slice-1 tables pass [`program`], the
/// slice-2 ones [`route_program`]. ONE implementation, because the first cut had two that
/// differed only in the builder and had already drifted: the copy re-ran the parse check
/// `check_src` performs and rendered its failure differently, dropping the source dump
/// (found by /code-review). A change to the reporting here now reaches every table.
fn run_with(cells: Vec<(String, String, Verdict)>, build: fn(&str) -> String) {
    let mut report = String::new();
    let mut failures: Vec<String> = Vec::new();
    for (label, body, want) in cells {
        match check_src(&label, &build(&body), want) {
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

/// `Iterable.map`'s RESULT type parameter is not reconciled against a match arm's type
/// — the one red row of the sweep below, and the gap WI-20260829-9TGP7 tracks.
const MAP_MATCH_GAP: Verdict = Verdict::KnownGap {
    wi: "WI-20260829-9TGP7",
    expect: "expected ?Dst",
};

/// 84 cells: {find, filter, map, foldLeft, foldRight} x {dot, unqualified, qualified} x
/// {constant, identity, field dot, match destructure, nested call, dot call}, less the 6
/// identity-under-a-predicate-host combinations the language cannot express.
///
/// 81 GREEN, 3 RED. The green is a CHARACTERIZATION rather than a null result — but read
/// it as "every one of these HOSTS AND DECLARATIONS", not "every host in every spelling".
/// The two are different because the spelling axis co-varies with the declaration it
/// resolves to (`xs.map` reaches `FiniteCollection.map`, `map(xs, …)` reaches
/// `Iterable.map`, `xs.find` reaches `Stream.find`), which
/// `each_spelling_resolves_to_a_named_declaration` pins. The first version of this note
/// claimed the spelling reading and /code-review measured it false; what the sweep
/// actually says is that N2FHM's repair reached every one of the SEVEN declarations these
/// cells touch — which is still what nobody could say when `find` was fixed and `filter`
/// was believed broken, and is a wider statement than the one it replaces. The 3 red are `MAP_MATCH_GAP`, which this sweep FOUND — the
/// discovery the ticket was written to get, on the first run. Any cell that moves names
/// the host, the spelling and the body form that moved.
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
/// less than it claims.
///
/// AND `swept` IS THE WEAK LINK, stated rather than pretended away (found by
/// /code-review): it is hand-maintained, so someone who adds a `Host` and dutifully adds
/// its name here but forgets the `#[test] fn sweep_<host>()` still gets a green guard and
/// 18 cells that never execute. Deriving the list from the test functions would close it
/// and needs a registry this file does not otherwise want; until then the guard catches
/// the common half (a `Host` added and nothing else touched) and this note names the half
/// it does not.
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
/// `KnownGap` arm that forgot the closed-gap branch — would leave all 110 table cells vacuous
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

    // A body that REFUSES, recorded as silently accepted ⇒ "the hole closed, flip it".
    let hole_closed = check(
        "self-test",
        ALWAYS_REFUSED,
        Verdict::SilentlyAccepted { wi: "WI-FAKE", should_say: "something" },
    )
    .expect_err("a SilentlyAccepted cell whose program is refused MUST fail — otherwise a \
                 closed hole is never noticed");
    assert!(
        hole_closed.contains("THIS HOLE HAS CLOSED") && hole_closed.contains("WI-FAKE"),
        "a closed hole must say so and name its WI, got: {hole_closed}"
    );

    // A LOCATED refusal recorded as unlocated ⇒ "it gained a span, flip it". `xs.map()`
    // is an op-arg-shaped error, which the span machinery does cover.
    let now_located = check(
        "self-test",
        "xs.map()",
        Verdict::RefusesUnlocated { wi: "WI-FAKE", expect: "no argument fills parameter" },
    )
    .expect_err("a RefusesUnlocated cell whose diagnostic HAS a span must fail");
    assert!(
        now_located.contains("NOW LOCATED") && now_located.contains("WI-FAKE"),
        "a newly-located diagnostic must say so and name its WI, got: {now_located}"
    );

    // And a program that LOADS is not an unlocated refusal either.
    check(
        "self-test",
        "xs.map(lambda r -> r.a)",
        Verdict::RefusesUnlocated { wi: "WI-FAKE", expect: "anything" },
    )
    .expect_err("a RefusesUnlocated cell whose program loads must fail");

    // A refusal recorded as unlocated with a fragment that does NOT appear. This is the
    // branch that matters most: `RefusesUnlocated::expect` exists because without it the
    // variant asserted only "≥1 error, none located", which any span-less refusal
    // satisfies. If that check regressed to a no-op the `{1}` cell and the whole verdict
    // would go vacuously green and nothing else in the file would notice
    // (found by /code-review).
    // Through `route_program`, which takes a whole declaration — `program` wraps its
    // argument in an operation body, and this case needs an operation of its own to get
    // an (unlocated) op-return error.
    let unlocated_wrong_reason = check_src(
        "self-test",
        &route_program("  operation z() -> Int64 = \"x\""),
        Verdict::RefusesUnlocated { wi: "WI-FAKE", expect: "a fragment in no message" },
    )
    .expect_err("a RefusesUnlocated cell whose message does not match `expect` must fail");
    assert!(
        unlocated_wrong_reason.contains("DIFFERENT reason"),
        "got: {unlocated_wrong_reason}"
    );

    // A KnownGap whose refusal is real but carries a different message than recorded.
    let gap_wrong_reason = check(
        "self-test",
        ALWAYS_REFUSED,
        Verdict::KnownGap { wi: "WI-FAKE", expect: "a fragment in no message" },
    )
    .expect_err("a KnownGap cell must not accept a refusal it does not recognize");
    assert!(
        gap_wrong_reason.contains("not with the message"),
        "got: {gap_wrong_reason}"
    );

    // A RefusesLocated cell over a refusal that carries NO span at all.
    let never_located = check_src(
        "self-test",
        &route_program("  operation z() -> Int64 = \"x\""),
        Verdict::RefusesLocated("(op-return)"),
    )
    .expect_err("a RefusesLocated cell over an unlocated diagnostic must fail");
    assert!(
        never_located.contains("no message carries"),
        "got: {never_located}"
    );

    // The positive controls: correctly-recorded cells still pass, so the rejections above
    // are the verdicts doing their job and not `check` refusing everything put in front
    // of it. One per verdict that has a witness in this file.
    check("self-test", "xs.map(lambda r -> r.a)", Verdict::Loads)
        .expect("a correctly-recorded Loads cell must pass");
    check("self-test", "xs.map()", Verdict::RefusesLocated("map"))
        .expect("a correctly-recorded RefusesLocated cell must pass");
    // NOT `length(xs.map(...))`, which is the live WI-20260829-N01PY gap: the day it is
    // fixed this control would panic with "a correctly-recorded KnownGap cell must pass"
    // and send its fixer to a self-test that has no defect — the exact rule stated 30
    // lines above, which the first cut of this line broke (found by /code-review).
    check(
        "self-test",
        ALWAYS_REFUSED,
        Verdict::KnownGap { wi: "WI-FAKE", expect: "unknown functor" },
    )
    .expect("a correctly-recorded KnownGap cell must pass");
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
            // NOT "type mismatch": EVERY typer diagnostic in this loader begins with it,
            // so that fragment discriminates nothing and the cell would stay green on an
            // unrelated refusal — including the `<unresolved receiver>` artifact the
            // module header is written about (found by /code-review).
            Verdict::RefusesLocated("expected Row -> Bool, got Row -> Int64"),
        ),
        (
            "callback reads a field the element does not have".into(),
            "xs.map(lambda r -> r.nosuchfield)".into(),
            Verdict::RefusesLocated("no such member"),
        ),
        (
            "host called with no callback at all".into(),
            "xs.map()".into(),
            Verdict::RefusesLocated("no argument fills parameter"),
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

// ═══ SLICE 2 — WHAT SITS IN THE POSITION x HOW ITS TYPE IS REACHED ══════════
//
// The ticket's second axis pair. Slice 1 swept ONE position (a lambda callback) across
// its hosts; this sweeps ONE POSITION KIND across the ROUTES by which its type can
// arrive. The bare operation name is the row that earns going first: three delivered
// items live in it (WI-20260828-2TMB5, -5NSZY, -8Q0Q5), each having found one route by
// hand, and none of them could say what the other routes did.

/// A program for the slice-2 rows: one operation, one arrow-typed entity, and the
/// several slots a bare name can land in. Shared so a row differs from its neighbours in
/// the ROUTE and nothing else.
fn route_program(body: &str) -> String {
    format!(
        r#"
namespace capmatrix_routes
  import anthill.prelude.{{List, Set, Int64, Bool, String, Option, Function}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.List.{{cons, nil}}
  operation inc(x: Int64) -> Int64 = x + 1
  sort ArrowField
    import anthill.prelude.{{Int64}}
    entity af(f: (Int64) -> Int64)
  end
  sort PlainField
    import anthill.prelude.{{Int64}}
    entity pf(v: Int64)
  end
  operation take_fn(f: (Int64) -> Int64) -> Int64 = f(41)
  operation take_int(v: Int64) -> Int64 = v
  operation apply_it(o: Option[T = Function[A = Int64, B = Int64]], v: Int64) -> Int64 = v
  operation head_apply(fs: List[T = Function[A = Int64, B = Int64]], v: Int64) -> Int64 = v
  operation set_apply(fs: Set[T = Function[A = Int64, B = Int64]], v: Int64) -> Int64 = v
  operation takes_list(s: List[T = Int64]) -> Int64 = 1
  operation takes_set(s: Set[T = Int64]) -> Int64 = 1
{body}
end
"#
    )
}

/// Run a slice-2 table — [`run_with`] over [`route_program`].
fn run_routes(cells: Vec<(String, String, Verdict)>) {
    run_with(cells, route_program)
}

/// A BARE OPERATION NAME, across every route by which the arrow it must lift against can
/// (or cannot) reach it. `inc(x: Int64) -> Int64` in every cell; only the SLOT changes.
///
/// WHAT EACH ROUTE COST TO LEARN, and why the row is worth having: WI-20260828-8Q0Q5
/// found routes 1-2, WI-20260828-2TMB5 found 3-4 (both were SILENT ACCEPTS before it —
/// `plain(inc)` loaded clean because the name took the zero-arg-call reading and typed as
/// its RETURN), WI-20260828-5NSZY found 5 and left 6-7 unreached on purpose. Each was a
/// separate discovery by hand; together they are one row of a table.
#[test]
fn a_bare_operation_name_across_its_routes() {
    // The list/set-literal routes. WI-20260828-5NSZY declined to supply the hint here and
    // said why: `TypeBuildFrame::ListLit` takes `element_hint` as the element type
    // UNCONDITIONALLY, so a hint would OVERWRITE the elements rather than check them —
    // trading a correct refusal for a silent accept. The hole that makes it unsafe is
    // WI-20260826-7JDWY, pinned by `a_hinted_literal_never_checks_its_elements` below;
    // these two cells and those are the same defect seen from both sides, which is the
    // kind of thing a matrix shows and two separate WI files do not.
    const LITERAL_GAP: Verdict = Verdict::KnownGap {
        wi: "WI-20260826-7JDWY",
        expect: "supplies no function type to lift it against",
    };
    run_routes(vec![
        (
            "1 operation param, ARROW slot".into(),
            "  operation c() -> Int64 = take_fn(inc)".into(),
            Verdict::Loads,
        ),
        (
            "2 entity FIELD, arrow-typed".into(),
            "  operation c() -> ArrowField = af(inc)".into(),
            Verdict::Loads,
        ),
        (
            "3 operation param, NON-callable (refusal is CORRECT)".into(),
            "  operation c() -> Int64 = take_int(inc)".into(),
            Verdict::RefusesLocated("supplies no function type to lift it against"),
        ),
        (
            "4 entity field, NON-callable (refusal is CORRECT)".into(),
            "  operation c() -> PlainField = pf(inc)".into(),
            Verdict::RefusesLocated("supplies no function type to lift it against"),
        ),
        (
            "5 nested in a CONSTRUCTOR argument, arrow one level out".into(),
            "  operation c() -> Int64 = apply_it(some(inc), 41)".into(),
            Verdict::Loads,
        ),
        (
            "6 inside a LIST literal".into(),
            "  operation c() -> Int64 = head_apply([inc], 41)".into(),
            LITERAL_GAP,
        ),
        (
            "7 inside a SET literal".into(),
            "  operation c() -> Int64 = set_apply({inc}, 41)".into(),
            LITERAL_GAP,
        ),
        (
            // THE CONTROL FOR 6 AND 7, and it is what makes them a gap rather than a
            // property of bare names in collections: the SAME name, the same declared
            // slot, spelled through the constructors the literal desugars to — accepted.
            "8 CONTROL — the desugared twin `cons(inc, nil())`".into(),
            "  operation c() -> Int64 = head_apply(cons(inc, nil()), 41)".into(),
            Verdict::Loads,
        ),
    ]);
}

/// A LITERAL IS CHECKED ON THE ARGUMENT ROUTE AND OVERWRITTEN ON THE RETURN-HINT ROUTE —
/// which is narrower and more useful than "a hinted literal never checks its elements",
/// the claim this table carried first (corrected by /code-review, which measured the
/// argument route I had never run).
///
/// `TypeBuildFrame::ListLit` takes `element_hint` as the element type UNCONDITIONALLY and
/// walks the elements only to merge effects, so where a hint arrives it OVERWRITES the
/// literal instead of checking it (WI-20260826-7JDWY). But the hint only arrives on some
/// routes: an operation's declared RETURN pushes one down, and an operation's declared
/// PARAMETER does not — so an argument-position literal is inferred bottom-up and its
/// elements are checked normally. The two halves are the point of the table:
///
///   operation c() -> List[T = Int64] = ["x"]   LOADS      ⇐ hint overwrites
///   takes_list(["x"])                          REFUSED, `got List[T = String]`
///
/// Same literal, same wrong element, opposite verdicts by ROUTE. Without the second row
/// the first reads as "literals are unchecked", which would send whoever fixes 7JDWY
/// looking in the wrong place.
#[test]
fn a_literal_is_checked_on_one_route_and_overwritten_on_the_other() {
    const HOLE: Verdict = Verdict::SilentlyAccepted {
        wi: "WI-20260826-7JDWY",
        should_say: "type mismatch: expected Int64, got String",
    };
    run_routes(vec![
        // ── the RETURN-HINT route: the hint overwrites, so nothing is checked ──
        (
            "return hint / list literal, ONE wrong element".into(),
            "  operation c() -> List[T = Int64] = [\"x\"]".into(),
            HOLE,
        ),
        (
            "return hint / list literal, TWO wrong elements".into(),
            "  operation c() -> List[T = Int64] = [\"x\", \"y\"]".into(),
            HOLE,
        ),
        (
            "return hint / set literal, TWO wrong elements (7JDWY's Set twin)".into(),
            "  operation c() -> Set[T = Int64] = {\"x\", \"y\"}".into(),
            HOLE,
        ),
        (
            // NOT a set-literal row, and the confusion is worth recording where someone
            // will meet the message. On THIS route `{1}` is read as a braced expression
            // yielding `Int64`, which is why it refuses against `Set[T = Int64]`. The
            // claim is route-specific: in an ARGUMENT slot `{41}` IS a one-element set
            // literal (row below), so the general reading "one-element braces are never a
            // set literal" — which this comment asserted first — is false.
            "return hint / one-element braces read as a BRACED EXPRESSION".into(),
            "  operation c() -> Set[T = Int64] = {1}".into(),
            Verdict::RefusesUnlocated {
                wi: "WI-20260829-6RBPD",
                expect: "(op-return)",
            },
        ),
        // ── the ARGUMENT route: no hint is pushed, so elements ARE checked ──
        //
        // THESE ARE THE ROWS THAT MAKE THE TABLE A MEASUREMENT. Each is the same literal
        // and the same wrong element as a row above, in the position that behaves
        // differently; together they locate the hole in the ROUTE rather than in literals.
        (
            "arg route / list literal, wrong element (CHECKED — the discriminator)".into(),
            "  operation c() -> Int64 = takes_list([\"x\"])".into(),
            Verdict::RefusesLocated("got List[T = String]"),
        ),
        (
            "arg route / set literal, wrong element (CHECKED)".into(),
            "  operation c() -> Int64 = takes_set({\"x\"})".into(),
            Verdict::RefusesLocated("got Set[T = String]"),
        ),
        (
            // And one-element braces DO make a set here — the counterexample to the
            // general claim, kept as its own row so the correction cannot be lost.
            "arg route / one-element braces ARE a set literal".into(),
            "  operation c() -> Int64 = takes_set({41})".into(),
            Verdict::Loads,
        ),
        (
            "arg route / CONTROL — elements that agree".into(),
            "  operation c() -> Int64 = takes_list([1])".into(),
            Verdict::Loads,
        ),
    ]);
}

/// A LAMBDA CANNOT APPEAR INSIDE A LIST LITERAL AT ALL — it does not PARSE, with or
/// without parentheses. Found by this slice while building the control for route 6.
///
/// It matters for the route table above: the natural repair for "a bare name in a list
/// literal is refused" is "write a lambda instead", and that advice is unavailable here.
/// Both spellings are recorded because the parenthesized one is what a reader would try
/// next, and it fails differently (`syntax error near 'lambda x -> x + 1'` against
/// `near 'lambda'`), which is the kind of detail that decides whether someone thinks they
/// have a syntax slip or a missing capability.
///
/// NOT a `Verdict` row: these are PARSE failures, and every verdict in this file is about
/// what the LOADER decides. Asserting the parse directly keeps that line clean.
#[test]
fn a_lambda_inside_a_list_literal_does_not_parse() {
    // The DISTINGUISHING token per row, not just "lambda" for both: the doc records that
    // the two spellings fail differently, and asserting only the common substring would
    // let that recorded distinction become false while the test stayed green
    // (found by /code-review).
    for (name, body, want) in [
        ("bare", "  operation c() -> Int64 = head_apply([lambda x -> x + 1], 41)", "near `lambda`"),
        (
            "parenthesized",
            "  operation c() -> Int64 = head_apply([(lambda x -> x + 1)], 41)",
            "near `lambda x -> x + 1`",
        ),
    ] {
        let src = route_program(body);
        let errs = anthill_core::parse::parse(&src)
            .err()
            .unwrap_or_else(|| panic!(
                "a {name} lambda inside a list literal now PARSES. If that is intended, \
                 move this case into `a_bare_operation_name_across_its_routes` as a \
                 load-verdict row and say what it types as."
            ));
        assert!(
            errs.iter().any(|e| e.message.contains(want)),
            "the {name} spelling must still fail with {want:?} — the two spellings failing \
             differently is what this case records; got: {:?}",
            errs.iter().map(|e| e.message.clone()).collect::<Vec<_>>(),
        );
    }
}

/// AN OP-RETURN MISMATCH CARRIES NO SPAN, while an op-arg mismatch and a dot-dispatch
/// miss both do — WI-20260829-6RBPD, surfaced by the braced-expression cell above failing
/// a `RefusesLocated` assertion I had written expecting it to hold.
///
/// The pairing is the whole content: two unlocated rows beside two located ones, through
/// the same loader, so the row says "this one path does not use the span machinery"
/// rather than "spans are missing". Whoever fixes it has the control here — the located
/// pair must stay located, since it is a change to one raise site and not to the plumbing.
///
/// `operation c() -> Int64 = "x"` is about as ordinary as a type error gets, and in a
/// file of any size the author is told only the operation's name.
#[test]
fn an_op_return_mismatch_carries_no_span() {
    fn errors_for(body: &str) -> Vec<String> {
        let src = format!(
            "\nnamespace capmatrix_spans\n  import anthill.prelude.{{Int64, String, Set}}\n  {body}\nend\n"
        );
        crate::common::try_load_kb_with(&src)
            .err()
            .unwrap_or_else(|| panic!("this program must be refused: {body}"))
    }

    for body in [
        "operation c() -> Int64 = \"x\"",
        "operation c() -> Set[T = Int64] = {1}",
    ] {
        let errs = errors_for(body);
        // The MESSAGE is checked, not just the absence of a span: without this, any
        // span-less refusal for any other reason satisfies the row, and the ticket's
        // central claim — that it is the OP-RETURN path specifically — could silently
        // become untrue while the test stayed green (found by /code-review).
        // BOTH HALVES OVER THE SAME MESSAGE. Asked independently, a located companion
        // diagnostic satisfies the second while the op-return error stays span-less, and
        // the row reds telling its reader to close a live ticket (found by /code-review).
        let op_return: Vec<&String> = errs.iter().filter(|e| e.contains("(op-return)")).collect();
        assert!(
            !op_return.is_empty(),
            "this row is about the OP-RETURN path, but nothing here is one:\n  {body}\n  {}",
            errs.join("\n  "),
        );
        assert!(
            !op_return.iter().any(|e| is_located(e)),
            "WI-20260829-6RBPD says an op-return mismatch carries no span, but this one \
             DOES — good news: flip this row and the braced-expression cell above to \
             located, and close the ticket.\n  {body}\n  {}",
            errs.join("\n  "),
        );
    }

    // THE CONTROL, and it is what makes the rows above a defect in one raise site rather
    // than a statement about the loader: the span machinery works everywhere else.
    // The fragment is checked here too, and correlated with the span: without it the
    // control passes on ANY located diagnostic these programs happen to emit, and "the
    // span machinery works everywhere else" stops being measured — the same weakness the
    // comment above fixes for the unlocated rows (found by /code-review).
    for (body, frag) in [
        (
            "operation d(v: Int64) -> Int64 = v\n  operation c() -> Int64 = d(\"x\")",
            "expected Int64, got String",
        ),
        ("operation c() -> Int64 = (1).nosuch", "no such member"),
    ] {
        let errs = errors_for(body);
        assert!(
            errs.iter().any(|e| e.contains(frag) && is_located(e)),
            "this diagnostic has LOST its span — the op-arg and dot paths must stay \
             located, and it is THIS message that must carry it ({frag:?}).\n  {body}\n  {}",
            errs.join("\n  "),
        );
    }
}

/// WHICH DECLARATION EACH SPELLING ACTUALLY REACHES — the axis the sweep co-varies with
/// and did not name until /code-review measured it.
///
/// `Spelling` looks like it varies one thing. It does not: the dot form dispatches on the
/// receiver's carrier and lands on a DIFFERENT operation than the named forms, so three of
/// the five hosts measure two declarations across their columns:
///
///   xs.map(f)      -> FiniteCollection.map      map(xs,f) / Iterable.map(xs,f) -> Iterable.map
///   xs.filter(p)   -> FiniteCollection.filter   filter(xs,p) / Iterable.filter -> Iterable.filter
///   xs.find(p)     -> Stream.find               find(xs,p)   / Iterable.find   -> Iterable.find
///   xs.foldLeft(…) -> List.foldLeft             both named forms                -> List.foldLeft
///
/// WHY IT MATTERS, and it is this file's own subject turned on itself: a defect confined
/// to `Iterable.map` would red the unqualified and qualified columns and leave the dot
/// column green, and a reader would call that a SPELLING defect. That is the N2FHM
/// mis-attribution — the thing the module header says this file exists to prevent —
/// reproduced by the fixture's own axis. Pinning the resolution converts an invisible
/// confound into a measured fact: if a spelling starts resolving elsewhere, this reds.
///
/// HOW IT IS READ: an arity error names the parameter list it checked against, so calling
/// each spelling with one argument too few makes the loader report the declaration it
/// resolved to. That is a diagnostic detail rather than a language guarantee, so if the
/// arity message stops naming the declaration this test says so plainly rather than
/// silently measuring nothing.
#[test]
fn each_spelling_resolves_to_a_named_declaration() {
    let rows: &[(&str, Spelling, &str)] = &[
        ("map", Spelling::Dot, "anthill.prelude.FiniteCollection.map"),
        ("map", Spelling::Unqualified, "anthill.prelude.Iterable.map"),
        ("map", Spelling::Qualified, "anthill.prelude.Iterable.map"),
        ("filter", Spelling::Dot, "anthill.prelude.FiniteCollection.filter"),
        ("filter", Spelling::Unqualified, "anthill.prelude.Iterable.filter"),
        ("filter", Spelling::Qualified, "anthill.prelude.Iterable.filter"),
        ("find", Spelling::Dot, "anthill.prelude.Stream.find"),
        ("find", Spelling::Unqualified, "anthill.prelude.Iterable.find"),
        ("find", Spelling::Qualified, "anthill.prelude.Iterable.find"),
        ("foldLeft", Spelling::Dot, "anthill.prelude.List.foldLeft"),
        ("foldLeft", Spelling::Unqualified, "anthill.prelude.List.foldLeft"),
        ("foldRight", Spelling::Dot, "anthill.prelude.List.foldRight"),
        ("foldRight", Spelling::Unqualified, "anthill.prelude.List.foldRight"),
        // The QUALIFIED fold columns, missing from the first cut while the doc table above
        // asserted them (found by /code-review). Without them, `List.foldLeft(xs, …)`
        // could start resolving elsewhere and 12 sweep cells would silently change which
        // declaration they measure with this guard still green — the exact confound the
        // test exists to rule out.
        ("foldLeft", Spelling::Qualified, "anthill.prelude.List.foldLeft"),
        ("foldRight", Spelling::Qualified, "anthill.prelude.List.foldRight"),
    ];
    // EVERY COLUMN THE SWEEP RUNS, checked rather than assumed: a host added to `HOSTS`
    // with no row here would have its declarations unpinned.
    assert_eq!(
        rows.len(),
        HOSTS.len() * 3,
        "this table must cover every host x spelling column the sweep runs ({} hosts x 3), \
         or some columns' declarations go unpinned",
        HOSTS.len(),
    );
    let mut wrong: Vec<String> = Vec::new();
    for (host, sp, want_decl) in rows {
        let h = HOSTS.iter().find(|h| h.name == *host).expect("host in HOSTS");
        // The callback is omitted, so the loader reports an arity error naming the
        // parameter list it resolved against. `seed` is dropped too for the folds, which
        // still leaves the call short by at least one argument.
        let call = match sp {
            Spelling::Dot => format!("xs.{}()", h.name),
            Spelling::Unqualified => format!("{}(xs)", h.name),
            Spelling::Qualified => format!("{}.{}(xs)", h.qualifier, h.name),
        };
        let errs = match crate::common::try_load_kb_with(&program(&call)) {
            Ok(_) => {
                wrong.push(format!("{host} / {} — expected an arity error, but it LOADED", sp.name()));
                continue;
            }
            Err(e) => e,
        };
        if !errs.iter().any(|e| e.contains("arity")) {
            wrong.push(format!(
                "{host} / {} — no arity error, so this test can no longer read the \
                 resolved declaration and is measuring nothing:\n    {}",
                sp.name(),
                errs.join("\n    "),
            ));
            continue;
        }
        if !errs.iter().any(|e| e.contains(want_decl)) {
            wrong.push(format!(
                "{host} / {} now resolves ELSEWHERE — expected {want_decl}, got:\n    {}",
                sp.name(),
                errs.join("\n    "),
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "the spelling→declaration map has moved, so the sweep's columns no longer measure \
         what its doc says they do — update this table AND the note on `Host::qualifier`:\n\n{}",
        wrong.join("\n\n"),
    );
}
