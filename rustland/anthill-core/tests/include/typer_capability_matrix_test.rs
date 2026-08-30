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
//! Byte-identical. The dot was never what was refused. Three separate probe sets (two in
//! the tickets, one in my first attempt to re-measure them) made that same
//! misattribution, because none ran the dull row next to the interesting one. So
//! [`Body::Constant`] is a row of this matrix, not a footnote: a RED cell means a
//! capability is missing only if its control is GREEN.
//!
//! AND THE SECOND READING WAS WRONG TOO — "a lazy stream cannot feed an eager consumer",
//! which is what WI-20260829-N01PY was filed as. The refusal is `List.length`'s, and
//! `length` is `List`'s OWN operation. `FiniteCollection.size` — the GENERIC eager
//! consumer — takes the same filtered stream, and so does an operation the author
//! declares over that spec. It took a THIRD row to see that, which is this file's own
//! lesson applied one level up: a pair whose two members agree still says nothing if
//! neither of them varies the axis that decides. `lazy_stream_consumption` and
//! `an_author_declared_consumer_takes_a_finite_carrier` are the two tables that separate
//! them now.
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
//! callback body forms {constant, identity, field dot, match destructure, if, nested call,
//! dot call} — 99 cells, the 6 remaining combinations being identity under a PREDICATE
//! host, which the language cannot express and which the sweep reports as skipped rather
//! than dropping. Plus four tables the sweep needs to mean anything: `lazy_stream_-
//! consumption` (what `List.length` does to a lazy carrier — a refusal the repo INTENDS,
//! each cell paired with its dot-free control), `an_author_declared_consumer_takes_a_-
//! finite_carrier` (what the GENERIC eager consumers do to the same values, which is
//! where the capability actually lives — WI-20260829-N01PY), `refusals_that_should_stand`
//! (refusals the repo INTENDS, so a future silent accept reds a cell), and
//! `every_verdict_fails_when_it_should` (the harness's own controls).
//!
//! WHY THESE AXES. Spelling, because WI-20260828-N2FHM's defect existed in the named
//! spelling and not the dot one. Body form, because that is what N2FHM was about.
//! `foldRight`, because its callback binds `(x, acc)` — the REVERSE of `foldLeft`'s
//! `(acc, x)` — so a defect keyed on binder ORDER shows there and nowhere else. And the
//! constant row, because it is the control for every other row at the same host and
//! spelling. `if` joined the body forms with WI-20260829-9TGP7: it shares
//! `compute_branch_join_type`'s checked mode with `match destructure`, so the two move
//! together and a table carrying one of them under-reports that mode by half — which it
//! did, silently, for as long as the `match` cell was the file's one red row.
//!
//! ONE AXIS WAS TRIED AND DROPPED, with the reason recorded rather than the axis silently
//! absent: a label-parameterized receiver (`Msg[Trust]` with a `Txt[Trust]` field, the
//! guardians shape) changes no verdict in any spelling. See
//! `a_label_parameterized_receiver_changes_no_verdict`, which also records the
//! mis-measurement that made it look necessary.
//!
//! WHAT A CELL CAN AND CANNOT WITNESS. A verdict here is about LOADING, and a sweep is
//! the only thing that can ask 99 questions cheaply — but `LOADS` is not `works`, and
//! this file must not be read as if it were. Driving each capability to a value is the
//! per-WI files''' job, and `wi_n2fhm_find_callback_dot_test` does exactly that for the
//! `find` callback dot (`first_flagged_name` asserts the selected row), as
//! `wi_9tgp7_branch_expected_flex_var_test` does for the `match` and `if` bodies under
//! `map` (it evaluates the mapped list). A cell that goes green here without a driven test
//! somewhere is evidence that the program type-checks and nothing more.
//!
//! SLICE 2 — WHAT SITS IN THE POSITION x HOW ITS TYPE IS REACHED, the ticket's other axis
//! pair. Slice 1 swept one POSITION (a lambda callback) across its hosts; slice 2 sweeps
//! one position kind across the ROUTES its type can arrive by. The bare operation name
//! goes first because three delivered items live in that row — WI-20260828-2TMB5, -5NSZY,
//! -8Q0Q5 — each having found ONE route by hand, none able to say what the others did.
//! `a_bare_operation_name_across_its_routes` is those three plus the routes nobody had
//! asked about, and `a_literal_is_checked_on_one_route_and_overwritten_on_the_other` is the other side of its
//! two red cells: the hint they need cannot be supplied while the literal OVERWRITES its
//! elements instead of checking them (WI-20260826-7JDWY).
//!
//! WHAT SLICE 2 TURNED UP that no ticket had: a lambda cannot appear inside a list
//! literal AT ALL (it does not parse, with or without parentheses — so "write a lambda
//! instead" is not available as the repair for the bare-name cells), and every op-return
//! type mismatch is UNLOCATED while op-arg and dot-dispatch mismatches are located
//! (WI-20260829-6RBPD, found by a cell of mine failing an assertion I expected to hold).
//!
//! SLICE 3 — THE REMAINING POSITIONS. `inline constructor`, `field dot`, `match`,
//! `qualified call` and `dot call`, each across the routes it can be spelled in, plus the
//! two routes nothing had exercised: `through a provision chain` and `from a sibling
//! projection`. With slices 1 and 2 that is every position and every route the ticket
//! names.
//!
//! WHAT SLICE 3 TURNED UP:
//!   * NO COMPOUND EXPRESSION IS A TERM — `match`, `if`, `let` and `lambda` parse only
//!     where a BODY is expected, and parentheses do not rescue them (WI-20260829-YBBC3).
//!     `grammar.js` puts them in `_expr_body` while every nested slot is `_term`, and
//!     `paren_expr` wraps a `_term`. This subsumes the earlier lambda-in-a-list finding
//!     and explains why WI-20260828-5NSZY could not offer "write a lambda instead".
//!   * A BOUND SPEC-VIEW PARAMETER REFUSES ITS OWN CARRIER while the bare spec name
//!     accepts it, and `Stream` accepts both (WI-20260829-GNPG7) — filed as a QUESTION,
//!     since which side is right is a design decision, and recorded here as measured
//!     facts rather than as gaps.
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
    /// WI-20260829-9TGP7 — THE OTHER BRANCHING FORM, and it was red for the same reason
    /// `match destructure` was while nothing in this table asked about it. `match` and
    /// `if` share ONE checked-mode implementation (`compute_branch_join_type`), so a
    /// defect in it presents at both and a table carrying only one of them under-reports
    /// its own subject by half. It is a row and not a footnote for exactly the reason
    /// `Constant` is.
    Branch,
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
            Body::Branch => "if",
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
            // Two branches of the SAME type, so the row asks only about the checked-mode
            // conformance against the expectation — not about the join, which
            // `branch_types_that_clash_are_still_refused` is where it belongs.
            (Body::Branch, true) => "if r.flag then true else false",
            (Body::Branch, false) => "if r.flag then 1 else 2",
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
    Body::Branch,
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

/// 99 cells: {find, filter, map, foldLeft, foldRight} x {dot, unqualified, qualified} x
/// {constant, identity, field dot, match destructure, if, nested call, dot call}, less the
/// 6 identity-under-a-predicate-host combinations the language cannot express.
///
/// ALL GREEN, and 6 of them only since WI-20260829-9TGP7 was fixed — 3 that this table
/// carried and reported RED, and 3 (`map` / `if`) it did not carry at all. The green is a
/// CHARACTERIZATION rather than a null result — but read it as "every one of these HOSTS
/// AND DECLARATIONS", not "every host in every spelling". The two are different because
/// the spelling axis co-varies with the declaration it resolves to (`xs.map` reaches
/// `FiniteCollection.map`, `map(xs, …)` reaches `Iterable.map`, `xs.find` reaches
/// `Stream.find`), which `each_spelling_resolves_to_a_named_declaration` pins. The first
/// version of this note claimed the spelling reading and /code-review measured it false;
/// what the sweep actually says is that N2FHM's repair reached every one of the SEVEN
/// declarations these cells touch — which is still what nobody could say when `find` was
/// fixed and `filter` was believed broken, and is a wider statement than the one it
/// replaces. Any cell that moves names the host, the spelling and the body form that moved.
///
/// WHAT THE RED ROWS WERE, kept because the neighbourhood is the finding and a table with
/// nothing red does not say on its own what it once separated. WI-20260829-9TGP7's
/// original description already recorded the cell verbatim —
/// `msgs.map(lambda m -> match m case message(i,f,r,s,b) -> b)` → "expected ?Dst, got
/// Text[Trust = ?_]"; this sweep LOCALIZED it (it did not discover it, and the first
/// version of this note claimed otherwise — found by /code-review):
///
///   map / {dot, unqualified, qualified} / match destructure   WAS RED, `expected ?Dst, got Int64`
///   map / {…} / if                                            WAS RED, same message
///                                                                 (added by the fix; the
///                                                                  table had no `if` row)
///   map / {…} / {constant, field dot, nested call, dot call}  GREEN  ⇒ not the callback binder
///   foldLeft / {…} / match destructure                        GREEN  ⇒ not "has a result param"
///                                                                      (`foldLeft[Acc]` has one)
///   find, filter / every body                                 GREEN  ⇒ not callbacks at large
///
/// THAT SET ANSWERED WI-20260829-9TGP7'S OPEN QUESTION, which asked whether spelling (b)
/// was a CONSEQUENCE of (a) — "if `Element` never grounds, the match arm has nothing to
/// reconcile `?Dst` against" — or independent. It was INDEPENDENT: `Element` grounds fine
/// here, which the green `map / field dot` cell said directly, and `?Dst` failed anyway.
/// (a) was WI-20260829-N01PY, now delivered — and the re-measurement moved it: `length`'s
/// refusal is `List.length`'s and correct, while what was genuinely missing was an eager
/// consumer declared over the SPEC. `lazy_stream_consumption` and
/// `an_author_declared_consumer_takes_a_finite_carrier` below are the two halves.
/// The root and its measurement are `wi_9tgp7_branch_expected_flex_var_test`.
///
/// ONE TEST PER HOST rather than one for the table, so libtest runs them on separate
/// threads: every cell is an independent full-stdlib load, and the 84 cells there were
/// then cost ~55s of wall time serialized that nothing needed to be serial (found by
/// /code-review). A failure
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
                // EVERY CELL LOADS. It has been true only since WI-20260829-9TGP7; the
                // six rows that did not are named in the note above, and the back-out
                // that fails them is stated at `wi_9tgp7_branch_expected_flex_var_test`.
                let want = Verdict::Loads;
                cells.push((
                    format!("{} / {} / {}", h.name, sp.name(), b.name()),
                    sp.call(h, &cb),
                    want,
                ));
            }
        }
    }
    // 3 spellings x 7 bodies, less the identity cells a PREDICATE host cannot express.
    let want_cells = if h.predicate { 18 } else { 21 };
    assert_eq!(
        cells.len(),
        want_cells,
        "{host}: 3 spellings x 7 bodies, less {} inexpressible",
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
/// 21 cells that never execute. Deriving the list from the test functions would close it
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

/// A CELL'S PROGRAM WITH THE GENERIC EAGER CONSUMERS IN SCOPE, and its own builder rather
/// than an addition to [`program`]: the sweep's 99 cells must keep loading the imports
/// they were measured under, and an import can change what a name MEANS (WI-1046).
/// `size` / `collect` live on `FiniteCollection`, and `total` is the consumer an AUTHOR
/// writes — declared over the SPEC, which is the shape WI-20260829-N01PY delivered.
fn consumption_program(body: &str) -> String {
    format!(
        r#"
namespace capmatrixcons
  import anthill.prelude.{{List, Int64, Bool, Stream, Option, Iterable, FiniteCollection}}
  import anthill.prelude.Iterable.{{find, filter, map}}
  import anthill.prelude.List.{{foldLeft, foldRight, length}}
  import anthill.prelude.FiniteCollection.{{size, collect}}
  import capmatrixcons.Row.{{row, a_of, is_set}}
{FIXTURE}
  operation total(c: FiniteCollection) -> Int64 effects c.E = size(c)
  operation cell(xs: List[T = Row]) -> Int64 =
    let s = {body}
    42
end
"#
    )
}

/// WHAT CONSUMING A LAZY COMBINATOR'S RESULT ACTUALLY DOES, and it is not what the
/// tickets that motivated this file said.
///
/// THE ORIGINAL READING, kept because the neighbourhood is the finding: four hand-written
/// probes reported `xs.filter(lambda r -> r.flag)` REFUSED and read it as a callback-dot
/// defect. Re-measured with the dot-free control beside each one, both members refused
/// byte-identically, so the callback was never implicated — which is what WI-20260829-N01PY
/// was filed for, as "a LAZY STREAM cannot feed an EAGER consumer".
///
/// AND THAT SECOND READING WAS ALSO WRONG, which the `size` rows below are here to say.
/// The refusal is `List.length`'s, and `length` is `List`'s OWN operation: a
/// `MappedStream` is not a `List` and never will be. The generic eager consumer is
/// `FiniteCollection.size`, and it takes the mapped stream — through the
/// `MappedStreamFinite` witness WI-590 delivered ("a mapped stream is finite WHEN ITS
/// SOURCE IS"). So the ticket's three candidate repairs stood as:
///
///   (b) a materializing step the author writes — `collect()` — ALREADY WORKED
///   (c) map/filter on a finite carrier returning a finite carrier — ALREADY DELIVERED
///   (a) an eager consumer declared over the SPEC rather than over `List` — the one that
///       was missing, and not as a design choice: the subtype relation asked the
///       CARRIER-keyed `sort_provides`, which cannot see a provision a WITNESS files
///       under itself, so such a consumer could be written and could not be CALLED.
///
/// (a) is what N01PY delivered; `an_author_declared_consumer_takes_a_finite_carrier` is
/// its cell here and `n01py_witness_provision_subtype_test` is where it is driven to a
/// value with its controls.
///
/// EVERY PAIR IS STILL A PAIR. A `length` row keeps its dot-free control, because the
/// pair is what says the callback body is not implicated; and the unconsumed rows are the
/// other half — the same call, not consumed, loads either way.
#[test]
fn lazy_stream_consumption() {
    // `List.length` over a non-`List`. A REFUSAL THE REPO INTENDS — the cell that used to
    // be a `KnownGap` citing WI-20260829-N01PY, which is what made that ticket look like a
    // typer defect rather than a call to the wrong operation.
    const NOT_A_LIST: Verdict = Verdict::RefusesLocated("expected List");
    run(vec![
        (
            "length(map(...)) / field dot".into(),
            "length(xs.map(lambda r -> r.a))".into(),
            NOT_A_LIST,
        ),
        (
            "length(map(...)) / constant (CONTROL — same refusal ⇒ the dot is not it)".into(),
            "length(xs.map(lambda r -> 7))".into(),
            NOT_A_LIST,
        ),
        (
            "length(filter(...)) / field dot".into(),
            "length(xs.filter(lambda r -> r.flag))".into(),
            NOT_A_LIST,
        ),
        (
            "length(filter(...)) / constant (CONTROL)".into(),
            "length(xs.filter(lambda r -> true))".into(),
            NOT_A_LIST,
        ),
        // The contrast that localizes the refusal to CONSUMPTION: the identical calls,
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
        // what attributes the refusal to the LAZY carriers rather than to callbacks at
        // large.
        (
            "find(...) into a consumer (CONTROL — eager host composes)".into(),
            "match xs.find(lambda r -> r.flag) case some(v) -> a_of(v) case none() -> 0".into(),
            Verdict::Loads,
        ),
    ]);
}

/// THE SAME CONSUMPTIONS THROUGH THE GENERIC EAGER CONSUMERS — the rows the table above
/// did not have, and whose absence is what let `length`'s refusal read as "a lazy stream
/// cannot feed an eager consumer".
///
/// `size` and `collect` are declared on `FiniteCollection`, which a mapped or filtered
/// stream provides through its finiteness WITNESS; `total(c: FiniteCollection)` is the
/// same capability in an operation an AUTHOR wrote, which is what WI-20260829-N01PY
/// delivered. The `Iterable.map` row is the soundness boundary in the same table: that
/// spelling DECLARES a bare `Stream` return, erasing the source and with it the
/// finiteness gate, so it must stay refused.
///
/// A CELL SAYS THE PROGRAM LOADS AND NOTHING MORE — `n01py_witness_provision_subtype_test`
/// and `wi492_transitive_provision_test` are where these are driven to values.
///
/// AND A THIRD READING WAS MISSING AGAIN, which the CHAINED rows are here to say. Every
/// row above consumes a ONE-HOP result. A SECOND hop of the same combinator —
/// `xs.map(f).map(g)` — did not load at all, and the table could not see it because it
/// never asked: dot dispatch takes the receiver's OWN member before a provided spec's, and
/// `MappedStream` declares a `map` (a static constructor returning an ERASED `Stream`)
/// while declaring no `filter`. So the mixed chains worked and the same-name ones did not.
/// WI-20260829-X13YV re-typed those two members to return a carrier built from their
/// input; `x13yv_map_map_chain_test` drives them to values and gates them on finiteness.
/// The MIXED rows sit beside the same-name ones because without them a same-name refusal
/// reads as "chaining lazy combinators is broken", which is what it looked like.
///
/// WHICH ROWS MEASURE WI-20260829-N01PY, measured by backing the fix out (making
/// `witness_provides_admissibly` return `false` at its first statement): ONLY the two
/// `AUTHOR's consumer <- map/filter` rows go red. The `size` / `collect` / `.size()` rows
/// PASS EITHER WAY BY DESIGN — those are the spec's OWN operations, dispatched on the
/// carrier, which the finiteness witness has answered since WI-590; they are here to say
/// the capability existed and only the AUTHOR-declared spelling of it did not. The
/// `total(xs)` control and the `Iterable.map` boundary pass either way too.
#[test]
fn an_author_declared_consumer_takes_a_finite_carrier() {
    let rows: Vec<(String, String, Verdict)> = vec![
        (
            "size(map(...)) / field dot".into(),
            "size(xs.map(lambda r -> r.a))".into(),
            Verdict::Loads,
        ),
        (
            "size(map(...)) / constant (CONTROL)".into(),
            "size(xs.map(lambda r -> 7))".into(),
            Verdict::Loads,
        ),
        (
            "size(filter(...)) / field dot".into(),
            "size(xs.filter(lambda r -> r.flag))".into(),
            Verdict::Loads,
        ),
        (
            "collect(map(...))".into(),
            "collect(xs.map(lambda r -> r.a))".into(),
            Verdict::Loads,
        ),
        (
            "map(...).size() — the dot spelling of the same".into(),
            "xs.map(lambda r -> r.a).size()".into(),
            Verdict::Loads,
        ),
        (
            "AUTHOR's consumer over the spec <- map(...)   [WI-20260829-N01PY]".into(),
            "total(xs.map(lambda r -> r.a))".into(),
            Verdict::Loads,
        ),
        (
            "AUTHOR's consumer over the spec <- filter(...) [WI-20260829-N01PY]".into(),
            "total(xs.filter(lambda r -> r.flag))".into(),
            Verdict::Loads,
        ),
        (
            "AUTHOR's consumer over the spec <- a plain List (CONTROL — direct provision)"
                .into(),
            "total(xs)".into(),
            Verdict::Loads,
        ),
        (
            "AUTHOR's consumer <- Iterable.map (BOUNDARY — the erased `Stream` return \
             is maybe-infinite and must NOT be eagerly consumable)"
                .into(),
            "total(Iterable.map(xs, lambda r -> r.a))".into(),
            Verdict::RefusesLocated("expected FiniteCollection"),
        ),
        // ── CHAINED HOPS (WI-20260829-X13YV) ────────────────────────────────────
        // The rows above all consume a ONE-HOP combinator result. Chaining a SECOND hop
        // of the SAME combinator was refused outright — `xs.map(f).map(g)` did not load —
        // while the MIXED chains did, because dot dispatch resolves a member on the
        // receiver's own sort before the specs it provides and `MappedStream` declares a
        // `map` while declaring no `filter`. The mixed rows are kept beside the same-name
        // ones for exactly that reason: without them the same-name refusal reads as
        // "chaining lazy combinators is broken".
        (
            "size(map(...).map(...)) — SAME name twice [WI-20260829-X13YV]".into(),
            "size(xs.map(lambda r -> r.a).map(lambda n -> n))".into(),
            Verdict::Loads,
        ),
        (
            "size(filter(...).filter(...)) — SAME name twice [WI-20260829-X13YV]".into(),
            "size(xs.filter(lambda r -> r.flag).filter(lambda r -> true))".into(),
            Verdict::Loads,
        ),
        (
            "size(map(...).filter(...)) — MIXED (CONTROL: loaded before the fix too)".into(),
            "size(xs.map(lambda r -> r.a).filter(lambda n -> true))".into(),
            Verdict::Loads,
        ),
        (
            "size(filter(...).map(...)) — MIXED (CONTROL)".into(),
            "size(xs.filter(lambda r -> r.flag).map(lambda r -> r.a))".into(),
            Verdict::Loads,
        ),
        (
            "AUTHOR's consumer <- map(...).map(...) [WI-20260829-X13YV]".into(),
            "total(xs.map(lambda r -> r.a).map(lambda n -> n))".into(),
            Verdict::Loads,
        ),
        (
            "map(...).map(...).collect() — the materializing consumer".into(),
            "xs.map(lambda r -> r.a).map(lambda n -> n).collect()".into(),
            Verdict::Loads,
        ),
    ];
    let mut failures = Vec::new();
    let mut report = String::new();
    for (label, body, want) in rows {
        match check_src(&label, &consumption_program(&body), want) {
            Ok(line) => {
                let _ = writeln!(report, "  {line}");
            }
            Err(e) => failures.push(e),
        }
    }
    println!("{report}");
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

// ── THE HARNESS'S OWN CONTROLS ───────────────────────────────────────────────

/// EVERY VERDICT MUST BE ABLE TO FAIL, and nothing above proves that: the two tables are
/// all-passing by construction, so a `check` that returned `Ok` unconditionally — or a
/// `KnownGap` arm that forgot the closed-gap branch — would leave every table cell vacuous
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
    // a program that fails because of something this file TRACKS: `length(xs.map(...))` was
    // used here first, and the day that stopped refusing these controls would start
    // failing with "a Loads cell whose program refuses must fail" — blaming the harness,
    // in the same run where the tracked cells correctly report themselves (found by
    // /code-review). `nosuchname` is refused by construction and by nothing anyone will
    // ever repair. (WI-20260829-N01PY has since been delivered WITHOUT changing
    // `length`'s verdict — `length` is `List`'s own operation and its refusal is right —
    // so the hazard this note describes did not fire, and the rule stands for the next
    // cell that would be tempted to reuse a tracked program here.)
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
    // NOT `length(xs.map(...))`, which the tables above track: were its verdict ever to
    // move, this control would panic with "a correctly-recorded KnownGap cell must pass"
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
/// (WI-20260829-N01PY: the erased `Stream` return of the QUALIFIED `Iterable.map` cannot
/// feed an eager consumer, and still cannot — that is the soundness boundary, not a gap).
/// /code-review caught it and measured the axis independently.
///
/// So the rows below carry the label parameter the guardians `Message[Trust]` has, and
/// they LOAD — in every spelling, exactly as the plain `Row` fixture does. The label
/// parameter separates nothing, which is why the main table does not carry it as an axis.
/// The one red cell it used to produce was `map` + match destructure, which was already in
/// the sweep under the plain fixture — the same gap (WI-20260829-9TGP7), not a new one, and
/// fixed with it.
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
    // WI-20260826-7JDWY, pinned by `a_literal_is_checked_on_one_route_and_overwritten_on_the_other`;
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

/// A LAMBDA INSIDE A LIST LITERAL — routes 6 and 7 of the table above, seen from the
/// other side. It did not PARSE at all until WI-20260829-YBBC3 (with or without
/// parentheses, since `paren_expr` wrapped a `_term` too); it now loads, and its element
/// type is CHECKED.
///
/// IT SETTLES THE REPAIR THE TABLE ABOVE COULD NOT OFFER. Routes 6 and 7 record that a
/// bare operation name in a list/set literal is refused (`LITERAL_GAP`, WI-20260826-7JDWY
/// through WI-20260828-5NSZY), and the natural advice — "write a lambda instead" — was
/// unavailable because that spelling was a syntax error. It is available now, and these
/// rows are what makes the advice checkable rather than plausible.
///
/// THE FIXTURE BODY IS `lambda x -> 7`, NOT `lambda x -> x + 1`, and the difference was
/// MEASURED: the arithmetic body refuses in every row here with "ambiguous dispatch of
/// Additive.add: 3 instances", a fact about numeric dispatch on a binder no route pins,
/// not about the position. `the_row_remainders` removed the same confound for the same
/// reason.
///
/// THE NEGATIVE ROW IS WHAT MAKES THE REST A MEASUREMENT: `takes_list([lambda x -> 7])`
/// refuses, located, naming the arrow it found. Without it, "loads" would be consistent
/// with the literal's elements never being looked at — which is exactly what
/// WI-20260826-7JDWY does on the RETURN-HINT route (`a_literal_is_checked_on_one_route_
/// and_overwritten_on_the_other`).
#[test]
fn a_lambda_inside_a_list_literal() {
    run_routes(vec![
        (
            "6' lambda inside a LIST literal (the repair route 6 lacked)".into(),
            "  operation c() -> Int64 = head_apply([lambda x -> 7], 41)".into(),
            Verdict::Loads,
        ),
        (
            "6' lambda inside a LIST literal, parenthesized".into(),
            "  operation c() -> Int64 = head_apply([(lambda x -> 7)], 41)".into(),
            Verdict::Loads,
        ),
        (
            // A set literal's elements are still `_term` (the `rule { _term • , }`
            // conflict), so the parenthesized spelling is the only one that reaches one.
            "7' lambda inside a SET literal, parenthesized (the only spelling)".into(),
            "  operation c() -> Int64 = set_apply({(lambda x -> 7)}, 41)".into(),
            Verdict::Loads,
        ),
        (
            "NEGATIVE — the element type is CHECKED, not overwritten".into(),
            "  operation c() -> Int64 = takes_list([lambda x -> 7])".into(),
            // BOTH SIDES of the mismatch. Pinning only `expected …` left the doc's claim
            // — that the refusal names the ARROW it found — unchecked, so a regression on
            // the `got` side would keep this green (found by /code-review).
            Verdict::RefusesLocated("expected List[T = Int64], got List[T = ??param -> Int64]"),
        ),
    ]);
    // The BARE set-literal spelling stays a parse error, and that is a language fact
    // rather than a coverage gap — `set_literal` was deliberately not widened. Asserted
    // here so the "parenthesized is the only spelling" claim one row up cannot go stale.
    assert!(
        anthill_core::parse::parse(&route_program(
            "  operation c() -> Int64 = set_apply({lambda x -> 7}, 41)"
        ))
        .is_err(),
        "a BARE lambda inside a set literal now parses — if `set_literal` was widened, \
         fold this into the row above and say what settled the `rule {{ _term • , }}` \
         conflict."
    );
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
        // could start resolving elsewhere and 14 sweep cells (2 hosts x 1 spelling x 7 body
        // forms) would silently change which declaration they measure with this guard
        // still green — the exact confound the test exists to rule out. THE FIGURE IS
        // DERIVED FROM `BODIES`, so it moves when the axis does: it read 12 until
        // WI-20260829-9TGP7 added the `if` row and nothing re-derived it (found by
        // /code-review, the second stale count of that pair).
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

// ═══ SLICE 3 — THE REMAINING POSITIONS x THE REMAINING ROUTES ═══════════════

/// A program with a `Row` value and an `Int64` in scope, plus a slot of every ROUTE kind.
/// `{slot}` is where a cell's expression goes; the surrounding declaration is the route.
fn pos_program(decl: &str) -> String {
    format!(
        r#"
namespace capmatrix_pos
  import anthill.prelude.{{List, Set, Int64, Bool, String, Iterable, Stream, Option}}
  sort Row
    import anthill.prelude.{{Int64, Bool}}
    entity row(a: Int64, flag: Bool)
    operation a_of(r: Row) -> Int64 = match r case row(x, f) -> x
    operation is_set(r: Row) -> Bool = match r case row(x, f) -> f
  end
  operation takes_int(v: Int64) -> Int64 = v
  operation takes_row(v: Row) -> Int64 = 1
  operation takes_any[A](x: A) -> Int64 = 1
  operation takes_iterable(c: Iterable[C = List[T = Row], Element = Row, E = {{}}]) -> Int64 = 1
  operation pair_up(a: Int64, b: Int64) -> Int64 = a
  operation pick(xs: List[T = Int64], e: xs.T) -> Int64 = 1
  operation takes_set(s: Set[T = Int64]) -> Int64 = 1
{decl}
end
"#
    )
}

fn run_positions(cells: Vec<(String, String, Verdict)>) {
    run_with(cells, pos_program)
}

/// THE REMAINING POSITIONS, each in the four routes that can be spelled uniformly for it.
/// Positions already covered: `lambda` (slice 1), `bare op name` and `list/set literal`
/// (slice 2). These are the other five the ticket names.
///
/// EVERY CELL IS WELL-TYPED BY CONSTRUCTION — an `Int64`-producing position only meets an
/// `Int64`-expecting route, and the constructor position only meets `Row`-expecting ones —
/// so a RED cell means the ROUTE failed to carry the type, never that the cell asked for
/// something impossible. That is what makes the table about routes rather than about
/// whether five expressions happen to type.
#[test]
fn the_remaining_positions_across_their_routes() {
    let mut cells: Vec<(String, String, Verdict)> = Vec::new();
    // (position, expression producing Int64)
    let int_positions: &[(&str, &str)] = &[
        ("field dot", "r.a"),
        ("match", "match r case row(x, f) -> x"),
        ("qualified call", "Row.a_of(r)"),
        ("dot call", "r.a_of()"),
    ];
    // (route, how the slot is spelled around `{}`)
    let int_routes: &[(&str, &str)] = &[
        ("written directly (annotated let)", "  operation c(r: Row) -> Int64 =\n    let v: Int64 = {}\n    v"),
        ("from a hint (declared return)", "  operation c(r: Row) -> Int64 = {}"),
        ("from a callee's declared param", "  operation c(r: Row) -> Int64 = takes_int({})"),
        ("from a type parameter", "  operation c(r: Row) -> Int64 = takes_any({})"),
        // A GENUINE sibling projection: `pick`'s second parameter type PROJECTS off the
        // first argument (`e: xs.T`), which is the stdlib's own shape (`Stream.find`'s
        // `pred: (x: s.T)`). The first cut used `pair_up(a: Int64, b: Int64)` and called
        // it a sibling projection — two ordinary parameters, projecting nothing, so the
        // row measured the argument route a second time under a different name.
        ("from a sibling projection", "  operation c(r: Row, ns: List[T = Int64]) -> Int64 = pick(ns, {})"),
    ];
    // NO ROUTE IS SKIPPED. The three NESTED routes — the ones that put the expression
    // inside a term rather than at a body — used to be unspellable for `match`, because
    // the compound forms lived in `_expr_body` alone; WI-20260829-YBBC3 widened the
    // delimited positions and closed that, so `match` sweeps the same five routes every
    // other position does. If a position ever becomes unspellable again, record it the
    // way that ticket's rows do — as a named skip WITH the WI — rather than by dropping
    // it from `int_positions`.
    for (pos, expr) in int_positions {
        for (route, shape) in int_routes {
            cells.push((
                format!("{pos} / {route}"),
                shape.replace("{}", expr),
                Verdict::Loads,
            ));
        }
    }
    // A GUARD, NOT A MEASUREMENT, and it cannot fail on today's loop — which is the
    // point: it replaced `assert_eq!(unspellable.len(), 3)`, which counted a skip list
    // that no longer exists. What reddens it is the edit it exists to catch — a
    // `continue` reintroduced in the loop above, which is how the `match` cells were
    // dropped while WI-20260829-YBBC3 was open. A skipped cell must be a named skip with
    // its WI, never a silently shorter table.
    assert_eq!(
        cells.len(),
        int_positions.len() * int_routes.len(),
        "every position must sweep every route — a skipped cell needs a WI, not silence"
    );
    // The CONSTRUCTOR position produces a `Row`, so it meets the Row-expecting routes.
    let row_routes: &[(&str, &str)] = &[
        ("written directly (annotated let)", "  operation c() -> Int64 =\n    let v: Row = {}\n    1"),
        ("from a hint (declared return)", "  operation c() -> Row = {}"),
        ("from a callee's declared param", "  operation c() -> Int64 = takes_row({})"),
        ("from a type parameter", "  operation c() -> Int64 = takes_any({})"),
    ];
    for (route, shape) in row_routes {
        cells.push((
            format!("inline constructor / {route}"),
            shape.replace("{}", "row(a: 1, flag: true)"),
            Verdict::Loads,
        ));
    }
    run_positions(cells);
}

/// A COMPOUND EXPRESSION IS A VALUE EXPRESSION — `match`, `if`, `let` and `lambda` are
/// admissible in every DELIMITED value position, and parentheses reach the rest.
/// WI-20260829-YBBC3, which this table's earlier slice found and which is now CLOSED.
///
/// WHAT IT WAS. `grammar.js` put the compound forms in `_expr_body` — the operation-BODY
/// rule — while arguments, named-argument values and list elements were built from
/// `_term`, which does not include them; and `paren_expr` wrapped a `_term` too, which is
/// why the parenthesized spellings failed IDENTICALLY to the bare ones. All five rows
/// below were parse errors that never reached the typer. They are `Verdict` rows now,
/// like everything else in this file.
///
/// THE TWO LIMITS ARE ROWS TOO, and they are what keeps this table from reading as
/// "compound forms are terms now": a bare compound form is still not an INFIX OPERAND and
/// still not a SET-LITERAL element. Those stay parse assertions, because that is what
/// they are.
///
/// IT EXPLAINS AN EARLIER FINDING. `a_lambda_inside_a_list_literal` was
/// this rule seen through one form, and it is why WI-20260828-5NSZY could not offer
/// "write a lambda instead" as the repair for a bare operation name in a list literal —
/// that spelling now parses, and that test now records what it types as.
///
/// The end-to-end evidence lives in `wi_ybbc3_compound_expression_positions_test`, which
/// DRIVES each position to a value; these rows are the matrix's own load verdicts.
#[test]
fn a_compound_expression_is_a_value_expression() {
    let cells: Vec<(String, String, Verdict)> = vec![
        (
            "match as an argument".into(),
            "  operation c(r: Row) -> Int64 = takes_int(match r case row(x, f) -> x)".into(),
            Verdict::Loads,
        ),
        (
            "match as an argument, parenthesized".into(),
            "  operation c(r: Row) -> Int64 = takes_int((match r case row(x, f) -> x))".into(),
            Verdict::Loads,
        ),
        (
            "if as an argument".into(),
            "  operation c(r: Row) -> Int64 = takes_int(if true then 1 else 2)".into(),
            Verdict::Loads,
        ),
        (
            "if as an argument, parenthesized".into(),
            "  operation c(r: Row) -> Int64 = takes_int((if true then 1 else 2))".into(),
            Verdict::Loads,
        ),
        (
            "match as a list element".into(),
            "  operation c(r: Row) -> List[T = Int64] = [match r case row(x, f) -> x]".into(),
            Verdict::Loads,
        ),
        // ── the NEGATIVE rows: the slot is type-checked, not merely parsed ──
        // Without these, every row above would stay green if a compound argument were
        // parsed and then skipped by the typer.
        (
            "NEGATIVE — a match arm's type is checked in an argument".into(),
            "  operation c(r: Row) -> Int64 = takes_int(match r case row(x, f) -> f)".into(),
            Verdict::RefusesLocated("expected Int64, got Bool"),
        ),
        (
            "NEGATIVE — an if branch's type is checked in an argument".into(),
            "  operation c(r: Row) -> Int64 = takes_int(if true then 1 else true)".into(),
            Verdict::RefusesLocated("expected Int64, got Bool"),
        ),
    ];
    run_positions(cells);

    // ── THE TWO LIMITS, which are parse facts and stay parse assertions ──
    // `_term` was NOT widened: only the delimited positions and `paren_expr` were. An
    // infix operand and a set-literal element are the two an author is most likely to
    // try next, and each has its own reason — an infix operand has no delimiter, and a
    // set literal's `{ a, b }` is already the block / goal-list spelling, so widening it
    // is a measured `rule { _term • , }` grammar conflict.
    for (what, expr, next) in [
        (
            "a bare compound form as an infix operand",
            "1 + if true then 1 else 2",
            "widening `_term` itself, which also puts the compound forms in dot-receiver \
             and pattern positions",
        ),
        (
            "a bare compound form as a set-literal element",
            "takes_set({if true then 1 else 2, 3})",
            "settling the `rule { _term • , }` conflict",
        ),
    ] {
        let src = pos_program(&format!("  operation c(r: Row) -> Int64 = {expr}"));
        assert!(
            anthill_core::parse::parse(&src).is_err(),
            "{what} (`{expr}`) now PARSES. That is a LARGER change than \
             WI-20260829-YBBC3 made — it needs {next}. Say so at the grammar site, then \
             flip this into a load-verdict cell above."
        );
    }
    // And the parenthesized spelling is what reaches both, so the limits are a shape
    // requirement and not a missing capability.
    run_positions(vec![
        (
            "if as an infix operand, parenthesized".into(),
            "  operation c(r: Row) -> Int64 = 1 + (if true then 1 else 2)".into(),
            Verdict::Loads,
        ),
        (
            "if as a set element, parenthesized".into(),
            "  operation c(r: Row) -> Int64 = takes_set({(if true then 1 else 2), 3})".into(),
            Verdict::Loads,
        ),
    ]);
}

/// A SPEC-TYPED PARAMETER AND ITS CARRIER — the `through a provision chain` route.
///
/// WI-20260829-GNPG7 SETTLED THIS, AND THE TABLE IT WAS FILED FROM MEASURED THE WRONG
/// AXIS. The reading recorded here was that "what decides admissibility is whether the
/// parameter's spec type carries BINDINGS" — every bindings-carrying `Iterable` row
/// refused while the bare one loaded, and `Stream` accepted both. That is a CONFOUND: the
/// rows also differ in HOP COUNT, because `List` declares `provides Stream[T, {}]` and
/// reaches `Iterable` only through `Stream provides Iterable`, while `List provides
/// Stream` is direct.
///
/// THE ROW THAT SEPARATES THEM is the `MutableStack` pair below, added when the ticket was
/// settled: `MutableStack` declares `provides Iterable[C = MutableStack[T], Element = T, E
/// = {}]` ITSELF, and it is accepted at the FULLY-BOUND spec view naming its own carrier —
/// the exact shape the "a bindings-carrying spec type is a distinct VIEW" reading says
/// must be refused. Same spec, same binding shape, opposite verdict from `List`. So
/// bindings were never the axis; transitivity was.
///
/// The cause was one relation with two readers: `sort_provides` (which the bare-spec arms
/// reach through `sort_provides_admissibly`) walks the whole provision chain, while
/// `provider_spec_view_bindings` read a single DIRECT fact. Both subtype sites now go
/// through `transitive_provider_spec_view_bindings`, which already existed for exactly
/// this chain (WI-714/WI-495).
///
/// ONE ROW STILL REFUSES, and it is a DIFFERENT defect with its own ticket
/// (WI-20260829-XZMGC): the composed view maps the intermediate's
/// PARAMS — `Element ↦ List.T` and `E ↦ {}` both compose, which is why
/// `Iterable[Element = Row, E = {}]` loads — but keeps `C = Stream`, the intermediate's
/// SELF-reference, verbatim. `compose_provision_views`' doc records that as deliberate,
/// and it is harmless for the consumers that ground params off a receiver; the subtype
/// relation is the one that COMPARES `C`, and `Iterable.iterator` on a `List` receives the
/// `List`, so `C = List` is the answer it should get.
///
/// STILL MEASURED FACTS, NOT GAPS, for the same reason as before: the refusing row is
/// `RefusesLocated` because the refusal is correct-as-far-as-the-composer-goes, and the
/// table's job is to make the next move visible.
#[test]
fn a_spec_typed_parameter_and_its_carrier() {
    fn program_with(param: &str) -> String {
        format!(
            r#"
namespace capmatrix_prov
  import anthill.prelude.{{Int64, Bool, List, Iterable, Stream}}
  sort Row
    import anthill.prelude.{{Int64, Bool}}
    entity row(a: Int64, flag: Bool)
  end
  operation ti(c: {param}) -> Int64 = 1
  operation c(rs: List[T = Row]) -> Int64 = ti(rs)
end
"#
        )
    }
    let rows: &[(&str, &str, Verdict)] = &[
        ("bare spec name", "Iterable", Verdict::Loads),
        (
            // THE ONE ROW STILL REFUSED, and no longer for "it carries bindings" — the
            // row below carries one too and loads. `C` alone: the composed view keeps
            // `Stream`, the intermediate's self-reference, where `List` belongs.
            "spec bound to its own carrier",
            "Iterable[C = List[T = Row], Element = Row, E = {}]",
            Verdict::RefusesLocated("expected Iterable[C = List[T = Row]"),
        ),
        (
            // WI-20260829-GNPG7: was refused, now LOADS. `Element` composes through
            // `List provides Stream` + `Stream provides Iterable` to `List.T`, which
            // this instance binds to `Row`.
            "spec with one binding, carrier unbound",
            "Iterable[Element = Row]",
            Verdict::Loads,
        ),
        (
            // The same, with the effect row written too — `E` composes to the `{}` that
            // `List provides Stream[T, {}]` supplies. Together with the row above this
            // says the composition works for every spec param EXCEPT the carrier one.
            "spec with every non-carrier binding",
            "Iterable[Element = Row, E = {}]",
            Verdict::Loads,
        ),
        // `Stream` accepts BOTH spellings, which is what makes the rows above an
        // asymmetry between two specs on one chain rather than a rule about spec params.
        ("bare Stream (CONTRAST)", "Stream", Verdict::Loads),
        (
            // `List provides Stream` is DIRECT — one hop — which is why this row loaded
            // even before WI-20260829-GNPG7, and why reading it as "Stream accepts
            // bindings, Iterable does not" put the difference on the wrong axis.
            "Stream WITH bindings (CONTRAST — one hop)",
            "Stream[T = Row, E = {}]",
            Verdict::Loads,
        ),
    ];
    let mut failures: Vec<String> = Vec::new();
    for (label, param, want) in rows {
        if let Err(e) = check_src(label, &program_with(param), *want) {
            failures.push(e);
        }
    }

    // THE DISCRIMINATOR — the pair the ticket's own table lacked, which is why it read
    // BINDINGS as the axis. `MutableStack` declares `provides Iterable[C = MutableStack[T],
    // Element = T, E = {}]` ITSELF (mutable_stack.anthill), so its route to `Iterable` is
    // ONE hop where `List`'s is two. The spec is the same `Iterable` and the binding shapes
    // are the same as the `List` rows above; only the hop count differs — and the FULLY
    // BOUND row, naming its own carrier, loads. That is the shape a "spec-with-bindings is
    // a structurally distinct VIEW" reading has to refuse, so this pair is what refutes it.
    //
    // BOTH ROWS PASS EITHER WAY across WI-20260829-GNPG7's change, by design: one hop needs
    // no composition. They are the CONTROL — they say the transitive routing did not
    // disturb the direct case, and they are why the `List` rows' movement is attributable
    // to transitivity rather than to bindings.
    let stack_program = |param: &str| -> String {
        format!(
            r#"
namespace capmatrix_prov_stack
  import anthill.prelude.{{Int64, Bool, MutableStack, Iterable}}
  sort Row
    import anthill.prelude.{{Int64, Bool}}
    entity row(a: Int64, flag: Bool)
  end
  operation ti(c: {param}) -> Int64 = 1
  operation c(rs: MutableStack[T = Row]) -> Int64 = ti(rs)
end
"#
        )
    };
    for (label, param) in [
        ("DIRECT provider, one binding", "Iterable[Element = Row]"),
        (
            "DIRECT provider, spec bound to its own carrier",
            "Iterable[C = MutableStack[T = Row], Element = Row, E = {}]",
        ),
    ] {
        if let Err(e) = check_src(label, &stack_program(param), Verdict::Loads) {
            failures.push(e);
        }
    }
    assert!(
        failures.is_empty(),
        "{} spec-view row(s) moved — if WI-20260829-GNPG7 was settled, update these and \
         close it:\n\n{}",
        failures.len(),
        failures.join("\n\n"),
    );
}

// ═══ THE COVERAGE CENSUS ════════════════════════════════════════════════════

/// WHAT THE GRID COVERS — the ticket's two axes crossed in full, each of the 48 cells
/// named by the test that asserts it. This exists because "is it all combinations?" is a
/// question I answered by eye once and got wrong, and because WI-20260829-ARQ5X was
/// DELIVERED once on a slice while its SHAPE section specified the whole grid.
///
/// IT NAMES TESTS, NOT A `Coverage` MARKER, and that is the difference between a census
/// that can fail and one that cannot. The first cut was an enum — `Built` /
/// `Unspellable(wi)` / `NotYetBuilt` — over a hand-written table, and once the grid
/// completed every cell read `Built`: two variants constructed nowhere (a dead-code
/// warning), and three asserts comparing a constant table against itself. What a reader
/// actually needs from a census is WHERE a cell is asserted, and that is checkable —
/// `include_str!` on this file, and every name below must be a `fn` in it.
///
/// WHAT REDDENS IT, which is the whole point: renaming or deleting a test the grid leans
/// on. That is not hypothetical — `a_compound_expression_is_not_a_term` and
/// `a_lambda_inside_a_list_literal_does_not_parse` were both renamed when
/// WI-20260829-YBBC3 closed, and under the enum the census stayed green through it,
/// still claiming 48 covered cells while two of the tests it meant no longer existed.
/// MEASURED, on this version: renaming `a_lambda_inside_a_list_literal` fails the census
/// naming the position that loses its owner (`lambda -> a_lambda_inside_a_list_literal`).
///
/// WHAT IT STILL DOES NOT CHECK, said plainly rather than implied: that the named test
/// asserts THIS position in THIS route. Rust cannot ask that, and the finer key would be
/// a fiction — slice 2's routes map onto the ticket's six only approximately, which its
/// own comment said. So the grid is per POSITION, listing every test that carries any of
/// its routes; a cell-level claim would be more precise and less true.
///
/// IF A CELL EVER BECOMES UNSPELLABLE AGAIN — the language cannot express it — that is a
/// LANGUAGE ticket, not a coverage gap. Write the position's entry as the WI id and say
/// so here; `a_compound_expression_is_a_value_expression` is what that looked like while
/// WI-20260829-YBBC3 was open, and its two `_term` limits are what it looks like now.
#[test]
fn the_grid_census_is_honest() {
    /// This file's own source, so a named test that no longer exists is a FAILURE rather
    /// than a stale comment.
    const SELF: &str = include_str!("typer_capability_matrix_test.rs");

    // The ticket's six ROUTES, in the order it lists them. Named so the arithmetic below
    // is about the ticket's axes and not a bare `48`.
    const ROUTES: [&str; 6] = [
        "written directly",
        "from a hint",
        "callee's declared param",
        "from a type parameter",
        "through a provision chain",
        "from a sibling projection",
    ];
    // The ticket's eight POSITIONS, each with the tests that carry its routes.
    let grid: &[(&str, &[&str])] = &[
        // Slice 2 swept this position across routes of its own naming; mapped onto the
        // ticket's six it reaches the hint and callee-param columns, and
        // `the_row_remainders` carries the rest — including the two REFUSALS (a type
        // parameter and a spec-typed slot supply no arrow to lift a bare name against).
        ("bare op name", &[
            "a_bare_operation_name_across_its_routes",
            "the_row_remainders",
        ]),
        // Slice 1 ALSO swept the lambda across HOSTS x SPELLINGS x BODIES — a different
        // and deeper cross than this grid; these are the tests carrying the grid's own
        // columns.
        ("lambda", &[
            "the_row_remainders",
            "a_lambda_inside_a_list_literal",
            "sweep_map",
        ]),
        ("inline constructor", &[
            "the_remaining_positions_across_their_routes",
            "the_row_remainders",
            "every_position_through_a_provision_chain",
        ]),
        ("field dot", &[
            "the_remaining_positions_across_their_routes",
            "every_position_through_a_provision_chain",
        ]),
        // Every NESTED route was UNSPELLABLE for `match` until WI-20260829-YBBC3 widened
        // the delimited value positions — a compound form lived in `_expr_body` (the
        // operation-BODY rule) and nowhere else, parentheses included.
        ("match", &[
            "the_remaining_positions_across_their_routes",
            "every_position_through_a_provision_chain",
            "a_compound_expression_is_a_value_expression",
        ]),
        // BOTH MEMBERS in every route, which is what this entry asserts and what the
        // first cut did not have: `the_row_remainders` sweeps a `[…]` and a `{…}` per
        // route, and the provision-chain column carries the two separately — a `List`
        // loads there and a `Set` REFUSES, correctly, because `prelude/set.anthill`
        // provides only `PartialEq` / `Eq`. Sweeping the LIST alone while the census
        // called the position covered is what /code-review caught.
        ("list/set literal", &[
            "a_literal_is_checked_on_one_route_and_overwritten_on_the_other",
            "the_row_remainders",
            "every_position_through_a_provision_chain",
        ]),
        ("qualified call", &[
            "the_remaining_positions_across_their_routes",
            "every_position_through_a_provision_chain",
        ]),
        ("dot call", &[
            "the_remaining_positions_across_their_routes",
            "every_position_through_a_provision_chain",
        ]),
    ];

    let mut missing: Vec<String> = Vec::new();
    for (pos, tests) in grid {
        assert!(
            !tests.is_empty(),
            "position `{pos}` names no test — a cell with no owner is the gap this \
             census exists to show, not an empty list"
        );
        for t in tests.iter() {
            if !SELF.contains(&format!("fn {t}(")) {
                missing.push(format!("{pos} -> {t}"));
            }
        }
    }
    assert!(
        missing.is_empty(),
        "the census names {} test(s) that do not exist in this file. A renamed or deleted \
         test leaves its grid cells unasserted while the census still claims them:\n  {}",
        missing.len(),
        missing.join("\n  "),
    );

    // THE SHAPE, against the ticket's own axes rather than a bare constant: 8 positions
    // times 6 routes. It reddens when a position or a route is added without the grid
    // being extended to say what covers it.
    assert_eq!(grid.len(), 8, "the ticket names eight positions");
    assert_eq!(grid.len() * ROUTES.len(), 48, "the grid is 8 positions x 6 routes");
    println!(
        "  grid: {} positions x {} routes = {} cells, every position owned by a live test",
        grid.len(),
        ROUTES.len(),
        grid.len() * ROUTES.len(),
    );
}

/// THE PROVISION-CHAIN COLUMN — the positions that can be delivered into a parameter
/// typed on a SPEC the argument's carrier provides transitively (`List provides Stream
/// provides Iterable`). It was the grid's largest gap: `a_spec_typed_parameter_and_its_
/// carrier` varies the PARAMETER's spec type, which is a different question from what
/// sits in the position.
///
/// NOT EVERY POSITION, and the exceptions are named rather than absent. `bare op name`
/// and `lambda` reach this column in `the_row_remainders`, where they REFUSE — a bare
/// non-nullary name has no arrow to lift against, and an arrow is not an `Iterable` — so
/// they sit beside the other routes' refusals of the same two rules. The first cut of
/// this table carried rows LABELLED for those two positions that did not hold them
/// (`ti(mk_list())` is a nullary call; `ti(Iterable.map(rs, …))` is a qualified call),
/// which made two cells claim one grid position with opposite verdicts — found by
/// /code-review; both are relabelled below under what they actually are.
///
/// THE PARAMETER IS THE BARE SPEC NAME, deliberately — per WI-20260829-GNPG7 that is the
/// only spelling that accepts a carrier at all, so a bound one would red every cell for a
/// reason that has nothing to do with the position under test.
///
/// AND THE SLOT DISCRIMINATES, which is what stops all-green from being vacuous: `ti`'s
/// body ignores its argument, so "loads" would mean nothing if the parameter accepted
/// anything. `ti(1)` and `ti(r)` are the two rows that carry that claim — an `Int64` and
/// a `Row` are each refused, located.
#[test]
fn every_position_through_a_provision_chain() {
    fn prov_program(decl: &str) -> String {
        format!(
            r#"
namespace capmatrix_chain
  import anthill.prelude.{{Int64, Bool, List, Set, Iterable, Stream}}
  import anthill.prelude.List.{{cons, nil}}
  sort Row
    import anthill.prelude.{{Int64, Bool}}
    entity row(a: Int64, flag: Bool)
  end
  sort Box
    import anthill.prelude.{{List}}
    import capmatrix_chain.{{Row}}
    entity box(rows: List[T = Row])
    operation rows_of(b: Box) -> List[T = Row] = match b case box(rs) -> rs
  end
  import capmatrix_chain.Row.{{row}}
  import capmatrix_chain.Box.{{box}}
  operation mk_list() -> List[T = Row] = nil()
  operation mk_box() -> Box = box(rows: nil())
  operation inc(x: Int64) -> Int64 = x + 1
  operation ti(c: Iterable) -> Int64 = 1
{decl}
end
"#
        )
    }
    let cells: Vec<(String, String, Verdict)> = vec![
        // A NULLARY CALL, not a bare operation name — `ti(mk_list())` APPLIES `mk_list`,
        // and the bare-name position is `ti(mk_list)`. It was labelled "bare op name"
        // here and that made two cells claim the same grid position with opposite
        // verdicts (found by /code-review). The genuine one is `the_row_remainders`'
        // `ti(inc)`, which REFUSES; this row is kept under its real name because a
        // nullary call reaching a spec-typed slot is worth a cell of its own.
        ("nullary call".into(), "  operation c() -> Int64 = ti(mk_list())".into(), Verdict::Loads),
        (
            "inline constructor".into(),
            "  operation c(r: Row) -> Int64 = ti(cons(r, nil()))".into(),
            Verdict::Loads,
        ),
        ("field dot".into(), "  operation c(b: Box) -> Int64 = ti(b.rows)".into(), Verdict::Loads),
        (
            "qualified call".into(),
            "  operation c() -> Int64 = ti(Box.rows_of(mk_box()))".into(),
            Verdict::Loads,
        ),
        ("dot call".into(), "  operation c() -> Int64 = ti(mk_box().rows_of())".into(), Verdict::Loads),
        ("list literal".into(), "  operation c(r: Row) -> Int64 = ti([r])".into(), Verdict::Loads),
        // A NESTED CALL, not a lambda: the expression in the spec-typed slot is
        // `Iterable.map(…)` and the lambda is one level inside it, in a slot the
        // callback sweep already covers. Labelled "lambda" it duplicated the
        // `qualified call` row three entries up and said nothing about a lambda in this
        // position (found by /code-review). The genuine lambda cell is
        // `the_row_remainders`' `ti(lambda x -> 7)`, which REFUSES — an arrow is not an
        // `Iterable` — and the refusal is correct by kind, which is why it lives beside
        // the other routes' refusals rather than here.
        (
            "nested call (a combinator result)".into(),
            "  operation c(rs: List[T = Row]) -> Int64 = ti(Iterable.map(rs, lambda x -> x))".into(),
            Verdict::Loads,
        ),
        // THE SET LITERAL, which this table did not exercise at all while the census
        // marked the `list/set literal` position Built in this column on the strength of
        // the LIST row alone (found by /code-review). It REFUSES, and correctly:
        // `prelude/set.anthill` declares `provides PartialEq[T = Set]` and
        // `provides Eq[T = Set]` and NOTHING else, so a `Set` has no chain to `Iterable`
        // — unlike `List`, which provides `Stream` / `FiniteCollection` / `Iterable`
        // outright. The cell is a fact about the stdlib's provision graph, not a gap:
        // the two members of this grid position genuinely differ on this route, which is
        // exactly what a table exists to show.
        (
            "set literal (REFUSES — Set provides no Iterable chain)".into(),
            "  operation c() -> Int64 = ti({1, 2})".into(),
            Verdict::RefusesLocated("expected Iterable, got Set[T = Int64]"),
        ),
        // `match` — an argument position, which WI-20260829-YBBC3 made spellable. It was
        // absent here while the compound forms lived in `_expr_body` alone, and the
        // census recorded the cell as one the LANGUAGE could not express; it is an
        // ordinary cell now.
        (
            "match".into(),
            "  operation c(b: Box) -> Int64 = ti(match b case box(rs) -> rs)".into(),
            Verdict::Loads,
        ),
        //
        // ── the NEGATIVE rows: the slot is not a hole ──
        (
            "NEGATIVE — an Int64 is not an Iterable".into(),
            "  operation c() -> Int64 = ti(1)".into(),
            Verdict::RefusesLocated("expected Iterable, got Int64"),
        ),
        (
            "NEGATIVE — a Row is not an Iterable".into(),
            "  operation c(r: Row) -> Int64 = ti(r)".into(),
            Verdict::RefusesLocated("expected Iterable, got Row"),
        ),
        (
            // NOT a negative for the SLOT, and the distinction matters: member
            // resolution fails BEFORE the argument's type ever reaches `ti`'s parameter,
            // so this row would stay red if the `Iterable` parameter silently became
            // permissive. It is the FIELD-DOT position's own control, and it is kept
            // under that name (found by /code-review). `ti(1)` and `ti(r)` above are the
            // two rows that carry the slot claim.
            "CONTROL — the field-dot POSITION refuses an absent member".into(),
            "  operation c(b: Box) -> Int64 = ti(b.nosuchfield)".into(),
            Verdict::RefusesLocated("no such member"),
        ),
    ];
    run_with(cells, prov_program);
}

/// THE ROW REMAINDERS — `lambda`, `bare op name` and `list/set literal` in the routes the
/// earlier slices did not reach, plus `inline constructor` in a sibling projection. With
/// `every_position_through_a_provision_chain` these are the last cells of the grid.
///
/// BOTH MEMBERS OF THE `list/set literal` POSITION are swept, not just the list: the two
/// differ on the provision-chain route (a `Set` provides no `Iterable` chain), so a table
/// that swept one of them and a census that marked the position Built would have hidden a
/// live refusal — found by /code-review, and the reason each literal route below carries a
/// `[…]` row and a `{…}` row.
///
/// AND WHAT THE LITERAL ROUTES DO NOT CHECK IS RECORDED, not left to a reader. Three
/// `SilentlyAccepted` rows name the holes — 7JDWY on the annotated-let route, and
/// WI-20260829-WBXGX, found here, on the ARGUMENT route that 7JDWY's own table uses as its
/// control: a literal's element type is its FIRST element's, so `takes_list([1, "a"])`
/// loads while `takes_list(["a", 1])` refuses. The reversed-order row is the control that
/// makes that a measurement rather than "literals are unchecked".
///
/// TWO REFUSALS HERE ARE CORRECT BY KIND, not gaps, and they are worth a cell precisely
/// because a reader scanning for red would otherwise have to re-derive that: a lambda and
/// a bare operation name are not `Iterable`s, so the provision-chain route refuses them
/// the way it refuses an `Int64`. They are `RefusesLocated`, and the message is pinned so
/// the cell cannot start passing on some other refusal.
///
/// THE `bare op name` REFUSALS ARE WI-20260828-2TMB5's RULE, seen from two more routes: a
/// non-nullary name needs an arrow to lift against, and neither a free type parameter nor
/// a spec-typed slot supplies one. The `written directly` and `sibling projection` rows
/// are the contrast — both DO supply an arrow, and both load.
///
/// ONE FIXTURE CONFOUND WAS MEASURED AND REMOVED. The lambda rows first used
/// `lambda x -> x + 1`, which refused in the two routes that leave the binder's type
/// open — but with "ambiguous dispatch of Additive.add: 3 instances", a fact about
/// numeric dispatch on an unpinned binder and not about the route. `lambda x -> 7` asks
/// the same question of the route with nothing else varying.
#[test]
fn the_row_remainders() {
    fn rem_program(decl: &str) -> String {
        format!(
            r#"
namespace capmatrix_rem
  import anthill.prelude.{{Int64, Bool, List, Set, Function, Iterable, Option}}
  import anthill.prelude.List.{{cons, nil}}
  sort Rw
    import anthill.prelude.{{Int64}}
    entity rw(a: Int64)
  end
  import capmatrix_rem.Rw.{{rw}}
  operation inc(x: Int64) -> Int64 = x + 1
  operation take_any[A](x: A) -> Int64 = 1
  operation pick(xs: List[T = Int64], e: xs.T) -> Int64 = 1
  operation pick_fn(fs: List[T = Function[A = Int64, B = Int64]], e: fs.T) -> Int64 = 1
  operation pick_rw(xs: List[T = Rw], e: xs.T) -> Int64 = 1
  -- The projection slots whose ELEMENT is itself a collection, so a literal in the
  -- slot is a literal and not an Int64 (see the `list literal / sibling projection`
  -- cell). `pick`'s `xs.T` is `Int64`, which is why it cannot host one.
  operation pick_ll(xss: List[T = List[T = Int64]], e: xss.T) -> Int64 = 1
  operation pick_ss(sss: List[T = Set[T = Int64]], e: sss.T) -> Int64 = 1
  operation takes_list(xs: List[T = Int64]) -> Int64 = 1
  operation takes_set(xs: Set[T = Int64]) -> Int64 = 1
  operation ti(c: Iterable) -> Int64 = 1
{decl}
end
"#
        )
    }
    let cells: Vec<(String, String, Verdict)> = vec![
        // ── lambda ──
        (
            "lambda / written directly (annotated let)".into(),
            "  operation c() -> Int64 =\n    let f: (Int64) -> Int64 = lambda x -> x + 1\n    f(41)".into(),
            Verdict::Loads,
        ),
        (
            "lambda / from a hint (declared return)".into(),
            "  operation c() -> (Int64) -> Int64 = lambda x -> x + 1".into(),
            Verdict::Loads,
        ),
        (
            // A `take_any[A](x: A)` slot unifies `A` with anything, so this cell says the
            // lambda TYPES, not that the route constrains it. The `bare op name / from a
            // type parameter` row below is the one that shows the route is not wholly
            // inert — it REFUSES through the same slot.
            "lambda / from a type parameter (the slot constrains nothing)".into(),
            "  operation c() -> Int64 = take_any(lambda x -> 7)".into(),
            Verdict::Loads,
        ),
        (
            "lambda / through a provision chain (CORRECT — an arrow is no Iterable)".into(),
            "  operation c() -> Int64 = ti(lambda x -> 7)".into(),
            Verdict::RefusesLocated("expected Iterable"),
        ),
        (
            "lambda / from a sibling projection".into(),
            "  operation c(fs: List[T = Function[A = Int64, B = Int64]]) -> Int64 = pick_fn(fs, lambda x -> x + 1)".into(),
            Verdict::Loads,
        ),
        // ── bare operation name ──
        (
            "bare op name / written directly (annotated let)".into(),
            "  operation c() -> Int64 =\n    let f: (Int64) -> Int64 = inc\n    f(41)".into(),
            Verdict::Loads,
        ),
        (
            "bare op name / from a type parameter (CORRECT — no arrow to lift against)".into(),
            "  operation c() -> Int64 = take_any(inc)".into(),
            Verdict::RefusesLocated("supplies no function type to lift it against"),
        ),
        (
            "bare op name / through a provision chain (CORRECT — same rule)".into(),
            "  operation c() -> Int64 = ti(inc)".into(),
            Verdict::RefusesLocated("supplies no function type to lift it against"),
        ),
        (
            "bare op name / from a sibling projection".into(),
            "  operation c(fs: List[T = Function[A = Int64, B = Int64]]) -> Int64 = pick_fn(fs, inc)".into(),
            Verdict::Loads,
        ),
        // ── list / set literal ──
        //
        // BOTH MEMBERS OF THE POSITION, in every route. The first cut swept the LIST
        // alone while the census marked `list/set literal` Built, and the two genuinely
        // differ on one route — a `Set` provides no `Iterable` chain (found by
        // /code-review; the provision-chain refusal is recorded in
        // `every_position_through_a_provision_chain`, where that column lives).
        (
            "list literal / written directly (annotated let)".into(),
            "  operation c() -> Int64 =\n    let xs: List[T = Int64] = [1, 2]\n    1".into(),
            Verdict::Loads,
        ),
        (
            "set literal / written directly (annotated let)".into(),
            "  operation c() -> Int64 =\n    let s: Set[T = Int64] = {1, 2}\n    1".into(),
            Verdict::Loads,
        ),
        (
            "list literal / from a type parameter".into(),
            "  operation c() -> Int64 = take_any([1, 2])".into(),
            Verdict::Loads,
        ),
        (
            "set literal / from a type parameter".into(),
            "  operation c() -> Int64 = take_any({1, 2})".into(),
            Verdict::Loads,
        ),
        (
            "list literal / through a provision chain".into(),
            "  operation c() -> Int64 = ti([1, 2])".into(),
            Verdict::Loads,
        ),
        (
            // A GENUINE list literal in the projection slot. `pick`'s `e: xs.T` is
            // `Int64`, so the first cut's `pick(xs, 1)` put an INTEGER there and the cell
            // would have stayed green with list-literal-into-a-projection broken outright
            // (found by /code-review). `pick_ll`'s element IS a list, so the literal
            // meets the slot.
            "list literal / from a sibling projection".into(),
            "  operation c(xss: List[T = List[T = Int64]]) -> Int64 = pick_ll(xss, [1, 2])"
                .into(),
            Verdict::Loads,
        ),
        (
            "set literal / from a sibling projection".into(),
            "  operation c(sss: List[T = Set[T = Int64]]) -> Int64 = pick_ss(sss, {1})".into(),
            Verdict::Loads,
        ),
        (
            // AND THE SLOT DISCRIMINATES — without this row the two above are consistent
            // with a projection slot accepting anything.
            "NEGATIVE — a list literal into an Int64 projection slot".into(),
            "  operation c(xs: List[T = Int64]) -> Int64 = pick(xs, [1, 2])".into(),
            Verdict::RefusesLocated("expected Int64, got List[T = Int64]"),
        ),
        //
        // ── WHAT THE LITERAL ROUTES DO NOT CHECK, recorded as verdicts rather than left
        // to a reader to infer from four green cells. /code-review's finding was that
        // those cells "cannot refuse"; these three say exactly what each route lets past,
        // so the coverage claim is bounded rather than overstated.
        (
            // The ANNOTATED-LET route: the annotation OVERWRITES the elements instead of
            // checking them, so the row above would be green with the annotation ignored.
            // Same defect as the return-hint rows in
            // `a_literal_is_checked_on_one_route_and_overwritten_on_the_other`.
            "SILENT — an annotated let does not check its literal's elements".into(),
            "  operation c() -> Int64 =\n    let xs: List[T = Int64] = [\"a\", \"b\"]\n    1"
                .into(),
            Verdict::SilentlyAccepted {
                wi: "WI-20260826-7JDWY",
                should_say: "type mismatch: expected Int64, got String",
            },
        ),
        (
            // The TYPE-PARAMETER route accepts anything BY CONSTRUCTION — `take_any[A](x: A)`
            // unifies `A` with whatever arrives — so its literal cell measures the literal
            // and not the route. Stated here rather than left implicit.
            "SILENT — a type parameter accepts a mixed literal (it accepts anything)".into(),
            "  operation c() -> Int64 = take_any([1, \"a\"])".into(),
            Verdict::SilentlyAccepted {
                wi: "WI-20260829-WBXGX",
                should_say: "list element 2 has type String; the literal's elements are Int64",
            },
        ),
        (
            // AND THE ARGUMENT ROUTE, which IS the checking one, lets the same literal
            // past — a distinct hole from 7JDWY, on the very route that ticket's table
            // uses as its control. `takes_list([\"a\"])` refuses; `takes_list([1, \"a\"])`
            // does not, because the element type is element ONE's and the rest ride free.
            "SILENT — a checked ARGUMENT slot takes the first element's type".into(),
            "  operation c() -> Int64 = takes_list([1, \"a\"])".into(),
            Verdict::SilentlyAccepted {
                wi: "WI-20260829-WBXGX",
                should_say: "list element 2 has type String; the literal's elements are Int64",
            },
        ),
        (
            // THE CONTROL THAT MAKES THE TWO ROWS ABOVE A MEASUREMENT: the SAME two
            // elements in the other order DO refuse. Without it "loads" is consistent
            // with the argument route checking nothing at all.
            "CONTROL — the same two elements reversed DO refuse".into(),
            "  operation c() -> Int64 = takes_list([\"a\", 1])".into(),
            Verdict::RefusesLocated("expected List[T = Int64], got List[T = String]"),
        ),
        // ── inline constructor, the one cell outside the three rows above ──
        (
            "inline constructor / from a sibling projection".into(),
            "  operation c(rs: List[T = Rw]) -> Int64 = pick_rw(rs, rw(a: 1))".into(),
            Verdict::Loads,
        ),
    ];
    run_with(cells, rem_program);
}



