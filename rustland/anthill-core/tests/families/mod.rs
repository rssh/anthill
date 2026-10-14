//! WI-20261002-E1WN0 — GENERATED FAMILIES OF PROGRAMS, EACH HELD TO STATED PROPERTIES.
//!
//! A row of `tests/include/` is a program someone thought of. A FAMILY is every program
//! obtained from ONE template by filling a few holes from short lists — the cross
//! product, enumerated, not drawn at random — so the cases of a rule meet each other
//! whether or not anyone thought of the meeting. A family is a value ([`Family`]): its
//! size is known before it runs, a program has a NAME (`hole=label,…`, [`Picks::name`]),
//! and the name is enough to print the program again (`scripts/families.sh print`).
//!
//! ── THE PROPERTIES ───────────────────────────────────────────────────────────
//!
//!  * P1, NO CRASH. Each program loads or is refused. One that overflows the stack,
//!    panics or hangs is NAMED and the run goes on: a stack overflow kills its process,
//!    so the programs are judged in child processes — this test binary run again as
//!    [`worker`] — and the parent reads which program a dead child had begun.
//!  * P2, NO UNEXPLAINED CHANGE. `verdicts/<family>.tsv` is committed: program name →
//!    verdict ([`Verdict`]). A verdict that moves is a line of that file's diff in the
//!    commit that moved it, read by a person.
//!  * P3, SOUNDNESS. A program that loads and has an entry point runs to its value.
//!    `loads; drive fails …` is a program the typer admitted and the interpreter could
//!    not run. And a program its template knows the rule refuses ([`Program::refused`] —
//!    an operation that declares nothing and does something) is refused: one that loads
//!    or runs is `UNSOUND …`, which no other property can see where every spelling of it
//!    is admitted alike.
//!  * P4, ONE VERDICT FOR TWO SPELLINGS. Options of a hole that carry one
//!    [`Opt::same`] tag are one program written two ways, and get one verdict.
//!
//! P1, P3 and P4 hold or the exception is LISTED on the family, with its ticket
//! ([`Exception`]); a listed exception that excuses nothing fails the run as well, so
//! the list cannot outlive the defect.
//!
//! ── HOW IT RUNS ──────────────────────────────────────────────────────────────
//!
//! `scripts/families.sh` — ONE command, and not part of `scripts/test.sh`: [`run`] and
//! [`worker`] are `#[ignore]`d, so the workspace run compiles this module and runs only
//! the tests at its end, which load no program. A child takes a range of a family and
//! judges it on the shared base (`common::load_outcome`), so the standard library is
//! loaded once a process and not once a program.
//!
//! ── CONTROLS ─────────────────────────────────────────────────────────────────
//!
//! Said where each is driven: [`the_runner_names_a_program_that_kills_its_process`]
//! (a dead child is a named verdict and the run goes on),
//! [`a_wrong_line_of_a_verdict_file_is_named`],
//! [`a_program_the_rule_refuses_is_unsound_where_it_is_admitted`], and the back-outs measured
//! against the real families at the head of each family's file.

use crate::common;
use anthill_core::eval::{self, Interpreter};
use anthill_core::kb::load;
use std::collections::BTreeMap;
use std::fmt;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

mod applied_arrow;
mod callback_row;
mod declaration_rule;
mod mutual_callbacks;
mod projected_call;

/// Every family, in the order they run.
fn families() -> Vec<&'static Family> {
    vec![
        &declaration_rule::FAMILY,
        &projected_call::FAMILY,
        &callback_row::FAMILY,
        &mutual_callbacks::FAMILY,
        &applied_arrow::FAMILY,
    ]
}

// ── A family ────────────────────────────────────────────────────────────────

/// One alternative of a hole.
pub struct Opt {
    /// Its part of the program's name.
    pub label: &'static str,
    /// What the template writes there.
    pub text: &'static str,
    /// Options of ONE hole with the same tag are one program written two ways (P4).
    pub same: Option<&'static str>,
}

pub const fn opt(label: &'static str, text: &'static str) -> Opt {
    Opt {
        label,
        text,
        same: None,
    }
}

/// An option that is one of several spellings of `same`.
pub const fn spelt(label: &'static str, text: &'static str, same: &'static str) -> Opt {
    Opt {
        label,
        text,
        same: Some(same),
    }
}

pub struct Hole {
    pub name: &'static str,
    pub options: &'static [Opt],
}

/// A program: a whole file, the entry point it declares where the template drives it,
/// and — where the entry point is no part of what the family is for — the file without
/// it, judged first, so that a refusal of the DRIVER is not read as a refusal of what it
/// drives ([`judge_program`]).
pub struct Program {
    pub source: String,
    /// The entry point's qualified name; it takes nothing and returns an `Int64`.
    pub entry: Option<&'static str>,
    pub subject: Option<String>,
    /// The template knows the rule refuses this program, so a tree that admits it is
    /// unsound ([`Verdict::Unsound`]); `false` where the verdict is the tree's to say.
    pub refused: bool,
}

/// Which property an [`Exception`] is an exception to. P2 has none: the verdict file is
/// the record.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Property {
    NoCrash,
    Sound,
    OneVerdict,
}

impl fmt::Display for Property {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Property::NoCrash => "P1 (no crash)",
            Property::Sound => "P3 (soundness)",
            Property::OneVerdict => "P4 (one verdict for two spellings)",
        })
    }
}

/// A known violation, with the ticket that owns it. `when` is a list of `hole=label`:
/// the exception covers every program that has all of them.
pub struct Exception {
    pub property: Property,
    pub when: &'static [&'static str],
    pub ticket: &'static str,
    pub why: &'static str,
}

pub struct Family {
    pub name: &'static str,
    /// The rule the family is for, in a line.
    pub rule: &'static str,
    pub holes: &'static [Hole],
    pub render: fn(&Picks<'_>) -> Program,
    /// The combinations of the holes that are not programs, if any: the family is the
    /// cross product less these, and says at its site why each is none.
    pub skips: Option<fn(&Picks<'_>) -> bool>,
    /// [`judge_program`] for a family of programs.
    pub judge: fn(&Program) -> Verdict,
    pub exceptions: &'static [Exception],
}

impl Family {
    pub fn len(&self) -> usize {
        match self.skips {
            None => self.product(),
            Some(_) => self.programs().len(),
        }
    }

    fn product(&self) -> usize {
        self.holes.iter().map(|h| h.options.len()).product()
    }

    /// The `at`th member of the cross product: the first hole is the most significant
    /// digit, so the programs of one first option are a contiguous run of the verdict file.
    fn nth(&self, at: usize) -> Picks<'_> {
        let mut rest = at;
        let mut chosen = vec![0; self.holes.len()];
        for (hole_at, hole) in self.holes.iter().enumerate().rev() {
            chosen[hole_at] = rest % hole.options.len();
            rest /= hole.options.len();
        }
        Picks {
            holes: self.holes,
            chosen,
        }
    }

    /// Every program's choices, in order: the cross product, less what `skips` says is no
    /// program.
    pub fn programs(&self) -> Vec<Picks<'_>> {
        (0..self.product())
            .map(|at| self.nth(at))
            .filter(|picks| !self.skips.is_some_and(|skips| skips(picks)))
            .collect()
    }

    /// The `index`th program's choices.
    pub fn picks(&self, index: usize) -> Picks<'_> {
        let picks = match self.skips {
            None => (index < self.product()).then(|| self.nth(index)),
            Some(_) => self.programs().into_iter().nth(index),
        };
        picks.unwrap_or_else(|| panic!("{}: no program {index}", self.name))
    }

    pub fn program(&self, index: usize) -> Program {
        (self.render)(&self.picks(index))
    }

    fn names(&self) -> Vec<String> {
        self.programs().iter().map(Picks::name).collect()
    }

    /// Where a run leaves this tree's verdicts, to diff the committed file against.
    fn found_file(&self) -> PathBuf {
        Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join("families")
            .join(format!("{}.tsv", self.name))
    }

    fn verdict_file(&self) -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/families/verdicts")
            .join(format!("{}.tsv", self.name))
    }
}

/// One program's choice at each hole.
pub struct Picks<'f> {
    holes: &'f [Hole],
    chosen: Vec<usize>,
}

impl Picks<'_> {
    fn opt(&self, hole: &str) -> &Opt {
        let at = self
            .holes
            .iter()
            .position(|h| h.name == hole)
            .unwrap_or_else(|| panic!("the family has no hole `{hole}`"));
        &self.holes[at].options[self.chosen[at]]
    }

    pub fn label(&self, hole: &str) -> &'static str {
        self.opt(hole).label
    }

    pub fn text(&self, hole: &str) -> &'static str {
        self.opt(hole).text
    }

    pub fn is(&self, hole: &str, label: &str) -> bool {
        self.label(hole) == label
    }

    /// `hole=label,…` in the holes' order.
    pub fn name(&self) -> String {
        self.joined(|o| o.label)
    }

    /// The name with each spelling replaced by what it spells: equal for two programs
    /// that are one program written two ways.
    fn spelling_key(&self) -> String {
        self.joined(|o| o.same.unwrap_or(o.label))
    }

    fn joined(&self, part: impl Fn(&Opt) -> &'static str) -> String {
        self.holes
            .iter()
            .zip(&self.chosen)
            .map(|(h, &c)| format!("{}={}", h.name, part(&h.options[c])))
            .collect::<Vec<_>>()
            .join(",")
    }

    fn has(&self, constraint: &str) -> bool {
        let (hole, label) = constraint
            .split_once('=')
            .unwrap_or_else(|| panic!("an exception's `when` is `hole=label`, not `{constraint}`"));
        let at = self
            .holes
            .iter()
            .position(|h| h.name == hole)
            .unwrap_or_else(|| panic!("an exception names the hole `{hole}`, which the family has not"));
        assert!(
            self.holes[at].options.iter().any(|o| o.label == label),
            "an exception names `{constraint}`, and the hole has no such option"
        );
        self.holes[at].options[self.chosen[at]].label == label
    }
}

// ── A verdict ───────────────────────────────────────────────────────────────

/// What the tree does with one program. The text ([`fmt::Display`]) is the verdict
/// file's second column.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Verdict {
    /// Loads, and the template has no entry point for it.
    Loads,
    /// Loads, and its entry point ran to this value.
    Runs(String),
    /// Refused at load: the refusals' classes, sorted, `+` between them.
    Refused(String),
    /// Loads; with its entry point it is refused.
    DriveRefused(String),
    /// Loads with its entry point, and the entry point did not run — a P3 violation.
    DriveFails(String),
    /// Admitted — loaded, or ran to a value — where the template says the rule refuses it:
    /// what was admitted, as [`Verdict::Loads`] or [`Verdict::Runs`] write it. A P3 violation.
    Unsound(String),
    /// The process judging it died — a P1 violation.
    Died(String),
    /// Nothing came back within the run's patience — a P1 violation.
    Hung,
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Verdict::Loads => f.write_str("loads"),
            Verdict::Runs(value) => write!(f, "runs {value}"),
            Verdict::Refused(classes) => write!(f, "refused {classes}"),
            Verdict::DriveRefused(classes) => write!(f, "loads; drive refused {classes}"),
            Verdict::DriveFails(class) => write!(f, "loads; drive fails {class}"),
            Verdict::Unsound(admitted) => write!(f, "UNSOUND {admitted}"),
            Verdict::Died(how) => write!(f, "DIED {how}"),
            Verdict::Hung => f.write_str("HUNG"),
        }
    }
}

impl Verdict {
    fn parse(text: &str) -> Option<Verdict> {
        let tail = |prefix: &str| text.strip_prefix(prefix).map(str::to_string);
        if text == "loads" {
            Some(Verdict::Loads)
        } else if text == "HUNG" {
            Some(Verdict::Hung)
        } else if let Some(v) = tail("runs ") {
            Some(Verdict::Runs(v))
        } else if let Some(v) = tail("refused ") {
            Some(Verdict::Refused(v))
        } else if let Some(v) = tail("loads; drive refused ") {
            Some(Verdict::DriveRefused(v))
        } else if let Some(v) = tail("loads; drive fails ") {
            Some(Verdict::DriveFails(v))
        } else if let Some(v) = tail("UNSOUND ") {
            Some(Verdict::Unsound(v))
        } else {
            tail("DIED ").map(Verdict::Died)
        }
    }

    /// The property this verdict alone violates, if any.
    fn violates(&self) -> Option<Property> {
        match self {
            Verdict::Died(_) | Verdict::Hung => Some(Property::NoCrash),
            Verdict::DriveFails(_) | Verdict::Unsound(_) => Some(Property::Sound),
            _ => None,
        }
    }
}

/// A refusal's CLASS: which `LoadError` it is; for the typer's catch-all the kind of place
/// it was raised at; for a member that does not fit its spec, which leg refused and at
/// which parameter. Not its text — a reworded message is not a moved verdict.
fn refusal_classes(errors: &[load::LoadError]) -> String {
    let mut classes: Vec<String> = errors
        .iter()
        .map(|e| match e.peel() {
            load::LoadError::TypeMismatch {
                origin: Some(origin),
                ..
            } => format!("TypeMismatch/{}", origin.context_kind),
            load::LoadError::IncompatibleMemberSignature { misfit, .. } => {
                format!("IncompatibleMemberSignature/{misfit}")
            }
            other => variant_name(other),
        })
        .collect();
    classes.sort();
    classes.dedup();
    classes.join("+")
}

/// The variant's name, off its `Debug` text.
fn variant_name(value: &dyn fmt::Debug) -> String {
    let text = format!("{value:?}");
    let end = text
        .find(|c: char| !(c.is_alphanumeric() || c == '_'))
        .unwrap_or(text.len());
    text[..end].to_string()
}

/// A program's verdict, in this process: its subject, where it has one apart from the
/// whole file; then the file, loaded and — where it declares an entry point — called.
pub fn judge_program(program: &Program) -> Verdict {
    held_to_its_refusal(program, judged(program))
}

/// What the tree did with `program`, read against what its template knows: a program the rule
/// refuses ([`Program::refused`]) that the tree admitted is [`Verdict::Unsound`].
fn held_to_its_refusal(program: &Program, verdict: Verdict) -> Verdict {
    match verdict {
        admitted @ (Verdict::Loads | Verdict::Runs(_)) if program.refused => {
            Verdict::Unsound(admitted.to_string())
        }
        verdict => verdict,
    }
}

/// [`judge_program`] before the template's expectation is read.
fn judged(program: &Program) -> Verdict {
    if let Some(subject) = &program.subject {
        let refusals = common::load_outcome(subject).errors();
        if !refusals.is_empty() {
            return Verdict::Refused(refusal_classes(&refusals));
        }
    }
    let kb = match common::load_outcome(&program.source).into_result() {
        Ok(kb) => kb,
        Err(refusals) if program.subject.is_some() => {
            return Verdict::DriveRefused(refusal_classes(&refusals))
        }
        Err(refusals) => return Verdict::Refused(refusal_classes(&refusals)),
    };
    let Some(entry) = program.entry else {
        return Verdict::Loads;
    };
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp).expect("register standard eval builtins");
    match interp.call(entry, &[]) {
        Ok(eval::Value::Int(value)) => Verdict::Runs(value.to_string()),
        Ok(other) => Verdict::DriveFails(format!("NotAnInt64/{}", variant_name(&other))),
        Err(error) => Verdict::DriveFails(variant_name(&error)),
    }
}

// ── The runner ──────────────────────────────────────────────────────────────

/// `<family>:<from>..<to>` — the range a [`worker`] judges.
const WORK_ENV: &str = "ANTHILL_FAMILY_WORK";
/// Where a [`worker`] writes what it began and what it found.
const LOG_ENV: &str = "ANTHILL_FAMILY_LOG";

/// What a [`worker`] prints before each program, so that what follows is that program's.
const BEGINS: &str = "family program ";

/// The stack a program is judged on: a process's main thread on Linux and macOS, which
/// is where `anthill load` loads. A test thread's 2 MiB would call a deep program a
/// crash that the product loads.
const JUDGE_STACK: usize = 8 * 1024 * 1024;

pub struct RunOptions {
    /// Child processes at a time.
    pub jobs: usize,
    /// How long a child may go without beginning or finishing a program.
    pub patience: Duration,
}

impl RunOptions {
    /// `ANTHILL_FAMILY_JOBS` (default: the CPU count) and `ANTHILL_FAMILY_PATIENCE_SECS`
    /// (default 120: an unoptimized child's first program pays the stdlib's load).
    fn from_env() -> RunOptions {
        let number = |name: &str| {
            std::env::var(name).ok().map(|v| {
                v.parse::<u64>()
                    .unwrap_or_else(|_| panic!("{name}={v}: not a number"))
            })
        };
        let cpus = std::thread::available_parallelism().map_or(4, |n| n.get());
        RunOptions {
            jobs: number("ANTHILL_FAMILY_JOBS").map_or(cpus, |n| n.max(1) as usize),
            patience: Duration::from_secs(number("ANTHILL_FAMILY_PATIENCE_SECS").unwrap_or(120)),
        }
    }
}

/// A child that died or was killed, and the end of what it printed.
pub struct Death {
    pub program: usize,
    pub said: String,
}

pub struct Outcome {
    pub verdicts: Vec<Verdict>,
    pub deaths: Vec<Death>,
    pub elapsed: Duration,
    /// Child processes started — one a range, and one more for each death.
    pub children: usize,
}

/// Every program of `family`, judged in child processes.
pub fn run_family(family: &'static Family, options: &RunOptions) -> Outcome {
    let started = Instant::now();
    let total = family.len();
    let jobs = options.jobs.min(total).max(1);
    // Ranges are handed out as children finish, so they need only be small beside a
    // job's share; each costs its child one stdlib load.
    let range = total.div_ceil(jobs * 4).clamp(1, 64);
    let next = AtomicUsize::new(0);
    let verdicts: Mutex<Vec<Option<Verdict>>> = Mutex::new(vec![None; total]);
    let deaths = Mutex::new(Vec::new());
    let children = AtomicUsize::new(0);
    let scratch = tempfile::tempdir().expect("a scratch directory for the workers' logs");
    std::thread::scope(|scope| {
        for _ in 0..jobs {
            scope.spawn(|| loop {
                let from = next.fetch_add(range, Ordering::Relaxed);
                if from >= total {
                    break;
                }
                let to = (from + range).min(total);
                run_range(family, from, to, options, scratch.path(), &verdicts, &deaths, &children);
            });
        }
    });
    let verdicts = verdicts
        .into_inner()
        .expect("no job panicked holding the verdicts")
        .into_iter()
        .enumerate()
        .map(|(i, v)| v.unwrap_or_else(|| panic!("{}: program {i} was never judged", family.name)))
        .collect();
    let mut deaths = deaths.into_inner().expect("no job panicked holding the deaths");
    deaths.sort_by_key(|d: &Death| d.program);
    Outcome {
        verdicts,
        deaths,
        elapsed: started.elapsed(),
        children: children.into_inner(),
    }
}

/// `from..to`, in as many children as it takes: a child that dies on a program is that
/// program's verdict, and the next child starts after it.
#[allow(clippy::too_many_arguments)]
fn run_range(
    family: &'static Family,
    mut from: usize,
    to: usize,
    options: &RunOptions,
    scratch: &Path,
    verdicts: &Mutex<Vec<Option<Verdict>>>,
    deaths: &Mutex<Vec<Death>>,
    children: &AtomicUsize,
) {
    while from < to {
        let log = scratch.join(format!("{}-{from}.log", family.name));
        let said_path = scratch.join(format!("{}-{from}.out", family.name));
        children.fetch_add(1, Ordering::Relaxed);
        let (status, killed) = run_worker(family, from, to, &log, &said_path, options.patience);
        let said = std::fs::read_to_string(&said_path).unwrap_or_default();
        let mut begun = None;
        let mut judged = from;
        for line in std::fs::read_to_string(&log).unwrap_or_default().lines() {
            let fields: Vec<&str> = line.splitn(3, '\t').collect();
            match fields[..] {
                ["B", index] => begun = Some(index.parse::<usize>().expect("a program's index")),
                ["E", index, verdict] => {
                    let index: usize = index.parse().expect("a program's index");
                    let verdict = Verdict::parse(verdict)
                        .unwrap_or_else(|| panic!("a worker wrote the verdict `{verdict}`"));
                    verdicts.lock().expect("verdicts")[index] = Some(verdict);
                    begun = None;
                    judged = index + 1;
                }
                // A line the child had not finished writing when it died.
                _ => {}
            }
        }
        match begun {
            Some(index) => {
                let verdict = if killed {
                    Verdict::Hung
                } else {
                    // What it printed for THIS program, not for the ones before it.
                    let begins = format!("{BEGINS}{index}\n");
                    let on_it = said.rsplit_once(&begins).map_or(said.as_str(), |(_, after)| after);
                    Verdict::Died(how_it_died(status, on_it))
                };
                verdicts.lock().expect("verdicts")[index] = Some(verdict);
                deaths.lock().expect("deaths").push(Death {
                    program: index,
                    said: last_lines(&said, 12),
                });
                from = index + 1;
            }
            None if status.success() && judged == to => from = to,
            None => panic!(
                "{}: the worker for {from}..{to} ended ({status}{}) outside any program, having \
                 judged up to {judged} — the runner's own failure, not a program's:\n{}",
                family.name,
                if killed { ", killed for silence" } else { "" },
                last_lines(&said, 40),
            ),
        }
    }
}

/// How long a child may take to write its first line: the binary's start, not a
/// program's silence, and long on a machine whose every core is running tests.
const STARTING: Duration = Duration::from_secs(300);

/// One child over `from..to`: its exit status, and whether it was killed for going
/// `patience` without a line.
fn run_worker(
    family: &Family,
    from: usize,
    to: usize,
    log: &Path,
    said: &Path,
    patience: Duration,
) -> (std::process::ExitStatus, bool) {
    let said = std::fs::File::create(said).expect("the worker's output file");
    let mut child = std::process::Command::new(std::env::current_exe().expect("this test binary"))
        .args(["--ignored", "--exact", &test_name("worker"), "--nocapture", "--test-threads=1"])
        .env(WORK_ENV, format!("{}:{from}..{to}", family.name))
        .env(LOG_ENV, log)
        .stdout(said.try_clone().expect("the worker's output file, again"))
        .stderr(said)
        .spawn()
        .expect("start a worker");
    let mut seen = 0;
    let mut since = Instant::now();
    loop {
        if let Some(status) = child.try_wait().expect("ask after the worker") {
            return (status, false);
        }
        let written = std::fs::metadata(log).map_or(0, |m| m.len());
        if written != seen {
            seen = written;
            since = Instant::now();
        } else if since.elapsed() > if seen == 0 { patience.max(STARTING) } else { patience } {
            // `kill` fails only on a child that has already gone, which `wait` reads.
            let _ = child.kill();
            return (child.wait().expect("the killed worker's status"), true);
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

/// A test of this module as libtest names it — the module path without the crate.
fn test_name(test: &str) -> String {
    let module = module_path!().split_once("::").map_or("", |(_, m)| m);
    format!("{module}::{test}")
}

fn how_it_died(status: std::process::ExitStatus, said: &str) -> String {
    if said.contains("has overflowed its stack") {
        return "stack overflow".to_string();
    }
    if said.contains("panicked at") {
        return "panic".to_string();
    }
    #[cfg(unix)]
    if let Some(signal) = std::os::unix::process::ExitStatusExt::signal(&status) {
        return format!("signal {signal}");
    }
    match status.code() {
        Some(code) => format!("exit {code}"),
        None => "no exit code".to_string(),
    }
}

fn last_lines(text: &str, count: usize) -> String {
    let lines: Vec<&str> = text.lines().collect();
    lines[lines.len().saturating_sub(count)..].join("\n")
}

/// THE CHILD. Judges `ANTHILL_FAMILY_WORK`'s range one program at a time, writing a `B`
/// line before each and an `E` line with the verdict after, so that a process which dies
/// has said which program it died on. Run on its own it has no work and does nothing.
#[test]
#[ignore = "a child process of `run`: it has work only when `run` starts it"]
fn worker() {
    let Ok(work) = std::env::var(WORK_ENV) else {
        return;
    };
    let log = std::env::var(LOG_ENV).unwrap_or_else(|_| panic!("{WORK_ENV} without {LOG_ENV}"));
    let (name, range) = work
        .split_once(':')
        .unwrap_or_else(|| panic!("{WORK_ENV}={work}: not `<family>:<from>..<to>`"));
    let (from, to) = range
        .split_once("..")
        .unwrap_or_else(|| panic!("{WORK_ENV}={work}: not `<family>:<from>..<to>`"));
    let (from, to): (usize, usize) = (from.parse().expect("from"), to.parse().expect("to"));
    let family = family_named(name);
    let judged = std::thread::Builder::new()
        .stack_size(JUDGE_STACK)
        .spawn(move || {
            let mut log = std::fs::File::create(log).expect("the worker's log");
            for index in from..to {
                eprintln!("{BEGINS}{index}");
                writeln!(log, "B\t{index}").expect("write the log");
                let verdict = (family.judge)(&family.program(index));
                writeln!(log, "E\t{index}\t{verdict}").expect("write the log");
            }
        })
        .expect("start the judging thread")
        .join();
    assert!(judged.is_ok(), "a program panicked the judging thread");
}

fn family_named(name: &str) -> &'static Family {
    if name == FAULTS.name {
        return &FAULTS;
    }
    families()
        .into_iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no family `{name}`"))
}

// ── The properties ──────────────────────────────────────────────────────────

/// One thing wrong, naming its program.
#[derive(Debug, PartialEq, Eq)]
pub struct Finding {
    pub program: String,
    pub what: String,
}

/// What a family's verdicts say against P1, P3 and P4, the listed exceptions taken off:
/// the violations no exception covers, and the exceptions that covered nothing.
pub fn property_findings(family: &Family, verdicts: &[Verdict]) -> Vec<Finding> {
    let programs = family.programs();
    assert_eq!(programs.len(), verdicts.len(), "{}: a verdict a program", family.name);
    let mut findings = Vec::new();
    let mut used = vec![false; family.exceptions.len()];
    let covering = |picks: &Picks<'_>, property: Property| {
        family
            .exceptions
            .iter()
            .enumerate()
            .filter(|(_, e)| e.property == property && e.when.iter().all(|c| picks.has(c)))
            .map(|(at, _)| at)
            .collect::<Vec<usize>>()
    };

    // P1 and P3: a verdict that is a violation by itself.
    for (index, verdict) in verdicts.iter().enumerate() {
        let Some(property) = verdict.violates() else {
            continue;
        };
        let picks = &programs[index];
        // Every exception that covers it is live, not the first alone.
        let excused = covering(picks, property);
        if excused.is_empty() {
            findings.push(Finding {
                program: picks.name(),
                what: match verdict {
                    Verdict::Unsound(_) => format!("{property}: {verdict}, where the template says the rule refuses it"),
                    _ => format!("{property}: {verdict}"),
                },
            });
        }
        for exception in excused {
            used[exception] = true;
        }
    }

    // P4: the programs that are one program written two ways, by what they spell.
    let mut spelt: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for index in 0..verdicts.len() {
        spelt.entry(programs[index].spelling_key()).or_default().push(index);
    }
    for members in spelt.values().filter(|m| m.len() > 1) {
        // A spelling an exception covers is set aside; it is a LIVE exception only where
        // its verdict does differ from a spelling beside it.
        let (excepted, held): (Vec<usize>, Vec<usize>) = members
            .iter()
            .partition(|&&i| !covering(&programs[i], Property::OneVerdict).is_empty());
        for &index in &excepted {
            if members.iter().any(|&other| verdicts[other] != verdicts[index]) {
                for exception in covering(&programs[index], Property::OneVerdict) {
                    used[exception] = true;
                }
            }
        }
        let Some((&first, rest)) = held.split_first() else {
            continue;
        };
        if rest.iter().any(|&i| verdicts[i] != verdicts[first]) {
            // Each verdict once, with how many spellings got it and the first of them.
            let mut by_verdict: Vec<(&Verdict, usize, usize)> = Vec::new();
            for &i in &held {
                match by_verdict.iter_mut().find(|(v, _, _)| *v == &verdicts[i]) {
                    Some((_, count, _)) => *count += 1,
                    None => by_verdict.push((&verdicts[i], 1, i)),
                }
            }
            let spellings = by_verdict
                .iter()
                .map(|(verdict, count, i)| format!("\n      {count} × `{verdict}`, as {}", programs[*i].name()))
                .collect::<String>();
            findings.push(Finding {
                program: programs[first].name(),
                what: format!("{}: one program, written {} ways:{spellings}", Property::OneVerdict, held.len()),
            });
        }
    }

    for (exception, _) in family.exceptions.iter().zip(&used).filter(|(_, &u)| !u) {
        findings.push(Finding {
            program: exception.when.join(","),
            what: format!(
                "a listed exception to {} ({}: {}) excuses nothing on this tree — take it off the family",
                exception.property, exception.ticket, exception.why
            ),
        });
    }
    findings
}

/// The verdict file's text for these verdicts.
pub fn verdict_text(family: &Family, verdicts: &[Verdict]) -> String {
    let mut text = format!(
        "# {} — {}\n# {} programs: name, tab, verdict. Written by `scripts/families.sh bless`; \
         a changed line is a changed verdict.\n",
        family.name,
        family.rule,
        family.len()
    );
    for (name, verdict) in family.names().iter().zip(verdicts) {
        text.push_str(&format!("{name}\t{verdict}\n"));
    }
    text
}

/// A verdict file's rows, in its order. A line that is not `name<TAB>verdict` is loud.
fn recorded_rows(recorded: &str) -> Vec<(&str, &str)> {
    recorded
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
        .map(|l| {
            l.split_once('\t')
                .unwrap_or_else(|| panic!("a verdict file's line is `name<TAB>verdict`, not `{l}`"))
        })
        .collect()
}

/// P2: where the tree's verdicts differ from the file's.
pub fn recorded_differences(family: &Family, verdicts: &[Verdict], recorded: &str) -> Vec<Finding> {
    let mut findings = name_differences(family, recorded);
    let recorded: BTreeMap<&str, &str> = recorded_rows(recorded).into_iter().collect();
    for (name, verdict) in family.names().into_iter().zip(verdicts) {
        if let Some(&was) = recorded.get(name.as_str()) {
            if was != verdict.to_string() {
                findings.push(Finding {
                    program: name,
                    what: format!("the verdict file says `{was}`, this tree says `{verdict}`"),
                });
            }
        }
    }
    findings
}

/// The programs the file has and the family has not, and the other way round — what a
/// changed template leaves behind, found without running a program.
fn name_differences(family: &Family, recorded: &str) -> Vec<Finding> {
    let names = family.names();
    let rows: Vec<&str> = recorded_rows(recorded).into_iter().map(|(name, _)| name).collect();
    let mut findings = Vec::new();
    for (at, row) in rows.iter().enumerate() {
        if rows[..at].contains(row) {
            findings.push(Finding {
                program: row.to_string(),
                what: "the verdict file has two lines for it".to_string(),
            });
        }
    }
    for name in &names {
        if !rows.contains(&name.as_str()) {
            findings.push(Finding {
                program: name.clone(),
                what: "the verdict file has no line for it".to_string(),
            });
        }
    }
    for row in rows {
        if !names.iter().any(|n| n == row) {
            findings.push(Finding {
                program: row.to_string(),
                what: "the verdict file has a line for it, and the family has no such program".to_string(),
            });
        }
    }
    findings
}

fn render_findings(findings: &[Finding], limit: usize) -> String {
    let mut text: String = findings
        .iter()
        .take(limit)
        .map(|f| format!("  {}\n    {}\n", f.program, f.what))
        .collect();
    if findings.len() > limit {
        text.push_str(&format!("  … and {} more\n", findings.len() - limit));
    }
    text
}

// ── The command ─────────────────────────────────────────────────────────────

/// Family names, comma-separated; a name's leading part is enough. Unset: every family.
const SELECT_ENV: &str = "ANTHILL_FAMILIES";
/// `1`: write each verdict file from this tree before comparing.
const BLESS_ENV: &str = "ANTHILL_FAMILIES_BLESS";
/// `<family>:<program name>` — print that program. Or a directory, with
/// [`DUMP_ENV`], to write every program into.
const PRINT_ENV: &str = "ANTHILL_FAMILIES_PRINT";
const DUMP_ENV: &str = "ANTHILL_FAMILIES_DUMP";

fn selected_families() -> Vec<&'static Family> {
    let all = families();
    let Ok(wanted) = std::env::var(SELECT_ENV) else {
        return all;
    };
    if wanted.is_empty() {
        return all;
    }
    wanted
        .split(',')
        .map(|w| {
            let matching: Vec<&&Family> = all.iter().filter(|f| f.name.starts_with(w)).collect();
            match matching[..] {
                [one] => *one,
                _ => panic!(
                    "{SELECT_ENV}={wanted}: `{w}` names {} of the families {:?}",
                    matching.len(),
                    all.iter().map(|f| f.name).collect::<Vec<_>>()
                ),
            }
        })
        .collect()
}

/// THE RUN: every selected family, every program, P1–P4. `scripts/families.sh`.
#[test]
#[ignore = "the generated families: `scripts/families.sh`, not part of the workspace run"]
fn run() {
    let options = RunOptions::from_env();
    let bless = std::env::var(BLESS_ENV).is_ok_and(|v| v == "1");
    let mut failed = Vec::new();
    for family in selected_families() {
        let outcome = run_family(family, &options);
        println!(
            "\n── {} — {} programs, {:.1} s, {} child processes, {} at a time ──",
            family.name,
            family.len(),
            outcome.elapsed.as_secs_f64(),
            outcome.children,
            options.jobs
        );
        let mut tally: BTreeMap<String, usize> = BTreeMap::new();
        for verdict in &outcome.verdicts {
            *tally.entry(verdict.to_string()).or_default() += 1;
        }
        for (verdict, count) in &tally {
            println!("  {count:>6}  {verdict}");
        }
        // The end of what a dead child printed, for the first few: one defect kills a
        // slab of a cross product, and every name is in the verdicts written below.
        for death in outcome.deaths.iter().take(3) {
            println!(
                "  {} — {}; its process ended with:\n{}",
                family.picks(death.program).name(),
                outcome.verdicts[death.program],
                death.said.lines().map(|l| format!("      {l}\n")).collect::<String>()
            );
        }
        let found = family.found_file();
        std::fs::create_dir_all(found.parent().expect("the scratch directory"))
            .and_then(|()| std::fs::write(&found, verdict_text(family, &outcome.verdicts)))
            .unwrap_or_else(|e| panic!("write {}: {e}", found.display()));

        let path = family.verdict_file();
        if bless {
            std::fs::create_dir_all(path.parent().expect("the verdicts directory"))
                .and_then(|()| std::fs::write(&path, verdict_text(family, &outcome.verdicts)))
                .unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
            println!("  wrote {}", path.display());
        }
        let recorded = std::fs::read_to_string(&path).unwrap_or_else(|e| {
            panic!(
                "{}: {e} — a family has a committed verdict file; `scripts/families.sh bless` writes it",
                path.display()
            )
        });
        let moved = recorded_differences(family, &outcome.verdicts, &recorded);
        let broken = property_findings(family, &outcome.verdicts);
        if !moved.is_empty() {
            println!(
                "  P2 — {} verdicts differ from {}:\n{}",
                moved.len(),
                path.display(),
                render_findings(&moved, 60)
            );
        }
        if !broken.is_empty() {
            println!("  {} findings against P1, P3, P4:\n{}", broken.len(), render_findings(&broken, 60));
        }
        if !(moved.is_empty() && broken.is_empty()) {
            println!("  every verdict of this tree: diff {} {}", path.display(), found.display());
            failed.push(format!("{}: {} moved, {} findings", family.name, moved.len(), broken.len()));
        }
    }
    assert!(failed.is_empty(), "the families do not hold: {failed:?} — each is named above");
}

/// PRINT ONE PROGRAM, OR WRITE THEM ALL: `scripts/families.sh print|dump`.
#[test]
#[ignore = "prints or writes the families' programs: `scripts/families.sh print|dump`"]
fn show() {
    if let Ok(which) = std::env::var(PRINT_ENV) {
        let (name, program) = which
            .split_once(':')
            .unwrap_or_else(|| panic!("{PRINT_ENV}={which}: not `<family>:<program name>`"));
        let family = family_named(name);
        let index = family
            .names()
            .iter()
            .position(|n| n == program)
            .unwrap_or_else(|| panic!("{}: no program `{program}`", family.name));
        let program = family.program(index);
        println!("{}", program.source);
        // Judged HERE, after the text is out: a program that kills its process has
        // been printed first.
        println!("# ── on this tree ──");
        if let Some(subject) = &program.subject {
            for refusal in common::load_errors_of(subject) {
                println!("# without its entry point, refused: {refusal}");
            }
        }
        for refusal in common::load_errors_of(&program.source) {
            println!("# refused: {refusal}");
        }
        println!("# verdict: {}", (family.judge)(&program));
    }
    if let Ok(dir) = std::env::var(DUMP_ENV) {
        for family in selected_families() {
            let into = Path::new(&dir).join(family.name);
            std::fs::create_dir_all(&into).unwrap_or_else(|e| panic!("create {}: {e}", into.display()));
            for index in 0..family.len() {
                let source = family.program(index).source;
                let path = into.join(format!("{}.anthill", family.picks(index).name()));
                std::fs::write(&path, source).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
            }
            println!("{}: {} programs under {}", family.name, family.len(), into.display());
        }
    }
}

// ── In the workspace run: the runner's own controls, and what needs no program ──

/// A family that loads nothing: its programs are faults, for the runner's controls.
static FAULTS: Family = Family {
    name: "runner-faults",
    rule: "the runner's own controls",
    holes: &[Hole {
        name: "does",
        options: &[
            opt("nothing-1", "ok"),
            opt("overflows", "overflow"),
            opt("nothing-2", "ok"),
            opt("panics", "panic"),
            opt("nothing-3", "ok"),
            opt("hangs", "hang"),
            opt("nothing-4", "ok"),
        ],
    }],
    render: |picks| Program {
        source: picks.text("does").to_string(),
        entry: None,
        subject: None,
        refused: false,
    },
    skips: None,
    judge: |program| match program.source.as_str() {
        "ok" => Verdict::Loads,
        "overflow" => Verdict::Runs(recurse_without_end(0).to_string()),
        "panic" => panic!("a program that panics its judge"),
        "hang" => loop {
            std::thread::sleep(Duration::from_secs(1));
        },
        other => panic!("no fault `{other}`"),
    },
    exceptions: &[],
};

#[allow(unconditional_recursion)]
fn recurse_without_end(depth: u64) -> u64 {
    let frame = std::hint::black_box([depth; 32]);
    recurse_without_end(depth + 1) + frame[0]
}

/// CONTROL — A PROGRAM THAT KILLS ITS PROCESS IS A NAMED VERDICT, AND THE RUN GOES ON. Three
/// of the seven die three ways — a real stack overflow, a panic, silence — and each is
/// its own verdict with the four around them judged: four children, one for the range and
/// one after each death. With `run_range` not restarting after a death (`from = to`) this
/// fails "program 2 was never judged".
#[test]
fn the_runner_names_a_program_that_kills_its_process() {
    let outcome = run_family(
        &FAULTS,
        &RunOptions {
            jobs: 1,
            patience: Duration::from_secs(3),
        },
    );
    let verdicts: Vec<String> = outcome.verdicts.iter().map(Verdict::to_string).collect();
    assert_eq!(
        verdicts,
        ["loads", "DIED stack overflow", "loads", "DIED panic", "loads", "HUNG", "loads"]
    );
    assert_eq!(outcome.children, 4);
    let died: Vec<String> = outcome.deaths.iter().map(|d| FAULTS.picks(d.program).name()).collect();
    assert_eq!(died, ["does=overflows", "does=panics", "does=hangs"]);
    // … and each is a finding against P1, by name.
    let findings = property_findings(&FAULTS, &outcome.verdicts);
    assert_eq!(
        findings.iter().map(|f| f.program.as_str()).collect::<Vec<_>>(),
        ["does=overflows", "does=panics", "does=hangs"]
    );
}

/// THE VERDICT FILES NAME THE FAMILIES' PROGRAMS — without running one: a template that
/// gained or lost a program since its file was written fails here, in the workspace run,
/// and `scripts/families.sh bless` is the repair. And the three families are the size the
/// ticket asks for.
#[test]
fn every_verdict_file_names_its_familys_programs() {
    let mut total = 0;
    for family in families() {
        let path = family.verdict_file();
        let recorded =
            std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let stale = name_differences(family, &recorded);
        assert!(
            stale.is_empty(),
            "{} is not this template's — `scripts/families.sh bless {}`:\n{}",
            path.display(),
            family.name,
            render_findings(&stale, 20)
        );
        for (name, verdict) in recorded_rows(&recorded) {
            assert!(Verdict::parse(verdict).is_some(), "{}: `{name}` has the verdict `{verdict}`", path.display());
        }
        total += family.len();
    }
    assert!(total >= 1000, "the families hold {total} programs");
}

/// Three programs, two of them one program written two ways.
const SPELLINGS: &[Hole] = &[Hole {
    name: "x",
    options: &[spelt("braced", "{E}", "row"), spelt("bare", "E", "row"), opt("other", "F")],
}];

fn spellings(exceptions: &'static [Exception]) -> Family {
    Family {
        name: "spellings",
        rule: "the properties' own controls",
        holes: SPELLINGS,
        render: |_| unreachable!("judged by hand"),
        skips: None,
        judge: |_| unreachable!("judged by hand"),
        exceptions,
    }
}

/// CONTROL — A WRONG LINE OF A VERDICT FILE IS NAMED (P2): one line of three edited, and the
/// one finding is that program with both verdicts. A line for a program the family has
/// not, and a program the file has no line for, are named as well.
#[test]
fn a_wrong_line_of_a_verdict_file_is_named() {
    let family = spellings(&[]);
    let verdicts = [Verdict::Loads, Verdict::Loads, Verdict::Refused("UnresolvedName".into())];
    let recorded = verdict_text(&family, &verdicts);
    assert_eq!(recorded_differences(&family, &verdicts, &recorded), []);

    let edited = recorded.replace("x=bare\tloads", "x=bare\trefused TypeMismatch/op-arg");
    assert_eq!(
        recorded_differences(&family, &verdicts, &edited),
        [Finding {
            program: "x=bare".into(),
            what: "the verdict file says `refused TypeMismatch/op-arg`, this tree says `loads`".into(),
        }]
    );

    let twice = format!("{recorded}x=bare\tloads\n");
    assert_eq!(
        recorded_differences(&family, &verdicts, &twice),
        [Finding {
            program: "x=bare".into(),
            what: "the verdict file has two lines for it".into(),
        }]
    );

    let renamed = recorded.replace("x=other\t", "x=another\t");
    let named: Vec<String> = recorded_differences(&family, &verdicts, &renamed)
        .into_iter()
        .map(|f| f.program)
        .collect();
    assert_eq!(named, ["x=other", "x=another"]);
}

/// CONTROL — A PROGRAM THE RULE REFUSES IS UNSOUND WHERE IT IS ADMITTED (P3): one the
/// template marks refused that loads or runs is `UNSOUND`, a P3 finding, and reads back from a
/// verdict file as itself; refused, it is the refusal; unmarked, it is what the tree said.
#[test]
fn a_program_the_rule_refuses_is_unsound_where_it_is_admitted() {
    let program = |refused| Program {
        source: String::new(),
        entry: None,
        subject: None,
        refused,
    };
    let runs = || Verdict::Runs("7".into());
    assert_eq!(held_to_its_refusal(&program(true), runs()), Verdict::Unsound("runs 7".into()));
    assert_eq!(held_to_its_refusal(&program(true), Verdict::Loads), Verdict::Unsound("loads".into()));
    let refusal = || Verdict::Refused("TypeMismatch/op-effects".into());
    assert_eq!(held_to_its_refusal(&program(true), refusal()), refusal());
    assert_eq!(held_to_its_refusal(&program(false), runs()), runs());

    let unsound = Verdict::Unsound("runs 7".into());
    assert_eq!(unsound.to_string(), "UNSOUND runs 7");
    assert_eq!(Verdict::parse(&unsound.to_string()), Some(unsound.clone()));
    assert_eq!(unsound.violates(), Some(Property::Sound));
    let found = property_findings(&spellings(&[]), &[Verdict::Loads, Verdict::Loads, unsound]);
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].program, "x=other");
    assert!(found[0].what.contains("UNSOUND runs 7, where the template says"), "{found:?}");
}

/// CONTROL — TWO SPELLINGS, TWO VERDICTS, ONE FINDING (P4); a listed exception takes the
/// spelling out of it; and an exception that excuses nothing is itself a finding.
#[test]
fn two_verdicts_for_two_spellings_are_named() {
    const LISTED: &[Exception] = &[Exception {
        property: Property::OneVerdict,
        when: &["x=bare"],
        ticket: "WI-0",
        why: "a bare row is read otherwise",
    }];
    let agree = [Verdict::Loads, Verdict::Loads, Verdict::Hung];
    let differ = [Verdict::Loads, Verdict::Refused("TypeMismatch".into()), Verdict::Loads];

    // The third program is no spelling of the other two: its own verdict is not theirs to
    // share — only its P1 finding is reported.
    let found = property_findings(&spellings(&[]), &agree);
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].program, "x=other");

    let found = property_findings(&spellings(&[]), &differ);
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].program, "x=braced");
    assert!(found[0].what.contains("1 × `refused TypeMismatch`, as x=bare"), "{found:?}");

    assert_eq!(property_findings(&spellings(LISTED), &differ), []);

    // Two exceptions covering one violating program are both live.
    const TWICE: &[Exception] = &[
        Exception {
            property: Property::NoCrash,
            when: &["x=other"],
            ticket: "WI-0",
            why: "it hangs",
        },
        Exception {
            property: Property::NoCrash,
            when: &["x=other"],
            ticket: "WI-1",
            why: "it hangs, said again",
        },
    ];
    assert_eq!(property_findings(&spellings(TWICE), &agree), []);

    let found = property_findings(&spellings(LISTED), &[Verdict::Loads, Verdict::Loads, Verdict::Loads]);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(found[0].what.contains("excuses nothing"), "{found:?}");
}
