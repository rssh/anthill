/// Shared test utilities for anthill-core integration tests.
use std::path::PathBuf;

/// WI-605/WI-618: the marker phrase of both bare-arrow lambda-typo
/// diagnostics — a stable slice of `load::LAMBDA_KEYWORD_HINT`, the tail the
/// two messages share. One const so the wi605/wi618 suites pin the same
/// invariant.
#[allow(dead_code)]
pub const LAMBDA_HINT: &str = "needs the `lambda` keyword";

use anthill_core::eval::{self, Interpreter};
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Collect all .anthill files under a directory, recursively. WI-747: the walk
/// is the shared `anthill_core::fs_util`; the test suites' policy is to panic on
/// an unreadable directory (a broken fixture is a test-authoring bug).
pub fn collect_anthill_files(dir: &std::path::Path) -> Vec<PathBuf> {
    anthill_core::fs_util::collect_files(dir, &["anthill"]).expect("collect .anthill files")
}

/// Read and parse every `.anthill` file under `dir`, in path order.
///
/// WI-932: the persistence backends used to expose this as `BulkStore::pull`,
/// and its only callers were tests — no production path ever pulled. Reading a
/// tree is the CALLER's job (`anthill-todo`'s cold start scans, parses and
/// loads, then seeds `IndexedFileStore::record_source`), so the scaffolding is
/// a test helper.
///
/// A parse fault is rendered `path:line:col` via [`ParseError::all_located`],
/// which is what `pull` did (WI-852). A raw `{:?}` of the error vector prints
/// byte offsets that name nothing — the shape WI-852 removed.
#[allow(dead_code)]
pub fn read_anthill_dir_parsed(dir: &std::path::Path) -> Vec<parse::ir::ParsedFile> {
    collect_anthill_files(dir)
        .iter()
        .map(|path| {
            let source = std::fs::read_to_string(path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            parse::parse(&source).unwrap_or_else(|errors| {
                let located: Vec<String> =
                    anthill_core::parse::error::ParseError::all_located(&errors, path, &source)
                        .collect();
                panic!("parse {}:\n{}", path.display(), located.join("\n"))
            })
        })
        .collect()
}

/// Workspace root (the `oss/anthill/` directory containing rustland/, stdlib/,
/// anthill-todo/, etc.). Computed from the anthill-core crate's manifest
/// directory.
#[allow(dead_code)]
pub fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Path to stdlib/anthill/ relative to the anthill-core crate root.
pub fn stdlib_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/anthill")
}

/// Path to rustland/anthill-stl/anthill/ — Rust host bindings for the
/// builtin spec sorts (proposal 038).
pub fn rust_stl_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../anthill-stl/anthill")
}

/// Collect all .anthill files from stdlib + the Rust host bindings — the FULL library
/// closure, and what a test that evaluates anything wants.
///
/// Use this in place of `collect_anthill_files(&stdlib_dir())`. The original reason was
/// the `fact Spec[Carrier]` records the rustland `provides Carrier language rust` blocks
/// emit; WI-880 made it much wider, because those blocks now also carry the
/// `operation_map` clauses that register EVERY host implementation — the arithmetic, the
/// String surface, and all 26 `anthill.reflect` accessors. A KB built from `stdlib/`
/// alone has no `operation_map` to register from, so those operations are unimplemented
/// and anything reaching the eval bridge dies `OperationBodyMissing`. Three fixtures were
/// loading half the library and measuring half the language when the reflect family
/// migrated; WI-1103 had already made the same call for `incremental_load_test`.
#[allow(dead_code)]
pub fn collect_stdlib_and_rust_bindings() -> Vec<PathBuf> {
    let mut files = collect_anthill_files(&stdlib_dir());
    files.extend(collect_anthill_files(&rust_stl_dir()));
    files.sort();
    files
}

/// Path to anthill-testcases/ relative to the anthill-core crate root.
#[allow(dead_code)]
pub fn testcases_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../anthill-testcases")
}

/// Path to examples/ relative to the anthill-core crate root.
#[allow(dead_code)]
pub fn examples_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples")
}

/// The text of one `examples/` source, by path relative to that root
/// (`example_source("sql-store/sql.anthill")`).
///
/// WI-934 lifted this at the second live copy — the same read appeared in
/// `sql_store_example_test` and in `wi931_free_standing_provider_backing_test`,
/// which asserts about the SQL shape now that it no longer ships in the stdlib.
/// Reach for [`collect_anthill_files`] instead when the caller wants a whole
/// example DIRECTORY: naming files literally means a file added later is silently
/// never loaded.
#[allow(dead_code)]
pub fn example_source(rel: &str) -> String {
    let p = examples_dir().join(rel);
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
}

/// The stdlib + Rust host bindings, read and parsed ONCE per test binary.
///
/// [`try_load_kb_with_files`] has 683 call sites in this crate's suites and used
/// to re-walk, re-read and re-parse all 76 files at every one of them. The
/// parsed files are immutable inputs to `load_all`, so sharing them is safe —
/// the shape `anthill-smt-gen`/`anthill-cpp-gen`'s harnesses already use, and
/// the one WI-959 introduced on the `src/` side.
static STDLIB_PARSED: std::sync::LazyLock<Vec<parse::ir::ParsedFile>> =
    std::sync::LazyLock::new(|| {
        let files = collect_stdlib_and_rust_bindings();
        assert!(!files.is_empty(), "stdlib empty");
        files
            .iter()
            .map(|p| {
                let src = std::fs::read_to_string(p)
                    .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
                parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
            })
            .collect()
    });

/// Turn a loader `Result` into a test failure that NAMES the errors. The one
/// owner of the "a load error fails the test" policy for suites that build
/// their own file set (a custom resolver, an incremental second phase, a
/// stdlib-only KB) and so cannot go through [`load_kb_with`].
///
/// WI-966: 25 sites across 19 `tests/include/` files instead wrote
/// `let _ = load::load_all(..)`. That is not a degraded diagnostic — it is NO
/// GUARD, and the tests then assert over a KB that never finished loading.
/// MEASURED by flipping all of them at once: `toml_ser_test`'s fixture had been
/// carrying an unresolved `List` through all 18 of its tests, and two more
/// suites' fixtures declared incoherent `provides` clauses. Three broken
/// fixtures, silent for as long as the discard was there.
///
/// A fixture that must load dirty does NOT belong here: use
/// [`try_load_kb_with`] and assert on the returned errors, so the intent lives
/// in the test instead of in a discard.
/// Generic over the error type so [`load_kb_with`] — whose `try_` twin renders
/// its `LoadError`s to `String` for the suites that assert on them — shares this
/// one policy instead of a second `unwrap_or_else` spelling of it.
#[allow(dead_code)]
pub fn expect_loaded<T, E: std::fmt::Display>(r: Result<T, Vec<E>>) -> T {
    r.unwrap_or_else(|errs| {
        for e in &errs {
            eprintln!("{}", e);
        }
        panic!(
            "load failed with {} errors: {:?}",
            errs.len(),
            errs.iter().map(|e| e.to_string()).collect::<Vec<_>>()
        )
    })
}

/// The deliberate-dirty twin of [`expect_loaded`], for the rare fixture that
/// must carry a shape the loader rejects — WI-224's variant pins how an
/// unsatisfiable `requires` leg is RECORDED, so its provider has to stay
/// incoherent for the test to have a subject at all.
///
/// Panics unless the load reported exactly the errors whose rendering contains
/// `expected`, one per entry, in order. A fixture that starts loading clean is
/// as much a test-authoring change as one that acquires a second error, so both
/// fail here. That is the difference from a discard: the incoherence becomes a
/// pinned invariant instead of a silence.
#[allow(dead_code)]
pub fn expect_load_errors<T, E: std::fmt::Display>(r: Result<T, Vec<E>>, expected: &[&str]) {
    let errs = match r {
        Ok(_) => panic!(
            "fixture loaded CLEAN, but this call site declares it must fail with {expected:?} \
             — route it through `expect_loaded` instead"
        ),
        Err(errs) => errs.iter().map(|e| e.to_string()).collect::<Vec<_>>(),
    };
    assert_eq!(
        errs.len(),
        expected.len(),
        "expected {} load error(s), got {}: {errs:#?}",
        expected.len(),
        errs.len()
    );
    for (got, want) in errs.iter().zip(expected) {
        assert!(
            got.contains(want),
            "expected a load error containing {want:?}, got {got:?}"
        );
    }
}

/// Load the stdlib + the given user source into a fresh KB. Panics with a
/// readable diagnostic on parse or load errors. Used across every eval
/// integration test; previously hand-copied in each file.
///
/// The name means the same thing in `anthill-smt-gen/tests/common` and
/// `anthill-cpp-gen/tests/common` — panic on a load error (WI-966). Reach for
/// the crate-local `*_lenient` twin, never a bare discard, when a fixture
/// deliberately carries a shape the loader rejects.
#[allow(dead_code)]
pub fn load_kb_with(source: &str) -> KnowledgeBase {
    expect_loaded(try_load_kb_with(source))
}

/// Same load as [`load_kb_with`] (full stdlib + Rust host bindings + `source`)
/// but returns the load errors instead of panicking, so a test can assert an
/// expected load-time (typer) error. The error strings are the rendered
/// `LoadError`s. Parse failures still panic (they are test-authoring bugs).
#[allow(dead_code)]
pub fn try_load_kb_with(source: &str) -> Result<KnowledgeBase, Vec<String>> {
    try_load_kb_with_files(&[source])
}

/// WI-1122 — [`try_load_kb_with`] with a hook that runs on the FRESH KB before
/// `load_all`, for the embedder seams that must be mounted before load
/// (`register_host_fn`, `register_extent_owner`). Registering after the load would not
/// exercise the documented ordering: load itself builds interpreters (a `[simp]` macro
/// fire crosses `run_in_bridge_interp`), and `register_host_fn` now REFUSES a late
/// entry, so a test that registered afterwards would not load at all.
#[allow(dead_code)]
pub fn try_load_kb_prepared(
    source: &str,
    prepare: impl FnOnce(&mut KnowledgeBase),
) -> Result<KnowledgeBase, Vec<String>> {
    try_load_kb_prepared_files(&[source], prepare)
}

/// Like [`try_load_kb_with`] but loads MULTIPLE user source strings as SEPARATE
/// files (each its own `ParsedFile`) alongside the stdlib — for asserting
/// cross-file load behavior, e.g. WI-321 cross-file mutual structural recursion
/// (two files whose entities reference each other's sorts must both load).
#[allow(dead_code)]
pub fn try_load_kb_with_files(sources: &[&str]) -> Result<KnowledgeBase, Vec<String>> {
    try_load_kb_prepared_files(sources, |_| {})
}

/// The shared body of [`try_load_kb_with_files`] and [`try_load_kb_prepared`]: parse
/// each source as its own file, build a fresh KB, run `prepare` on it, then `load_all`.
/// ONE recipe rather than two, so a change to the load pipeline (a different resolver,
/// an added pass) cannot reach the ~683 ordinary call sites while leaving the
/// prepared-KB tests on an older one.
#[allow(dead_code)]
pub fn try_load_kb_prepared_files(
    sources: &[&str],
    prepare: impl FnOnce(&mut KnowledgeBase),
) -> Result<KnowledgeBase, Vec<String>> {
    try_load_kb_named_prepared(sources, None, prepare)
}

/// The one recipe, with the file NAMES optional — see [`try_load_kb_with_named_files`]
/// for why a test ever needs them. `names`, when given, is parallel to `sources`.
#[allow(dead_code)]
fn try_load_kb_named_prepared(
    sources: &[&str],
    names: Option<&[&str]>,
    prepare: impl FnOnce(&mut KnowledgeBase),
) -> Result<KnowledgeBase, Vec<String>> {
    if let Some(names) = names {
        assert_eq!(names.len(), sources.len(), "one name per source");
    }
    let user: Vec<_> = sources
        .iter()
        .enumerate()
        .map(|(i, s)| {
            let mut f = parse::parse(s).expect("parse user source");
            if let Some(names) = names {
                f.path = Some(std::sync::Arc::from(std::path::Path::new(names[i])));
            }
            f
        })
        .collect();

    let mut refs: Vec<&parse::ir::ParsedFile> = STDLIB_PARSED.iter().collect();
    refs.extend(user.iter());
    let mut kb = KnowledgeBase::new();
    prepare(&mut kb);
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => Ok(kb),
        Err(errs) => Err(errs.iter().map(|e| e.to_string()).collect()),
    }
}

/// The stdlib WITHOUT the Rust host bindings, parsed once — the peer of
/// [`STDLIB_PARSED`] for the configuration that must not see `anthill-stl`'s bindings.
static STDLIB_ONLY_PARSED: std::sync::LazyLock<Vec<parse::ir::ParsedFile>> =
    std::sync::LazyLock::new(|| {
        let files = collect_anthill_files(&stdlib_dir());
        assert!(!files.is_empty(), "stdlib empty");
        files
            .iter()
            .map(|p| {
                let src = std::fs::read_to_string(p)
                    .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
                parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
            })
            .collect()
    });

/// [`load_kb_with`] MINUS the Rust host bindings: the stdlib files and `source`, in ONE
/// `load_all`.
///
/// WHY THIS EXISTS AS ITS OWN RECIPE, since two neighbours nearly serve and neither
/// does. `load_kb_with` also loads `rustland/anthill-stl/anthill/*.anthill`, and for a
/// fixture that turns on which carriers provide a spec that is not a superset but a
/// different world — measured at `WI-20260831-QF5JT`, where a `requires(PartialEq[T])`
/// guard stops discriminating by carrier once those bindings are present.
/// `load_stdlib_kb_with_source` drops the bindings but loads the user file in a SECOND
/// pass (`load_stdlib`, then `load`), which is not the same as one `load_all` over both:
/// driven, the same guard fixture answers 0 for EVERY carrier that way, i.e. the fixture
/// goes dead rather than discriminating.
///
/// `wi300_rule_body_requires_test` and `cut_test` each hand-roll exactly this sequence;
/// they are left as found, and a new caller should use this instead of adding a fourth
/// copy.
#[allow(dead_code)]
pub fn load_kb_with_stdlib_only(source: &str) -> KnowledgeBase {
    let user = parse::parse(source).expect("parse user source");
    let mut refs: Vec<&parse::ir::ParsedFile> = STDLIB_ONLY_PARSED.iter().collect();
    refs.push(&user);
    let mut kb = KnowledgeBase::new();
    expect_loaded(
        load::load_all(&mut kb, &refs, &NullResolver)
            .map_err(|errs| errs.iter().map(|e| e.to_string()).collect::<Vec<_>>()),
    );
    kb
}

/// Load the stdlib plus each `(name, source)` as a file that KNOWS ITS PATH.
///
/// [`try_load_kb_with_files`]'s sources are path-less, so a diagnostic that NAMES the
/// files it spans — 061's multi-file predicate refusal — renders `<file 0>` for every
/// one of them and a test cannot tell which file it meant. This sets `ParsedFile::path`
/// so the message carries the names the author would see.
///
/// Goes through [`try_load_kb_prepared_files`]' body, NOT a second copy of the load
/// recipe: that function's own comment says why (one recipe, so a change to the pipeline
/// cannot leave some call sites on an older one), and a duplicate here would also have
/// silently dropped the `prepare` hook. Found by /code-review.
#[allow(dead_code)]
pub fn try_load_kb_with_named_files(files: &[(&str, &str)]) -> Result<KnowledgeBase, Vec<String>> {
    let (names, sources): (Vec<&str>, Vec<&str>) = files.iter().copied().unzip();
    try_load_kb_named_prepared(&sources, Some(&names), |_| {})
}

/// The messages of a source that must NOT parse — for a rule enforced at
/// parse/convert rather than at load, where `try_load_kb_with` would panic
/// instead of returning the diagnostic. Panics if the source parses clean, since
/// a fixture that no longer trips the rule is a test-authoring bug.
///
/// Shared because the checks that report here have multiplied: the projection
/// well-formedness rules (`validate_projection_labels`, WI-639) and the tuple
/// component-label distinctness rule (`check_label_unique`, WI-805),
/// whose fixtures live in four suites. Assert on the returned messages; the
/// panic here only says the source parsed at all.
#[allow(dead_code)]
pub fn parse_errs(src: &str) -> Vec<String> {
    match parse::parse(src) {
        Ok(_) => panic!("expected a parse error, but the source parsed clean"),
        Err(errs) => errs.iter().map(|e| e.message.clone()).collect(),
    }
}

/// The control twin of [`parse_errs`]: a source that MUST parse. Panics with the
/// diagnostics if it does not, so a guard that over-fires names what it caught
/// rather than failing as a bare `false`.
#[allow(dead_code)]
pub fn parses_clean(src: &str) {
    if let Err(errs) = parse::parse(src) {
        panic!("expected a clean parse; got: {errs:?}");
    }
}

/// A refusal control that asserts only "something failed" measures nothing: a fixture typo
/// or an unrelated future change keeps it green while the behaviour it names rots. This
/// takes the token(s) that DISTINGUISH the right refusal from the wrong acceptance — the
/// string the corresponding back-out makes disappear.
///
/// Shared rather than per-file since WI-20260829-70XVH, whose rows are the second set to
/// need it: a control's whole value is that its token is the one a back-out removes, and two
/// copies of the assertion would let two files drift on what "refused" is allowed to mean.
#[track_caller]
#[allow(dead_code)]
pub fn assert_refused_naming(errs: &[String], tokens: &[&str], why: &str) {
    let joined = errs.join(" | ");
    assert!(!errs.is_empty(), "{why}: expected a refusal, got a clean load");
    for t in tokens {
        assert!(
            joined.contains(t),
            "{why}: the refusal should name `{t}`, got:\n{joined}"
        );
    }
}

/// Load stdlib + user source, construct an `Interpreter`, and register the
/// standard eval builtins. The one-liner every eval_mN_test file needs.
#[allow(dead_code)]
pub fn interp_for(source: &str) -> Interpreter {
    let kb = load_kb_with(source);
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    interp
}

/// [`interp_for`] over MULTIPLE user sources, each its own file — for an eval test
/// whose fixture is split into a shared declarations file plus a per-case consumer
/// (WI-329). Same recipe, same builtins; only the load helper differs, so an eval test
/// that needs the split cannot drift onto a different pipeline than the single-source
/// one.
#[allow(dead_code)]
pub fn interp_for_files(sources: &[&str]) -> Interpreter {
    let kb = expect_loaded(try_load_kb_with_files(sources));
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    interp
}

// ── Effect handler test helpers (M5) ─────────────────────────

/// Build a buffered Console handler and return `(buffer, handler)`.
/// Works for ConsoleOutput or ConsoleError — the caller registers the
/// handler against whichever effect sort it wants to capture.
#[allow(dead_code)]
pub fn buffered_console() -> (
    std::rc::Rc<std::cell::RefCell<String>>,
    anthill_core::eval::effects::EffectHandler,
) {
    let buf = std::rc::Rc::new(std::cell::RefCell::new(String::new()));
    let handler = anthill_core::eval::effects::buffered_console_handler(buf.clone());
    (buf, handler)
}

/// Build a scripted `ConsoleInput` handler from a list of lines and
/// return `(queue, handler)`. The queue holds any lines the program
/// didn't consume — useful for assertions.
#[allow(dead_code)]
pub fn scripted_console_input(
    lines: &[&str],
) -> (
    std::rc::Rc<std::cell::RefCell<std::collections::VecDeque<String>>>,
    anthill_core::eval::effects::EffectHandler,
) {
    let queue = std::rc::Rc::new(std::cell::RefCell::new(
        lines.iter().map(|s| s.to_string()).collect(),
    ));
    let handler = anthill_core::eval::effects::scripted_console_input_handler(queue.clone());
    (queue, handler)
}

/// Register the default `Modify` arena-backed handler on the interpreter.
/// Shared across Modify-focused tests that don't want to depend on the
/// stdio-binding side effects of `register_standard_effect_handlers`.
#[allow(dead_code)]
pub fn register_modify_handler(interp: &mut Interpreter) {
    interp
        .register_effect_handler(
            "anthill.prelude.Modify",
            anthill_core::eval::effects::default_modify_handler(),
        )
        .expect("register Modify handler");
}

/// The stdlib-only KB the re-type suites build on: parse + `load_stdlib` (which
/// bootstraps — WI-967), with NO user source. WI-732 lifted this here
/// after finding six verbatim copies across the test tree (typing_test, incremental_load_test,
/// wi211, wi219, wi759, and its own) — a change to the load sequence otherwise has to land in
/// every one, and the copy that misses it fails as though the code under test were broken.
///
/// Distinct from [`try_load_kb_with`], which loads the stdlib AND a user source in one shot and
/// returns only errors. A caller needing the `LoadResult` (to type-check the user file's OWN
/// sorts, then RE-type-check to exercise the free-op sweep) needs the two steps split, which
/// is what this and [`load_stdlib_kb_with_source`] provide.
#[allow(dead_code)]
pub fn load_stdlib_kb() -> KnowledgeBase {
    let files = collect_anthill_files(&stdlib_dir());
    assert!(!files.is_empty(), "no stdlib files found");
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {p:?}: {e}"));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {p:?}: {e:?}"))
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::load_stdlib(&mut kb, &refs, &NullResolver).expect("stdlib load");
    kb
}

/// The MIRROR IMAGE of [`load_stdlib_kb`]: the user sources with NO stdlib files —
/// `load_all` (which bootstraps — WI-967), nothing else. The configuration an EMBEDDER
/// uses, and the one where a name's implicit-prelude target may simply not exist
/// (WI-900).
///
/// Lifted here for the reason [`load_stdlib_kb`] records: verbatim copies of this exact
/// sequence had accumulated (`wi720_ctor_order_test`, `wi458_head_span_occurrence_test`),
/// and a change to the load sequence otherwise lands in one and not the others.
#[allow(dead_code)]
pub fn load_kb_bare(sources: &[&str]) -> KnowledgeBase {
    let parsed: Vec<_> = sources
        .iter()
        .map(|s| parse::parse(s).expect("parse source"))
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &refs, &NullResolver).unwrap_or_else(|errs| {
        for e in &errs {
            eprintln!("Load error: {e}");
        }
        panic!("load failed with {} errors", errs.len());
    });
    kb
}

/// [`load_stdlib_kb`] plus ONE user source, returning the `LoadResult` too — the split-step
/// form a re-type test needs (`type_check_sorts(&result.defined_sorts)`, then
/// `type_check_sorts(&[])`). Parse and load failures panic: both are test-authoring bugs here,
/// since a test asserting a LOAD error uses [`try_load_kb_with`] instead.
#[allow(dead_code)]
pub fn load_stdlib_kb_with_source(
    source: &str,
) -> (KnowledgeBase, anthill_core::kb::load::LoadResult) {
    let mut kb = load_stdlib_kb();
    let parsed = parse::parse(source).expect("parse failed");
    let result = load::load(&mut kb, &parsed, &NullResolver).expect("load failed");
    (kb, result)
}

/// Solutions of the unary goal `qn(?r)`, as `(the reified `?r`, the solution is
/// definite)`.
///
/// THE POINT IS THAT DRIVING A RULE COSTS ONE LINE. A test speaks to the resolver
/// by BUILDING TERMS — intern a name, allocate a fresh var, wrap it, hand-assemble
/// the goal `Term::Fn`, resolve, reify out of the substitution — six steps to ask
/// one question, where `try_resolve_symbol(name).is_some()` is one and proves only
/// that the NAME exists. That asymmetry is why the cheap form spread, and the cheap
/// form is what keeps passing when the name resolves to something that answers
/// nothing (CLAUDE.md: a test for a capability must DRIVE the capability).
///
/// UNARY is not a limitation: write the hard part in anthill source as a wrapper
/// rule and drive that, so the plumbing stays fixed however complex the goal is —
///
/// ```ignore
/// rule add_x(?x) :- ancestor(alice, ?p), parent(?p, ?x)
/// ```
///
/// Raw `Value`s, not rendered strings: a caller that wants a number should assert
/// on one, and rendering is the caller's business.
#[allow(dead_code)]
pub fn query_unary(kb: &mut KnowledgeBase, qn: &str) -> Vec<(eval::Value, bool)> {
    use anthill_core::kb::resolve::ResolveConfig;
    use anthill_core::kb::term::{Term, Var};
    use smallvec::SmallVec;

    let sym = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("query_unary: `{qn}` does not resolve"));
    let r_sym = kb.intern("r");
    let r_vid = kb.fresh_var(r_sym);
    let r_var = kb.alloc(Term::Var(Var::Global(r_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_elem(r_var, 1),
        named_args: SmallVec::new(),
    });
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .map(|sol| (kb.reify(r_var, &sol.subst), sol.is_definite()))
        .collect()
}

/// [`query_unary`] KEEPING ONLY THE DEFINITE ANSWERS — what a test asserting that
/// something DECIDES must count.
///
/// WI-20260822-WZX6B. `query_unary` already carries definiteness in each pair's `bool`,
/// and callers were dropping it: `query_unary(..).len()` counts FLOUNDERED answers too,
/// and a floundered answer is a suspension — "I could not decide this" — which is the
/// one outcome that must never read as success. `Solution::is_definite`'s own doc
/// already says so ("a floundered solution must never be counted as a definite answer");
/// this is the ergonomic half, so the shortest thing to write is also the right one.
///
/// MEASURED, and it is not a corner: `=` is `PartialEq.eq`, a semantic equality TEST
/// that never binds (§8.3), so the common fixture idiom `rule p(?m) :- <goal>, ?m = 1`
/// SUSPENDS — `total = 1, definite = 0` — and four suites were asserting that 1 as a
/// decision, one of them a CONTROL whose message read "the control must answer, or
/// nothing below proves anything". Put the constant in the HEAD (`rule p(1) :- <goal>`)
/// and the same claim decides.
///
/// A test whose subject IS a residual should keep [`query_unary`] and assert the flag,
/// or count derivations and say at its site that that is what it is counting.
#[allow(dead_code)]
pub fn definite_unary(kb: &mut KnowledgeBase, qn: &str) -> Vec<eval::Value> {
    query_unary(kb, qn)
        .into_iter()
        .filter(|(_, definite)| *definite)
        .map(|(v, _)| v)
        .collect()
}

/// Every `SortProvidesInfo` fact as `(carrier qualified name, spec qualified
/// name)` — "who provides what", the question several suites ask of a loaded KB.
///
/// Lifted here (WI-931) rather than copied a fourth time: the same walk —
/// `rules_by_functor` → `is_fact` → `fact_head_named_args` → the `sort_ref` /
/// `spec` fields → unwrap `SortView(Spec, …bindings)` to its first positional —
/// is already hand-written in `wi858_pair_orderings_test`, `eval_test`'s
/// `wi362_stream_provides_iterable`, and `wi391_binding_extractability_test`.
/// Those predate this and are left as found; new readers should call this so the
/// count stops growing.
///
/// The loader's own `sort_ref_functor` / `provides_spec_base_sym` are
/// `pub(crate)`, which is why this reads the fields structurally rather than
/// calling them.
///
/// A field that is present but not name-like PANICS rather than being skipped: a
/// silent skip here would read as "no such provision" and quietly weaken whatever
/// the caller is asserting.
#[allow(dead_code)]
pub fn sort_provisions(kb: &KnowledgeBase) -> Vec<(String, String)> {
    use anthill_core::kb::term::{Term, TermId};
    let Some(sym) = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") else {
        return Vec::new();
    };
    fn name_of(kb: &KnowledgeBase, t: TermId, field: &str) -> String {
        match kb.get_term(t) {
            Term::Fn { functor: s, .. } | Term::Ref(s) | Term::Ident(s) => {
                kb.qualified_name_of(*s).to_string()
            }
            other => panic!("SortProvidesInfo.{field} is not a name-like term: {other:?}"),
        }
    }
    let mut out = Vec::new();
    for rid in kb.rules_by_functor(sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(named) = kb.fact_head_named_args(rid) else {
            continue;
        };
        let get = |f: &str| {
            named
                .iter()
                .find(|(s, _)| kb.local_name_of(*s) == f)
                .map(|(_, v)| *v)
        };
        let (Some(sr), Some(spec_view)) = (get("sort_ref"), get("spec")) else {
            continue;
        };
        // `SortView(Spec, …)` carries the spec as its first positional; a bare
        // reference is already the spec.
        let spec_term = match kb.get_term(spec_view) {
            Term::Fn { pos_args, .. } if !pos_args.is_empty() => pos_args[0],
            _ => spec_view,
        };
        out.push((name_of(kb, sr, "sort_ref"), name_of(kb, spec_term, "spec")));
    }
    out
}

/// [`sort_provisions`] without the EQUALITY family (`PartialEq` / `Eq` / `NonEq`) —
/// for a suite whose question is "what does this carrier provide" about some OTHER
/// spec.
///
/// WI-1098: those three are no longer a property of what a fixture WROTE. Every
/// composite carrier now derives one of the two classifications — `PartialEq`+`Eq`
/// when its fields are all lawful, `PartialEq`+`NonEq` when one reaches an IEEE
/// `Float` — so a two-field entity that says nothing about equality still contributes
/// two rows, and a fixture asserting an exact provision set for its own carrier was
/// reading a population that grew under it.
///
/// A filter by SPEC, not by provenance, and that is not a shortcut: a hand-written
/// `provides Eq[T = X]` is indistinguishable from a derived one at the fact layer —
/// deliberately, since the whole point of deriving is that the two are the same claim.
/// A fixture that means to assert something ABOUT equality must therefore call
/// [`sort_provisions`] and name the rows it expects.
#[allow(dead_code)]
pub fn sort_provisions_outside_equality(kb: &KnowledgeBase) -> Vec<(String, String)> {
    sort_provisions(kb)
        .into_iter()
        .filter(|(_, spec)| {
            !matches!(
                spec.as_str(),
                "anthill.prelude.PartialEq" | "anthill.prelude.Eq" | "anthill.prelude.NonEq"
            )
        })
        .collect()
}

/// The `Var::Global` id backing `sort_sym` as a type parameter — the target of its
/// `SortAlias(<sort_sym>, ?V)` fact. `None` when the sort has no alias at all, and
/// also when its alias target is not a logic var (`sort T = Int64` aliases a concrete
/// sort; only `sort T = ?` and the WI-452 marked-param shape mint a backing var).
///
/// WI-956 — ONE reader for five suites (wi210, wi221, wi224, wi452, wi943) that each
/// hand-rolled this walk. Deliberately a HAND READ of the `SortAlias` relation and NOT
/// a call into the loader/typer's own `find_sort_alias_var` / `resolve_sort_alias`:
/// every one of those suites exists to assert that a production reader agrees with the
/// DECLARATION, and routing the expected side through the production reader would only
/// assert that it agrees with itself.
///
/// FIRST match in `rules_by_functor` order, which is the production scan's precedence.
/// Three of the five copies took the LAST match instead; that has never differed,
/// because the loader's `sort_alias_exists` dedup guard means a sort has at most one
/// `SortAlias` fact — but a test should not depend on a property it does not state.
#[allow(dead_code)]
pub fn sort_alias_backing_var(
    kb: &KnowledgeBase,
    sort_sym: anthill_core::intern::Symbol,
) -> Option<anthill_core::kb::term::VarId> {
    use anthill_core::kb::term::Term;
    let alias_sym = kb.try_resolve_symbol("SortAlias")?;
    // `rules_by_functor_iter`, as the production scan does: nothing here needs a
    // snapshot, and callers run this once per type-param in a loop.
    kb.rules_by_functor_iter(alias_sym)
        .filter(|rid| kb.is_fact(*rid))
        .find_map(|rid| {
            // `fact_head_term`, matching the readers under test: a `Value::Node` head
            // carries a denoted-bearing target, which is never a logic `Var`.
            let head = kb.fact_head_term(rid)?;
            let Term::Fn { pos_args, .. } = kb.get_term(head) else {
                return None;
            };
            let Term::Fn { functor, .. } = kb.get_term(*pos_args.first()?) else {
                return None;
            };
            if *functor != sort_sym {
                return None;
            }
            match kb.get_term(*pos_args.get(1)?) {
                Term::Var(v) => v.as_global(),
                _ => None,
            }
        })
}

/// The HEAD VALUES of a `cons`/`nil` list, in order — the element-type-agnostic
/// peer of [`list_ints`], for suites whose elements are not `Int` (a projected
/// relation drains to `Value::Tuple` rows, WI-762). Walks via [`cons_spine`].
///
/// Elements that are THEMSELVES entities used to be out of scope for both
/// helpers, because the old walk identified the tail as "the `Entity` among the
/// two fields" and so could not tell an entity element from the tail. Reading
/// head/tail BY POSITION removes that restriction (WI-733 review).
#[allow(dead_code)]
pub fn list_heads(v: &eval::Value) -> Vec<eval::Value> {
    cons_spine(v, "list_heads")
}

/// Walk an anthill cons-list `Value` into its `Int64` elements — [`list_heads`]
/// plus an `Int64` read on each element, LOUD if one is not an `Int`.
///
/// A list is a chain of `cons(head, tail)` entities terminated by a zero-field
/// `nil`. Several per-WI suites grew a private copy of this walk (wi714_*,
/// wi727, wi730); this is the shared one to reach for.
#[allow(dead_code)]
pub fn list_ints(v: &eval::Value) -> Vec<i64> {
    cons_spine(v, "list_ints")
        .into_iter()
        .map(|h| match h {
            eval::Value::Int(i) => i,
            other => panic!("list_ints: expected an Int64 element, got {other:?}"),
        })
        .collect()
}

/// WI-20260818-YQB1Y — the SOLE COLUMN's value of a one-column relation row.
///
/// 052 OQ5 option A dropped the schema 1-collapse, so a relation row is a named tuple at
/// EVERY arity: a one-column drain yields `(name: "alice")` where it used to yield the bare
/// `"alice"`. The suites that drain a one-column relation read the column through here.
///
/// STRICT, and that is the point: anything but a ONE-component named tuple panics. A lenient
/// "take the first named field" would keep passing if a fixture started draining a
/// two-column relation, reading its first column and reporting a pass — which is the exact
/// silent-wrong-answer shape this ticket removed from the typer.
#[allow(dead_code)]
pub fn sole_column(v: &eval::Value) -> eval::Value {
    match v {
        eval::Value::Tuple { pos, named } if pos.is_empty() && named.len() == 1 => {
            named[0].1.clone()
        }
        other => panic!(
            "sole_column: expected a ONE-column relation row (a one-component named tuple), \
             got {other:?}"
        ),
    }
}

/// Walk a one-column relation drain into its `String` column values — [`list_heads`], then
/// [`sole_column`] on each row, then a carrier-neutral string read. LOUD on any other shape.
///
/// WI-20260827-3ZNBC — the read goes through [`scalar_str`] and so needs a
/// `&KnowledgeBase`. A relation column is the bound value ON ITS OWN CARRIER now
/// (`materialize_solution`), so `Value::Str` names one of the three ways the same
/// string arrives; matching it was asking which variant carried the answer, not what
/// the answer was.
#[allow(dead_code)]
pub fn list_column_strings(kb: &KnowledgeBase, v: &eval::Value) -> Vec<String> {
    cons_spine(v, "list_column_strings")
        .into_iter()
        .map(|h| {
            let col = sole_column(&h);
            scalar_str(kb, &col)
                .unwrap_or_else(|| panic!("list_column_strings: expected a String column, got {col:?}"))
        })
        .collect()
}

/// Walk a one-column relation drain into its `Int64` column values — the [`list_ints`] of
/// [`list_column_strings`].
#[allow(dead_code)]
pub fn list_column_ints(kb: &KnowledgeBase, v: &eval::Value) -> Vec<i64> {
    cons_spine(v, "list_column_ints")
        .into_iter()
        .map(|h| {
            let col = sole_column(&h);
            scalar_int(kb, &col)
                .unwrap_or_else(|| panic!("list_column_ints: expected an Int64 column, got {col:?}"))
        })
        .collect()
}

/// The FUNCTOR SYMBOL of an entity value, whatever CARRIER it rides on.
///
/// Through [`TermView`] rather than a `Value::Entity` match, for the reason
/// [`entity_field`] spells out. A NULLARY constructor reads as `ViewHead::Ref` and not
/// as an empty `Functor` (WI-436/WI-511), so both spellings must be accepted or `nil` /
/// `none` answer `None` here while `some(1)` answers a symbol.
#[allow(dead_code)]
pub fn entity_functor(
    kb: &KnowledgeBase,
    v: &eval::Value,
) -> Option<anthill_core::intern::Symbol> {
    use anthill_core::kb::term_view::{TermView, ViewHead};
    match v.head(kb) {
        ViewHead::Functor {
            functor: Some(s), ..
        }
        | ViewHead::Ref(s) => Some(s),
        _ => None,
    }
}

/// An entity's field BY DECLARED NAME, whatever CARRIER the entity rides on — the
/// test-side twin of `project_field` (`kb/resolve.rs`).
///
/// THROUGH [`TermView`], AND NOT BY MATCHING `Value::Entity`, which is the whole point.
/// One entity reaches a test on any of three carriers — `Value::Entity`, a hash-consed
/// `Value::Term(TermId)`, and a `Value::Node(occurrence)` — and an enum match reads the
/// first and panics on the other two, so the RECEIVER'S CARRIER decides whether its own
/// field is reachable. That is exactly the bug `project_field` was rewritten to stop
/// making, and hand-rolled `Value::Entity { pos, .. }` readers in the test tree had
/// re-created it: `cli_parse_test` and `wi733_relation_head_eval_test` each carried
/// their own copy, and both broke on WI-20260827-T2470 for that reason.
///
/// NAME FIRST, THEN THE POSITIONAL RANK, for the reason `project_field` asks both. A
/// canonical entity carries its args NAMED — every producer desugars positional→named
/// through `positional_to_named_plan` (WI-500/WI-433/WI-20260827-T2470) — but a
/// `Value::Entity` built directly in Rust by a host builtin or a bridge has no such
/// obligation and may still spell them positionally. `pos_rank` is the field's index in
/// the DECLARATION, which is the order the positional spelling fills.
///
/// LOUD when neither channel has the field: a silently-`None` field read is what turned
/// this ticket's regression into "the assert compares against nothing".
#[allow(dead_code)]
pub fn entity_field(
    kb: &KnowledgeBase,
    v: &eval::Value,
    name: &str,
    pos_rank: usize,
) -> eval::Value {
    use anthill_core::kb::term_view::TermView;
    if let Some(sym) = v
        .named_keys(kb)
        .into_iter()
        .find(|s| kb.local_name_of(*s) == name)
    {
        if let Some(item) = v.named_arg(kb, sym) {
            return item.to_value();
        }
    }
    v.pos_arg(kb, pos_rank)
        .map(|item| item.to_value())
        .unwrap_or_else(|| panic!("entity_field: no field `{name}` and no pos[{pos_rank}] on {v:?}"))
}

/// A SCALAR read through the carrier-neutral view: `ViewHead::Const`.
///
/// SAME REASON AS [`entity_field`], one level down. `Value::as_str` / `as_bool` answer
/// only the `Value::Str` / `Value::Bool` carrier, so a test built on them lets the
/// carrier decide whether a string is a string — and the same literal also arrives as a
/// hash-consed `Value::Term` over `Term::Const(Literal::String)` and as a `Value::Node`
/// over `Expr::Const`. `TermView::head` maps all three onto one `ViewHead::Const`, which
/// is what the resolver's own comparisons read.
///
/// `None` for a non-literal head and for a literal of the wrong TYPE — the caller
/// asserts, so a wrong-typed value must not read as absent-but-fine.
#[allow(dead_code)]
pub fn scalar_str(kb: &KnowledgeBase, v: &eval::Value) -> Option<String> {
    use anthill_core::kb::term::Literal;
    use anthill_core::kb::term_view::{TermView, ViewHead};
    match v.head(kb) {
        ViewHead::Const(Literal::String(s)) => Some(s),
        _ => None,
    }
}

/// The `Int64` a value DENOTES, read through the carrier-neutral view — the integer
/// peer of [`scalar_str`], and needed for the same reason (WI-20260827-3ZNBC): a
/// relation row column carries its value on whatever carrier the search proved it on,
/// so `matches!(col, Value::Int(_))` asks which VARIANT rather than which VALUE.
#[allow(dead_code)]
pub fn scalar_int(kb: &KnowledgeBase, v: &eval::Value) -> Option<i64> {
    use anthill_core::kb::term::Literal;
    use anthill_core::kb::term_view::{TermView, ViewHead};
    match v.head(kb) {
        ViewHead::Const(Literal::Int(n)) => Some(n),
        _ => None,
    }
}

/// The `Bool` a value DENOTES, read through the carrier-neutral view — the peer of
/// [`scalar_str`] / [`scalar_int`], for the same reason (WI-20260827-3ZNBC).
#[allow(dead_code)]
pub fn scalar_bool(kb: &KnowledgeBase, v: &eval::Value) -> Option<bool> {
    use anthill_core::kb::term::Literal;
    use anthill_core::kb::term_view::{TermView, ViewHead};
    match v.head(kb) {
        ViewHead::Const(Literal::Bool(b)) => Some(b),
        _ => None,
    }
}

/// ANY scalar a value denotes, rendered — for the suites that join a row's columns into
/// one comparable string and do not care which scalar sort each column is. LOUD (`None`)
/// on a non-literal, so a column that is not a scalar at all still fails its assertion
/// rather than reading as an empty field.
#[allow(dead_code)]
pub fn scalar_display(kb: &KnowledgeBase, v: &eval::Value) -> Option<String> {
    use anthill_core::kb::term::Literal;
    use anthill_core::kb::term_view::{TermView, ViewHead};
    match v.head(kb) {
        ViewHead::Const(Literal::String(s)) => Some(s),
        ViewHead::Const(Literal::Int(n)) => Some(n.to_string()),
        ViewHead::Const(Literal::BigInt(n)) => Some(n.to_string()),
        ViewHead::Const(Literal::Float(f)) => Some(f.into_inner().to_string()),
        ViewHead::Const(Literal::Bool(b)) => Some(b.to_string()),
        _ => None,
    }
}

/// The shared cons-spine walk behind [`list_heads`] and [`list_ints`].
///
/// Handles BOTH carriers a cons cell arrives in, because reading only one of them made a
/// positionally-built list walk out as an EMPTY vector, silently and with the doc
/// claiming the opposite (WI-733 review).
///
/// WHICH PRODUCER STILL BUILDS THE POSITIONAL ONE, restated because the original answer
/// expired: this used to say "`build_list_value` emits NAMED head/tail while
/// `classify_ctor_arg` pushes POSITIONALLY (eval.rs)". WI-20260827-T2470 made
/// `finish_constructor` desugar positional→named for every declared entity, and
/// `List.cons` is one — so a source-written `cons(x, nil)` now reaches here NAMED too,
/// and the positional arm is left for a cons cell built directly in Rust. The dual read
/// stays: which carrier arrives is still not this walker's to assume.
///
/// LOUD on a shape that is neither: a silent `break` here reads as "the list
/// ended" and turns a malformed value into a short answer, which is what the
/// production reader in `eval/builtins.rs` refuses to do.
///
/// RESIDUAL LIMITATION, stated because it cannot be fixed here: with no `&KnowledgeBase`
/// in hand this cannot check that the functors really are `List.cons`/`List.nil`, so
/// any 2-field entity walks as a cons and any nullary one ends the spine. A suite
/// that needs the functor checked must do it at its own site with a KB handle.
fn cons_spine(v: &eval::Value, who: &str) -> Vec<eval::Value> {
    use eval::Value;
    let mut out = Vec::new();
    let mut cur = v.clone();
    loop {
        let (pos, named) = match &cur {
            Value::Entity { pos, named, .. } => (pos.clone(), named.clone()),
            other => panic!("{who}: expected a cons/nil entity in the list spine, got {other:?}"),
        };
        if pos.is_empty() && named.is_empty() {
            return out; // nil
        }
        let (head, tail) = if pos.len() == 2 {
            (pos[0].clone(), pos[1].clone())
        } else if named.len() == 2 {
            (named[0].1.clone(), named[1].1.clone())
        } else {
            panic!("{who}: a cons cell carries head+tail; got pos={pos:?} named={named:?}")
        };
        out.push(head);
        cur = tail;
    }
}

// ── Tuple-cluster fixture builder (WI-786 / 788 / 803) ───────

/// Build `ap(f) = f(<lit>)` over a `Function[A = <ty>, B = Int64]`, driven by
/// `drive() = ap(<lam>)`.
///
/// ONE builder for the program shape the WI-775 → 786 → 788 → 804 → 803 cluster
/// is argued over: a tuple literal reaching a destructuring binder list through a
/// `Function` slot. It had been copy-pasted into three test files, and
/// `wi788_..`'s copy carried a doc comment claiming it was "the same builder as
/// `wi786_..`'s" — a claim nothing enforced, and exactly the property those files
/// need, since their value is being comparable line for line. WI-803 was about to
/// add a fourth copy.
///
/// `imports` is the brace-list body (e.g. `"Int64, String, Function"`).
#[allow(dead_code)]
pub fn function_slot_case(ns: &str, imports: &str, ty: &str, lit: &str, lam: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{{imports}}}
  operation ap(f: Function[A = {ty}, B = Int64]) -> Int64
    = f({lit})
  operation drive() -> Int64
    = ap({lam})
end
"#
    )
}

// ── Conditional-instance fixture (WI-817 / 822 / 855) ────────

/// Spec `Desc`, a LEAF instance at `Leaf` (describe → 1), and a CONDITIONAL
/// instance at `Wrap[E]` given `Desc[E]` (describe → 10·describe(inner) + 2).
///
/// ONE copy of the program shape the requirement-supply cluster is argued over.
/// The answers are DEPTH-CODED — `describe(wrapⁿ(leaf))` = 1, 12, 122, 1222, … —
/// so a wrong dictionary at any step shows up as a different number rather than
/// as an error, and that coding is what each file's assertions read. It had been
/// copy-pasted byte-identically into three files, two of which carried the
/// unenforced claim that they were "the same shape" as the first; WI-855 was
/// about to add a fourth copy.
///
/// Assign it to a file-local `const INSTANCES: &str = common::DESC_INSTANCES;`
/// so the surrounding programs can keep interpolating `{INSTANCES}` inline.
#[allow(dead_code)]
pub const DESC_INSTANCES: &str = r#"
  -- WI-20260825-KD9SW: `WrapDesc.describe` writes `add(mul(10, …), 2)` — WRITTEN names,
  -- not minted operators — so this fragment brings them into scope itself rather than
  -- leaning on every namespace that splices it. A minted `+`/`*` would need nothing.
  import anthill.prelude.Additive.{add}
  import anthill.prelude.Multiplicative.{mul}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end

  sort Wrap
    sort A = ?
    entity wrap(inner: A)
  end

  sort WrapDesc
    sort E = ?
    requires Desc[T = E]
    fact Desc[T = Wrap[A = E]]
    operation describe(w: Wrap[A = E]) -> Int64 =
      add(mul(10, Desc.describe(w.inner)), 2)
  end
"#;

/// The WI-325 ladder's suggestion for [`DESC_INSTANCES`]' spec — what an UNCOVERED
/// abstract `Desc.describe` call is refused with, and what the requirement-supply
/// cluster's positive pins revert to when their fix is backed out.
///
/// Lifted here for the same reason [`DESC_INSTANCES`] was, at the same count: it had
/// been copy-pasted byte-identically into three files (`wi817_polyrec_requirement`,
/// `wi822_op_scoped_supply`, `wi824_abstract_mispin`) and WI-823 was about to add a
/// fourth. It is PRODUCER-COUPLED — the `format!` raising `MissingRequiresForSpecOp`
/// in `kb/typing.rs` — so a reworded diagnostic must desync one reader, not four
/// independently. It also carries a U+2026, easy to mistype and awkward to grep for.
///
/// Assign it to a file-local `const MISSING_REQUIRES: &str =
/// common::MISSING_DESC_REQUIRES;` so each file's assertions keep reading their own
/// short name. Pair it with the SITE (`<ns>.Desc.describe.requires`) when asserting:
/// `DESC_INSTANCES` contains its own abstract call in `WrapDesc.describe`, so the
/// text alone does not say WHICH call was refused.
#[allow(dead_code)]
pub const MISSING_DESC_REQUIRES: &str = "missing `requires Desc[T = …]`";

/// The rewritten term for the call to `spec_op_qn` inside operation `op_qn` — the
/// site-scoped read that replaced `assert_req_param_spec` (WI-873).
///
/// `kb.dispatch_origin_iter()` is KB-GLOBAL, so "the rewrite for this spec op" is not
/// a question it can answer for a caller who means their OWN fixture's: `PartialEq.eq`
/// is deferred from a dozen stdlib bodies as well as the fixture's. Before WI-873 the
/// rewrite table kept exactly ONE entry per spec op for the whole image — every call
/// site of one functor collapsed onto one synthesized key — so the suites here took
/// "the first (or last) entry for this spec" and got whichever body won a `HashMap`
/// race. They could then only assert the SPEC of the requirement-param name, via a
/// tolerant `assert_req_param_spec` helper, because the disambiguating suffix belonged
/// to a stranger's chain.
///
/// WI-873 keyed the table by [`CallSite`], so every site's rewrite is recorded and the
/// enclosing OPERATION selects one. That is what lets these suites assert the exact
/// synthesized name again — the name is now their fixture's, by construction.
///
/// Panics unless exactly one rewrite matches: zero means the call was not classified
/// (or the operation name is wrong), and more than one means the operation calls the
/// spec op at several sites and the caller must say which.
#[allow(dead_code)]
pub fn rewrite_in_op(
    kb: &KnowledgeBase,
    op_qn: &str,
    spec_op_qn: &str,
) -> anthill_core::kb::term::TermId {
    let op_sym = kb
        .try_resolve_symbol(op_qn)
        .unwrap_or_else(|| panic!("no operation symbol `{op_qn}`"));
    let spec_sym = kb
        .try_resolve_symbol(spec_op_qn)
        .unwrap_or_else(|| panic!("no spec-op symbol `{spec_op_qn}`"));
    let hits: Vec<_> = kb
        .dispatch_rewrites_iter()
        .filter(|(site, r)| site.op == op_sym && r.spec_op == spec_sym)
        .map(|(_, r)| r.rewritten)
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "expected exactly one recorded rewrite of `{spec_op_qn}` inside `{op_qn}`; \
         got {}. Zero means the call was never classified; more than one means the \
         body calls it at several sites and this read must name which.",
        hits.len(),
    );
    hits[0]
}

/// The `var_ref(name = …)` requirement-param symbol at the head of a rewritten
/// `apply_within`'s `requirements` channel — the one thing a defer-rewrite assertion
/// needs, without the six-step drill down `requirements` → `cons` → `head` → `name`.
///
/// `wi222_defer_rewrite_test` and `wi227_projection_search_test` keep their drills
/// inline on purpose and are NOT counted as callers here: each of their intermediate
/// assertions carries a message about the shape THAT test is pinning (names model,
/// Strategy 1, channel cardinality), and collapsing them into one call would trade
/// four located failures for one.
///
/// Panics with the shape it found when the channel is not a single-entry list of a
/// `var_ref`: a `requirement_at_sort` head means the rewrite was a TRANSITIVE
/// deferral, which is a different claim and must not be read as this one, and a
/// non-`nil` tail means the channel carries more than one dictionary — a shape change
/// against §"Channel cardinality (v0)" that these suites exist to catch.
///
/// THE TAIL CHECK IS NOT DECORATION: WI-873's review found this doc promising it
/// while the body read only `head`, so a second dispatching dict would have slipped
/// past three suites in silence, each of them still asserting confidently about the
/// first.
#[allow(dead_code)]
pub fn defer_dict_param_name(
    kb: &KnowledgeBase,
    rewritten: anthill_core::kb::term::TermId,
) -> anthill_core::intern::Symbol {
    use anthill_core::kb::term::Term;
    use anthill_core::kb::typing::get_named_arg;

    let named = match kb.get_term(rewritten) {
        Term::Fn { named_args, .. } => named_args.clone(),
        other => panic!("rewritten term must be a Fn; got {other:?}"),
    };
    let reqs =
        get_named_arg(kb, &named, "requirements").expect("apply_within must carry `requirements`");
    let reqs_named = match kb.get_term(reqs) {
        Term::Fn { named_args, .. } => named_args.clone(),
        other => panic!("requirements must be a cons cell; got {other:?}"),
    };
    let tail = get_named_arg(kb, &reqs_named, "tail").expect("cons must carry `tail`");
    let tail_functor = match kb.get_term(tail) {
        Term::Fn { functor, .. } => *functor,
        // WI-511: the empty list is canonicalized to the bare `Ref(nil)` form.
        Term::Ref(s) => *s,
        other => panic!("tail must be a Fn (nil) or Ref (nil); got {other:?}"),
    };
    let nil_sym = kb
        .try_resolve_symbol("anthill.prelude.List.nil")
        .expect("List.nil in stdlib");
    assert_eq!(
        tail_functor,
        nil_sym,
        "the requirements channel must hold exactly one dispatching dict \
         (§\"Channel cardinality (v0)\"); tail is {}",
        kb.qualified_name_of(tail_functor)
    );

    let head = get_named_arg(kb, &reqs_named, "head").expect("cons must carry `head`");
    let (head_functor, head_named) = match kb.get_term(head) {
        Term::Fn {
            functor,
            named_args,
            ..
        } => (*functor, named_args.clone()),
        other => panic!("dispatching dict must be a Fn; got {other:?}"),
    };
    let var_ref_sym = kb
        .try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .expect("var_ref in stdlib");
    assert_eq!(
        head_functor,
        var_ref_sym,
        "dispatching dict for a DIRECT deferral must be `var_ref` (names model); got {}",
        kb.qualified_name_of(head_functor)
    );
    let name = get_named_arg(kb, &head_named, "name").expect("var_ref must carry `name`");
    match kb.get_term(name) {
        Term::Ref(s) => *s,
        other => panic!("var_ref name must be Term::Ref(<sym>); got {other:?}"),
    }
}

/// The short name of an occurrence's head functor (`test.ns.wrapped(…)` →
/// `"wrapped"`) — the assertion every `[simp]`/macro suite makes about a rewritten
/// operation body: *which* functor the rewrite produced.
///
/// WI-902: byte-identical copies had accumulated in `wi669_defining_equations_test`,
/// `wi722_compile_time_macro_test` and `wi722_read_builtins_test`, and this ticket
/// was about to add a fourth — the same trigger under which `load_stdlib_kb`,
/// `function_slot_case` and `DESC_INSTANCES` were lifted here. (Not
/// `wi687_match_specialization_test`'s same-named helper, which also maps
/// `Expr::If` → `"if"` — a different assertion, deliberately left as its own.)
///
/// Panics on a non-`Apply` head: a suite reaching for this is asserting on a
/// rewritten CALL, so a `Const`/`DotApply` head means the rewrite under test did
/// not happen — louder as a panic naming the shape than as a silent mismatch.
#[allow(dead_code)]
pub fn head_short(
    kb: &KnowledgeBase,
    occ: &std::rc::Rc<anthill_core::kb::node_occurrence::NodeOccurrence>,
) -> String {
    use anthill_core::kb::node_occurrence::Expr;
    match occ.as_expr() {
        Some(Expr::Apply { functor, .. }) => kb
            .local_name_of(*functor)
            .rsplit('.')
            .next()
            .unwrap_or("")
            .to_string(),
        other => panic!("expected a functor application, got {other:?}"),
    }
}

/// The functor SYMBOL a query pattern binds, through the shipped entry point: `fact
/// <pattern>`, `scan_definitions`, then `load::convert_query_term` at `<global>` — the
/// exact path `anthill query --pattern` takes, rather than a private resolver helper.
///
/// WI-907: lifted here at the second LIVE copy (`wi040_reserved_vocab_test` and this
/// ticket's; `wi752_dotted_ladder_test` carried a third that nothing called — the
/// dotted-ladder suite reaches this resolver through a proof target instead — and the
/// lift is what surfaced it). `head_short` and `load_kb_bare` were lifted on the same
/// trigger. The SYMBOL is the primitive: a test asking "which of these symbols?" cannot
/// ask it of a string.
///
/// Panics on a pattern that produces no `Term::Fn`: a caller reaching for this is
/// asserting about a functor, so a var/literal pattern is a test-authoring bug.
#[allow(dead_code)]
pub fn query_pattern_functor(
    kb: &mut KnowledgeBase,
    pattern: &str,
) -> anthill_core::intern::Symbol {
    use anthill_core::kb::term::Term;
    let t = query_pattern_term(kb, pattern);
    match kb.get_term(t) {
        Term::Fn { functor, .. } => *functor,
        other => panic!("query pattern `{pattern}` is not an application: {other:?}"),
    }
}

/// The WHOLE term a query pattern converts to, by the same shipped path
/// [`query_pattern_functor`] reads its head off (WI-917 lifted this out of it): a test
/// asking about a NESTED position — a disjunction branch, a data slot — cannot ask it of
/// the head symbol alone.
#[allow(dead_code)]
pub fn query_pattern_term(kb: &mut KnowledgeBase, pattern: &str) -> anthill_core::kb::term::TermId {
    let src = format!("fact {pattern}");
    let parsed = parse::parse(&src).expect("parse query pattern");
    // WI-966: MEASURED empty for every pattern the suites pass here, so the
    // scan's verdict is asserted rather than dropped — a pattern that stops
    // scanning clean must not reach `convert_query_term` unnoticed.
    let errs = load::scan_definitions(kb, &[&parsed]);
    assert!(
        errs.is_empty(),
        "query pattern `{pattern}` failed to scan: {:?}",
        errs.iter().map(|e| e.to_string()).collect::<Vec<_>>()
    );
    let global_scope = kb.global_scope();
    let mut var_map = std::collections::HashMap::new();
    for item in &parsed.items {
        if let anthill_core::parse::ir::Item::Fact(f) = item {
            return load::convert_query_term(
                kb,
                &parsed.terms,
                &parsed.symbols,
                f.term,
                global_scope,
                &mut var_map,
            );
        }
    }
    panic!("query pattern `{pattern}` produced no fact item");
}

/// [`query_pattern_functor`]'s answer as a qualified name — what a suite asserting
/// WHERE a spelling lands wants (`wi040`, `wi752`).
#[allow(dead_code)]
pub fn query_pattern_functor_qn(kb: &mut KnowledgeBase, pattern: &str) -> String {
    let sym = query_pattern_functor(kb, pattern);
    kb.qualified_name_of(sym).to_string()
}

/// WI-995 — supply imports the way `anthill query -i <ns>` does: through the
/// INVOCATION, not through a file.
///
/// Since imports became file-local, a top-level `import ns.*` written into a PROGRAM
/// source is local to that source, so it no longer reaches a query pattern or a
/// host-supplied name — those have no file to be local to. The `-i` flag is the channel
/// that does reach them, because it belongs to the run rather than to any file
/// ([`load::ImportAttribution::Invocation`]). This is the in-process spelling of it, so
/// a test that means "the query is run with these namespaces in scope" says exactly
/// that instead of relying on a program file's imports leaking outward.
///
/// Each `spec` is a flag body as the CLI takes it — `"wi907.alpha.*"`, `"a.b.{X}"`.
#[allow(dead_code)]
pub fn supply_invocation_imports(kb: &mut KnowledgeBase, specs: &[&str]) {
    for spec in specs {
        let src = format!("import {spec}\n");
        let parsed = parse::parse(&src).unwrap_or_else(|e| panic!("parse `-i {spec}`: {e:?}"));
        let ids = load::register_sources(kb, &[&parsed]);
        let errs = load::scan_definitions_with_sources(
            kb,
            &[&parsed],
            &ids,
            load::ImportAttribution::Invocation,
        );
        assert!(errs.is_empty(), "`-i {spec}` did not resolve: {errs:?}");
    }
}

/// Mount an empty in-memory extent under `name` — the live `resolve_name_in_global`
/// caller, since `register_extent_owner` resolves every `owned()` name to a `Symbol`.
/// WI-907: lifted at the second copy (`wi908_global_name_ladder_test` was the first);
/// the mount seam has already moved once under it (WI-797's `ResidentCollision`).
#[allow(dead_code)]
pub fn mount_extent(
    kb: &mut KnowledgeBase,
    name: &str,
) -> Result<(), anthill_core::kb::extent::ExtentRegError> {
    use anthill_core::kb::extent::{ArgKey, InMemoryExtentSource};
    let key = ArgKey::Named(kb.intern("id"));
    let src = InMemoryExtentSource::new(kb, name, key, vec![]).expect("no rows to key");
    kb.register_extent_owner(Box::new(src)).map(|_| ())
}

/// WI-1023 — a KB whose only rules are ALTERNATIVES FOR ONE GOAL, each binding
/// the goal's var to an arbitrary `Value` carrier. Returns `(kb, the goal's var
/// TERM, the goal TERM)`.
///
/// The gadget is `resolve_sort_instantiation_param(SortView(T: <v>), T, ?out)`,
/// which hands `?out` the `SortView`'s `T` slot **in that value's own carrier**
/// (`finish_result_value`, WI-1015). Splicing an arbitrary `Value` into that slot
/// is how a test puts an arbitrary carrier into σ.
///
/// TWO PROPERTIES THE CALLERS DEPEND ON, both learned the hard way:
///
///  - **The alternatives are for ONE goal.** Historically load-bearing: dedup used to
///    fingerprint the NEAREST ancestor ChoicePoint's goal, so two routes reached
///    through a disjunction in a rule BODY were keyed on that body goal (whose two
///    answers genuinely differ) and measured nothing — WI-1016's first shape.
///    WI-FFPGD moved the projection onto the QUERY's goals, which would catch the
///    body-disjunction shape too, so the constraint is no longer needed for
///    correctness. It is KEPT because the shape it produces is the simplest one that
///    isolates a carrier: a builtin-only body pushes no ChoicePoint and adds no
///    intermediate goal, so `wi1023_p(?x)` is both the head goal and the whole
///    query, and a row's count moves only with the carrier under test.
///  - **`build` mints inside THIS kb.** A `Symbol` indexes one KB's symbol table and
///    a `TermId` one KB's term store, so a value built elsewhere names something
///    else entirely — a mistake that reads as a green `assert_ne!` on carriers that
///    were never the pair they claimed to be.
///
/// Each inner `Vec` is one alternative: its LAST value lands in the head var (so it
/// is goal-reachable) and any earlier ones in rule-local vars the goal never
/// mentions — the domain distinction answer dedup's two guards turn on.
#[allow(dead_code)]
pub fn one_goal_carrier_fixture(
    functor_name: &str,
    build: impl FnOnce(&mut KnowledgeBase) -> Vec<Vec<eval::Value>>,
) -> (
    KnowledgeBase,
    anthill_core::kb::term::TermId,
    anthill_core::kb::term::TermId,
) {
    use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
    use anthill_core::kb::term::{Term, Var};
    use anthill_core::kb::ClauseKind;
    use anthill_core::span::{SourceId, SourceSpan};
    use eval::Value;
    use smallvec::SmallVec;
    use std::rc::Rc;

    let mut kb = load_kb_with("namespace test.wi1023_fixture\nend\n");
    let alternatives = build(&mut kb);
    assert!(
        !alternatives.is_empty(),
        "a fixture with no alternative measures nothing"
    );

    let domain = kb.intern("test");
    let span = SourceSpan::new(SourceId::from_raw(0), 0, 4);
    let p = kb.intern(functor_name);
    let sort_view = kb.intern("SortView");
    let t_param = kb.intern("T");
    let rsip = kb.resolve_symbol("anthill.reflect.resolve_sort_instantiation_param");

    for slots in alternatives {
        let v = {
            let n = kb.intern("?v");
            kb.fresh_var(n)
        };
        let v_term = kb.alloc(Term::Var(Var::Global(v)));
        let head = kb.alloc(Term::Fn {
            functor: p,
            pos_args: SmallVec::from_elem(v_term, 1),
            named_args: SmallVec::new(),
        });
        let last = slots.len() - 1;
        let body: Vec<Rc<NodeOccurrence>> = slots
            .into_iter()
            .enumerate()
            .map(|(i, slot)| {
                let out = if i == last {
                    v
                } else {
                    let n = kb.intern("?w");
                    kb.fresh_var(n)
                };
                let inst = Value::Entity {
                    functor: sort_view,
                    pos: Rc::from(Vec::<Value>::new()),
                    named: Rc::from(vec![(t_param, slot)]),
                };
                NodeOccurrence::new_expr(
                    Expr::Apply {
                        recv_type: None,
                        functor: rsip,
                        pos_args: vec![
                            NodeOccurrence::new_expr(Expr::Spliced(inst), span, None),
                            NodeOccurrence::new_expr(
                                Expr::Spliced(Value::SymbolRef(t_param)),
                                span,
                                None,
                            ),
                            NodeOccurrence::new_expr(Expr::Var(Var::Global(out)), span, None),
                        ],
                        named_args: Vec::new(),
                        type_args: Vec::new(),
                    },
                    span,
                    None,
                )
            })
            .collect();
        kb.assert_rule_debruijn_with_nodes(Value::term(head), body, ClauseKind::Rule, domain, None);
    }

    let q = {
        let n = kb.intern("?q");
        kb.fresh_var(n)
    };
    let q_term = kb.alloc(Term::Var(Var::Global(q)));
    let goal = kb.alloc(Term::Fn {
        functor: p,
        pos_args: SmallVec::from_elem(q_term, 1),
        named_args: SmallVec::new(),
    });
    (kb, q_term, goal)
}

/// WI-1045 — a requirement dictionary `Dictionary(subs…, impl: impl_sym)`, the
/// one construction path a test has.
///
/// WI-867: the UNCHECKED constructor on purpose — these fixtures drive the value
/// carrier (a projection reading slot `k`, `Dictionary.impl` reading a symbol back),
/// where the (spec, provider) pair is not a claim about any spec and a layout would be
/// a fiction invented to satisfy. A host building EVIDENCE uses
/// `Interpreter::alloc_dictionary`, which refuses a wrong-shaped one at construction.
///
/// It goes through the interpreter rather than assembling a
/// `Value::Entity` by hand ON PURPOSE: a test that spelled the functor and the
/// `impl` key itself would keep passing if the production spelling moved, which
/// is exactly the drift `dictionary_view_syms` exists to make impossible.
/// Panics in a KB that never loaded `anthill.realization.runtime` — for a test
/// that is a broken fixture, not a state to handle.
#[allow(dead_code)]
pub fn dict(
    interp: &Interpreter,
    impl_sym: anthill_core::intern::Symbol,
    subs: impl IntoIterator<Item = eval::value::Dictionary>,
) -> eval::value::Dictionary {
    interp
        .alloc_dictionary_unchecked(impl_sym, subs)
        .expect("the loaded stdlib declares anthill.realization.runtime.Dictionary")
}

/// WI-1045 — the dictionary IR CONSTRUCTION node,
/// `Dictionary(sub₀ … subₙ₋₁, impl: impl_sym)`.
///
/// ONE SPELLING with the value (`requirement-channel.md` §9): same functor, same
/// key set. This resolves both names the way the typer's `build_dictionary_term`
/// does — the QUALIFIED accessor for `impl`, not a bare `intern("impl")`, which
/// is a different symbol and would build a node the materializer reads as having
/// no `impl` at all.
#[allow(dead_code)]
pub fn dict_term(
    kb: &mut KnowledgeBase,
    impl_sym: anthill_core::intern::Symbol,
    subs: &[anthill_core::kb::term::TermId],
) -> anthill_core::kb::term::TermId {
    use anthill_core::kb::term::Term;
    let ctor = kb
        .try_resolve_symbol("anthill.realization.runtime.Dictionary")
        .expect("the loaded stdlib declares anthill.realization.runtime.Dictionary");
    let impl_key = kb
        .try_resolve_symbol("anthill.realization.runtime.Dictionary.impl")
        .expect("the loaded stdlib declares Dictionary.impl");
    let impl_ref = kb.alloc(Term::Ref(impl_sym));
    kb.alloc(Term::Fn {
        functor: ctor,
        pos_args: subs.iter().copied().collect(),
        named_args: smallvec::SmallVec::from_slice(&[(impl_key, impl_ref)]),
    })
}
