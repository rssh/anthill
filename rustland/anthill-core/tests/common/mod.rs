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

/// Collect all .anthill files from stdlib + the Rust host bindings.
/// Use this in place of `collect_anthill_files(&stdlib_dir())` for tests
/// that depend on `fact Spec[Carrier]` records emitted by the rustland
/// `provides Carrier language rust` blocks.
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

/// Like [`try_load_kb_with`] but loads MULTIPLE user source strings as SEPARATE
/// files (each its own `ParsedFile`) alongside the stdlib — for asserting
/// cross-file load behavior, e.g. WI-321 cross-file mutual structural recursion
/// (two files whose entities reference each other's sorts must both load).
#[allow(dead_code)]
pub fn try_load_kb_with_files(sources: &[&str]) -> Result<KnowledgeBase, Vec<String>> {
    let user: Vec<_> = sources
        .iter()
        .map(|s| parse::parse(s).expect("parse user source"))
        .collect();

    let mut refs: Vec<&parse::ir::ParsedFile> = STDLIB_PARSED.iter().collect();
    refs.extend(user.iter());
    let mut kb = KnowledgeBase::new();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => Ok(kb),
        Err(errs) => Err(errs.iter().map(|e| e.to_string()).collect()),
    }
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

/// Walk an anthill cons-list `Value` into its `Int64` elements.
///
/// A list is a chain of `cons(head, tail)` entities terminated by a
/// zero-field `nil`; each `cons` carries its two components as NAMED fields, so
/// the head is the `Int` among them and the tail the `Entity`. Several
/// per-WI suites grew a private copy of this walk (wi714_*, wi727, wi730);
/// this is the shared one to reach for.
/// The HEAD VALUES of a `cons`/`nil` list, in order — the element-type-agnostic
/// peer of [`list_ints`], for suites whose elements are not `Int` (a projected
/// relation drains to `Value::Tuple` rows, WI-762).
///
/// Same walk and the same limitation: within a `cons` the TAIL is the `Entity`
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

/// field and the head is the other one, so a list whose elements are themselves
/// entities is out of scope for both helpers.
#[allow(dead_code)]
pub fn list_heads(v: &eval::Value) -> Vec<eval::Value> {
    use eval::Value;
    let mut out = Vec::new();
    let mut cur = v.clone();
    while let Value::Entity { named, .. } = &cur {
        if named.is_empty() {
            break; // nil
        }
        let mut head: Option<Value> = None;
        let mut tail: Option<Value> = None;
        for (_k, item) in named.iter() {
            match item {
                Value::Entity { .. } => tail = Some(item.clone()),
                other => head = Some(other.clone()),
            }
        }
        match (head, tail) {
            (Some(h), Some(t)) => {
                out.push(h);
                cur = t;
            }
            _ => break,
        }
    }
    out
}

#[allow(dead_code)]
pub fn list_ints(v: &eval::Value) -> Vec<i64> {
    use eval::Value;
    let mut out = Vec::new();
    let mut cur = v.clone();
    while let Value::Entity { named, .. } = &cur {
        if named.is_empty() {
            break; // nil
        }
        let mut head: Option<i64> = None;
        let mut tail: Option<Value> = None;
        for (_k, item) in named.iter() {
            match item {
                Value::Int(i) => head = Some(*i),
                Value::Entity { .. } => tail = Some(item.clone()),
                _ => {}
            }
        }
        match (head, tail) {
            (Some(h), Some(t)) => {
                out.push(h);
                cur = t;
            }
            _ => break,
        }
    }
    out
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

/// Assert that a dispatching dict's requirement-param name belongs to the SPEC the
/// caller expects — `__req_partialeq`, or a DISAMBIGUATED sibling of it.
///
/// The names-model suites (`wi222_defer_rewrite_test`, `wi227_projection_search_test`)
/// read `kb.dispatch_origin_iter()`, which is KB-GLOBAL, and take the first (or last)
/// rewrite for a spec op. MEASURED at WI-858: the map keeps exactly ONE rewrite per
/// spec op across the whole image, and which sort's survives is arbitrary — with the
/// `wi227.flat` fixture loaded the surviving `PartialEq.eq` entry is
/// `__req_partialeq_14325` (`anthill.prelude.Pair`'s, whose chain names `PartialEq`
/// twice), while with `wi222.box` it is the fixture's own `__req_partialeq`, and in
/// the same load the `Ord.compare` entry is a `Pair` ordering's
/// `__req_ord_14331`. The eviction is pre-existing — **WI-873** — but before
/// WI-858 no sort in the tree repeated a spec in its chain, so no disambiguated name
/// existed and the exact spelling always matched.
///
/// So the SUFFIX is not the fixture's to control, and asserting it made the suites
/// depend on symbol-interning order. What survives is the claim those suites are
/// actually about: the dispatching dict is a `var_ref` naming a requirement param
/// synthesized from a chain slot of THIS SPEC. A foreign spec still fails.
///
/// The accepted spellings are `synth_req_names`' (`kb::typing`), which is the one
/// minter: the bare base when the parent's chain names the spec once, else
/// `{base}_{TermId}` for a ground spec or `{base}_d{idx}` for a denoted one (WI-662).
/// Both disambiguations are accepted here — matching only the ground form would leave
/// this reader silently out of sync with its producer.
#[allow(dead_code)]
pub fn assert_req_param_spec(
    kb: &KnowledgeBase,
    actual: anthill_core::intern::Symbol,
    expected_base: &str,
    why: &str,
) {
    let actual_s = kb.local_name_of(actual);
    let disambiguated = |rest: &str| {
        let digits = rest.strip_prefix("_d").or_else(|| rest.strip_prefix('_'));
        digits.is_some_and(|d| !d.is_empty() && d.chars().all(|c| c.is_ascii_digit()))
    };
    assert!(
        actual_s == expected_base
            || actual_s
                .strip_prefix(expected_base)
                .is_some_and(disambiguated),
        "{why}: expected the requirement-param name `{expected_base}` (or a \
         `{expected_base}_<n>` / `{expected_base}_d<n>` disambiguation of the SAME spec \
         — see `assert_req_param_spec`); got `{actual_s}`",
    );
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
/// <pattern>`, `scan_definitions`, then `load::convert_query_term` at `_global` — the
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
///  - **The alternatives are for ONE goal.** `is_duplicate_projection` fingerprints
///    the NEAREST ancestor ChoicePoint's goal, so two routes reached through a
///    disjunction in a rule BODY would be keyed on that body goal (whose two answers
///    genuinely differ) and measure nothing — WI-1016's first shape. A builtin-only
///    body pushes no ChoicePoint, so the nearest ancestor for every alternative here
///    is the shared head goal.
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
/// It goes through `Interpreter::alloc_requirement` rather than assembling a
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
        .alloc_requirement(impl_sym, subs)
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
