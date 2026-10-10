//! Measurement for docs/design/test-infrastructure.md. Kept HERE, not under
//! `anthill-core/examples/` (`cargo test` builds examples): copy it there to run,
//! remove it after.
//!
//! Measures the numbers the test-speed design hinges on:
//!   parse      — read + tree-sitter parse of the stdlib + rust host bindings
//!   full       — fresh KB + load_all(stdlib + bindings + one small user file)   [what every test pays]
//!   pre_typer  — same, LoadOptions { run_typer: false }                          [everything before the typer]
//!   incr       — load_all(one small user file) INTO an already-loaded stdlib KB  [what a cached-KB design pays]
//!   clone      — KnowledgeBase::deep_clone of the loaded stdlib                     [WI-20261009-D0SD4]
//!   clone+incr — the copy, then the user file loaded into it                        [what WI-059 would pay per test]
//!   sealed incr / sealed clone+incr — the same two with the stdlib's load SEALED before
//!                the user file (`load::seal_declarations`), as the test recipes and the
//!                shared base do: a sealed load's bodies are not typed again
//!                (WI-20261010-9BKZ4). `incr` and `clone+incr` seal nothing and are what
//!                a plain sequence of loads pays.
//!
//! ITERS=<n> picks the iteration count (default 5). LOOP=1 runs `full` forever for a sampler.
//! THREADS=<n> runs `full` on n threads at once, ITERS loads each, and reports the
//! per-load time and the throughput — whether loads SCALE, which is what a test
//! binary's `--test-threads` assumes. Each thread builds its own KB on a default-size
//! (2 MiB) stack, as a libtest thread does.
use std::path::PathBuf;
use std::time::{Duration, Instant};

use anthill_core::kb::load::{self, LoadOptions, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

const USER_SRC: &str = r#"
namespace test.bench_user
  import anthill.prelude.{Int64, Cell, Unit}

  operation overwrite(c: Cell[V = Int64], n: Int64) -> Unit effects Modify[c] = Cell.set(c, n)
end
"#;

fn files() -> Vec<PathBuf> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut v = anthill_core::fs_util::collect_files(&root.join("../../stdlib/anthill"), &["anthill"]).unwrap();
    v.extend(anthill_core::fs_util::collect_files(&root.join("../anthill-stl/anthill"), &["anthill"]).unwrap());
    v.sort();
    v
}

fn parse_all(paths: &[PathBuf]) -> Vec<parse::ir::ParsedFile> {
    paths
        .iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap_or_else(|e| panic!("{p:?}: {e:?}")))
        .collect()
}

/// One `full` load — fresh KB, `load_all(stdlib ∪ bindings ∪ user)` — and how long it took.
/// The ONE definition: `full`, the `THREADS` rows and `LOOP` all call it, so the thread
/// columns cannot come to measure a different load than the column they are read against.
fn full_load(parsed: &[parse::ir::ParsedFile], user: &parse::ir::ParsedFile) -> Duration {
    let mut refs: Vec<&parse::ir::ParsedFile> = parsed.iter().collect();
    refs.push(user);
    let s = Instant::now();
    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &refs, &NullResolver).map_err(|e| e.len()).unwrap();
    s.elapsed()
}

/// An environment variable that, when set, must be a positive count — a malformed value is
/// an error, not a silent fall-back to the default measurement.
fn count_var(name: &str) -> Option<usize> {
    let raw = std::env::var(name).ok()?;
    match raw.parse::<usize>() {
        Ok(n) if n > 0 => Some(n),
        _ => panic!("{name}={raw:?}: expected a positive integer"),
    }
}

fn stats(name: &str, xs: &[Duration]) {
    let mut v: Vec<f64> = xs.iter().map(|d| d.as_secs_f64() * 1000.0).collect();
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let med = v[v.len() / 2];
    println!("{name:17} n={:2}  min={:8.1}ms  median={:8.1}ms  max={:8.1}ms", v.len(), v[0], med, v[v.len() - 1]);
}

fn main() {
    let iters: usize = count_var("ITERS").unwrap_or(5);
    let paths = files();
    println!("files: {}", paths.len());

    // parse
    let mut t = vec![];
    let mut parsed = vec![];
    for _ in 0..iters {
        let s = Instant::now();
        parsed = parse_all(&paths);
        t.push(s.elapsed());
    }
    stats("parse", &t);
    let user = parse::parse(USER_SRC).unwrap();

    if let Some(n) = count_var("THREADS") {
        let wall = Instant::now();
        let all: Vec<Duration> = std::thread::scope(|sc| {
            let handles: Vec<_> = (0..n)
                .map(|_| {
                    sc.spawn(|| (0..iters).map(|_| full_load(&parsed, &user)).collect::<Vec<_>>())
                })
                .collect();
            handles.into_iter().flat_map(|h| h.join().unwrap()).collect()
        });
        let wall = wall.elapsed().as_secs_f64();
        stats(&format!("full x{n}"), &all);
        println!("threads={n} loads={} wall={wall:.2}s throughput={:.2} loads/s", all.len(), all.len() as f64 / wall);
        return;
    }

    if std::env::var("LOOP").is_ok() {
        loop {
            full_load(&parsed, &user);
        }
    }

    // full
    let t: Vec<Duration> = (0..iters).map(|_| full_load(&parsed, &user)).collect();
    stats("full", &t);

    // pre_typer
    let mut t = vec![];
    for _ in 0..iters {
        let mut refs: Vec<&parse::ir::ParsedFile> = parsed.iter().collect();
        refs.push(&user);
        let s = Instant::now();
        let mut kb = KnowledgeBase::new();
        load::load_all_with(&mut kb, &refs, &NullResolver, LoadOptions { run_typer: false, ..Default::default() })
            .map_err(|e| e.len())
            .unwrap();
        t.push(s.elapsed());
    }
    stats("pre_typer", &t);

    // incr: stdlib first (untimed), then the user file alone (timed)
    let mut t = vec![];
    for _ in 0..iters {
        let refs: Vec<&parse::ir::ParsedFile> = parsed.iter().collect();
        let mut kb = KnowledgeBase::new();
        load::load_all(&mut kb, &refs, &NullResolver).map_err(|e| e.len()).unwrap();
        let s = Instant::now();
        load::load_all(&mut kb, &[&user], &NullResolver).map_err(|e| e.len()).unwrap();
        t.push(s.elapsed());
    }
    stats("incr", &t);

    // sealed incr: the same, the stdlib's load sealed first (WI-20261010-9BKZ4)
    let mut t = vec![];
    for _ in 0..iters {
        let refs: Vec<&parse::ir::ParsedFile> = parsed.iter().collect();
        let mut kb = KnowledgeBase::new();
        load::load_all(&mut kb, &refs, &NullResolver).map_err(|e| e.len()).unwrap();
        load::seal_declarations(&mut kb);
        let s = Instant::now();
        load::load_all(&mut kb, &[&user], &NullResolver).map_err(|e| e.len()).unwrap();
        t.push(s.elapsed());
    }
    stats("sealed incr", &t);

    // clone: a deep copy of the loaded stdlib (WI-20261009-D0SD4) — what a test pays
    // INSTEAD of the stdlib's load once the base is shared (WI-059).
    // clone+incr: the copy, then the user file loaded into it — the whole of what a
    // test pays then, beside `full`.
    let refs: Vec<&parse::ir::ParsedFile> = parsed.iter().collect();
    let mut base = KnowledgeBase::new();
    load::load_all(&mut base, &refs, &NullResolver).map_err(|e| e.len()).unwrap();
    let (mut copy_only, mut copy_and_load) = (vec![], vec![]);
    for _ in 0..iters {
        let s = Instant::now();
        let mut kb = base.deep_clone().expect("a loaded stdlib copies");
        copy_only.push(s.elapsed());
        load::load_all(&mut kb, &[&user], &NullResolver).map_err(|e| e.len()).unwrap();
        copy_and_load.push(s.elapsed());
    }
    stats("clone", &copy_only);
    stats("clone+incr", &copy_and_load);

    // The same over a SEALED base — what a test on the shared base pays.
    load::seal_declarations(&mut base);
    let mut copy_and_load = vec![];
    for _ in 0..iters {
        let s = Instant::now();
        let mut kb = base.deep_clone().expect("a sealed stdlib copies");
        load::load_all(&mut kb, &[&user], &NullResolver).map_err(|e| e.len()).unwrap();
        copy_and_load.push(s.elapsed());
    }
    stats("sealed clone+incr", &copy_and_load);
}
