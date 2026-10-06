//! Measurement for docs/design/test-infrastructure.md. Kept HERE, not under
//! `anthill-core/examples/` (`cargo test` builds examples): copy it there to run,
//! remove it after.
//!
//! Measures the numbers the test-speed design hinges on:
//!   parse      — read + tree-sitter parse of the stdlib + rust host bindings
//!   full       — fresh KB + load_all(stdlib + bindings + one small user file)   [what every test pays]
//!   pre_typer  — same, LoadOptions { run_typer: false }                          [everything before the typer]
//!   incr       — load_all(one small user file) INTO an already-loaded stdlib KB  [what a cached-KB design pays]
//!
//! ITERS=<n> picks the iteration count (default 5). LOOP=1 runs `full` forever for a sampler.
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

fn stats(name: &str, xs: &[Duration]) {
    let mut v: Vec<f64> = xs.iter().map(|d| d.as_secs_f64() * 1000.0).collect();
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let med = v[v.len() / 2];
    println!("{name:10} n={:2}  min={:8.1}ms  median={:8.1}ms  max={:8.1}ms", v.len(), v[0], med, v[v.len() - 1]);
}

fn main() {
    let iters: usize = std::env::var("ITERS").ok().and_then(|s| s.parse().ok()).unwrap_or(5);
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

    if std::env::var("LOOP").is_ok() {
        loop {
            let mut refs: Vec<&parse::ir::ParsedFile> = parsed.iter().collect();
            refs.push(&user);
            let mut kb = KnowledgeBase::new();
            load::load_all(&mut kb, &refs, &NullResolver).map_err(|e| e.len()).unwrap();
        }
    }

    // full
    let mut t = vec![];
    for _ in 0..iters {
        let mut refs: Vec<&parse::ir::ParsedFile> = parsed.iter().collect();
        refs.push(&user);
        let s = Instant::now();
        let mut kb = KnowledgeBase::new();
        load::load_all(&mut kb, &refs, &NullResolver).map_err(|e| e.len()).unwrap();
        t.push(s.elapsed());
    }
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
}
