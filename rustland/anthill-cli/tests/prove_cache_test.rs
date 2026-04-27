//! End-to-end exercise of the WI-096 proof cache.
//!
//! Skipped when `z3` isn't on $PATH (cache is wired around the solver
//! invocation, so without z3 we can't drive a hit/miss cycle).

use std::path::PathBuf;
use std::process::Command;

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

fn z3_available() -> bool {
    Command::new("z3").arg("--version").output()
        .map(|o| o.status.success()).unwrap_or(false)
}

fn write_temp(name: &str, contents: &str) -> PathBuf {
    let dir = std::env::temp_dir()
        .join(format!("anthill-cache-test-{}-{}", std::process::id(), name));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, contents).unwrap();
    path
}

const SRC_BASE: &str = r#"
    namespace test.cache.simple
      export simple_unsat
      entity Cfg(scale: Int)
      fact Cfg(scale: 5)

      rule simple_unsat(?marker)
        :- Cfg(scale: ?s), gt(?s, 99), eq(?marker, ?s)

      proof simple_unsat by z3(logic: "LIA") end
    end
"#;

fn run_prove(source_path: &str, cache_dir: &PathBuf, extra_args: &[&str]) -> (bool, String) {
    let mut cmd = Command::new(ANTHILL_BIN);
    cmd.args(["prove", source_path, "-v", "--cache-dir"])
        .arg(cache_dir);
    for arg in extra_args { cmd.arg(arg); }
    let out = cmd.output().expect("run anthill prove");
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    (out.status.success(), stdout)
}

#[test]
fn cache_hit_on_second_run() {
    if !z3_available() {
        eprintln!("skipping: z3 not on $PATH");
        return;
    }
    let path = write_temp("hit.anthill", SRC_BASE);
    let cache_dir = std::env::temp_dir()
        .join(format!("anthill-cache-hit-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&cache_dir);

    let (ok1, out1) = run_prove(path.to_str().unwrap(), &cache_dir, &[]);
    assert!(ok1, "first run failed: {out1}");
    assert!(!out1.contains("cache hit"),
        "first run should be a miss: {out1}");

    let (ok2, out2) = run_prove(path.to_str().unwrap(), &cache_dir, &[]);
    assert!(ok2, "second run failed: {out2}");
    assert!(out2.contains("cache hit"),
        "second run should hit the cache: {out2}");
}

#[test]
fn cache_invalidates_on_transitive_fact_edit() {
    if !z3_available() {
        eprintln!("skipping: z3 not on $PATH");
        return;
    }
    let path = write_temp("invalidate.anthill", SRC_BASE);
    let cache_dir = std::env::temp_dir()
        .join(format!("anthill-cache-inval-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&cache_dir);

    let (ok1, _) = run_prove(path.to_str().unwrap(), &cache_dir, &[]);
    assert!(ok1);
    let (ok2, out2) = run_prove(path.to_str().unwrap(), &cache_dir, &[]);
    assert!(ok2);
    assert!(out2.contains("cache hit"), "second run before edit must hit");

    // Edit the transitively-referenced fact's value.
    std::fs::write(&path, SRC_BASE.replace("scale: 5", "scale: 7")).unwrap();
    let (ok3, out3) = run_prove(path.to_str().unwrap(), &cache_dir, &[]);
    assert!(ok3, "post-edit run failed: {out3}");
    assert!(!out3.contains("cache hit"),
        "post-edit run must be a miss (transitive fact change must \
         invalidate the cache key): {out3}");
}

#[test]
fn no_cache_flag_bypasses_lookup_and_write() {
    if !z3_available() {
        eprintln!("skipping: z3 not on $PATH");
        return;
    }
    let path = write_temp("nocache.anthill", SRC_BASE);
    let cache_dir = std::env::temp_dir()
        .join(format!("anthill-cache-bypass-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&cache_dir);

    let (ok1, _) = run_prove(path.to_str().unwrap(), &cache_dir, &["--no-cache"]);
    assert!(ok1);
    // Cache dir should not have been populated.
    let projects_dir = cache_dir.join("projects");
    assert!(!projects_dir.exists() || projects_dir.read_dir().map(|i| i.count()).unwrap_or(0) == 0,
        "--no-cache must not write entries");

    let (ok2, out2) = run_prove(path.to_str().unwrap(), &cache_dir, &["--no-cache"]);
    assert!(ok2);
    assert!(!out2.contains("cache hit"),
        "--no-cache must not hit the cache");
}

#[test]
fn show_cache_lists_entries() {
    if !z3_available() { return; }
    let path = write_temp("show.anthill", SRC_BASE);
    let cache_dir = std::env::temp_dir()
        .join(format!("anthill-cache-show-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&cache_dir);

    // Populate cache.
    run_prove(path.to_str().unwrap(), &cache_dir, &[]);

    // --show-cache exits without dispatching proofs and lists entries.
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "--show-cache",
               "--cache-dir"]).arg(&cache_dir)
        .output().expect("run anthill prove --show-cache");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "show-cache failed: {stdout}");
    assert!(stdout.contains("entries"), "expected entries summary: {stdout}");
    assert!(stdout.contains("proved"),
        "expected proved verdict in listing: {stdout}");
    assert!(!stdout.contains("summary:"),
        "show-cache should not run proofs: {stdout}");
}

#[test]
fn gc_cache_removes_old_entries() {
    if !z3_available() { return; }
    let path = write_temp("gc.anthill", SRC_BASE);
    let cache_dir = std::env::temp_dir()
        .join(format!("anthill-cache-gc-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&cache_dir);
    run_prove(path.to_str().unwrap(), &cache_dir, &[]);

    // GC with 0 days ⇒ everything is older than 0 days ⇒ delete all.
    let out = Command::new(ANTHILL_BIN)
        .args(["prove", path.to_str().unwrap(), "--gc-cache", "0",
               "--cache-dir"]).arg(&cache_dir)
        .output().expect("run anthill prove --gc-cache 0");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "gc failed: {stdout}");
    assert!(stdout.contains("removed"));

    // Subsequent normal run must miss (cache empty).
    let (_, post) = run_prove(path.to_str().unwrap(), &cache_dir, &[]);
    assert!(!post.contains("cache hit"),
        "after GC, next run must miss: {post}");
}

#[test]
fn stats_flag_prints_hit_miss_summary() {
    if !z3_available() { return; }
    let path = write_temp("stats.anthill", SRC_BASE);
    let cache_dir = std::env::temp_dir()
        .join(format!("anthill-cache-stats-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&cache_dir);

    let (_, miss_out) = run_prove(path.to_str().unwrap(), &cache_dir, &["--stats"]);
    assert!(miss_out.contains("cache:"),
        "expected cache stats line: {miss_out}");
    assert!(miss_out.contains("1 miss"),
        "first run should record 1 miss: {miss_out}");
    assert!(miss_out.contains("1 written"),
        "first run should record 1 write: {miss_out}");

    let (_, hit_out) = run_prove(path.to_str().unwrap(), &cache_dir, &["--stats"]);
    assert!(hit_out.contains("1 hit"),
        "second run should record 1 hit: {hit_out}");
}

#[test]
fn refresh_cache_forces_resolver_rerun_then_writes() {
    if !z3_available() {
        eprintln!("skipping: z3 not on $PATH");
        return;
    }
    let path = write_temp("refresh.anthill", SRC_BASE);
    let cache_dir = std::env::temp_dir()
        .join(format!("anthill-cache-refresh-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&cache_dir);

    // Populate the cache.
    let (_, _) = run_prove(path.to_str().unwrap(), &cache_dir, &[]);
    // Confirm second run hits.
    let (_, out_hit) = run_prove(path.to_str().unwrap(), &cache_dir, &[]);
    assert!(out_hit.contains("cache hit"));
    // --refresh-cache must NOT hit even with a populated cache.
    let (ok, out) = run_prove(path.to_str().unwrap(), &cache_dir, &["--refresh-cache"]);
    assert!(ok);
    assert!(!out.contains("cache hit"),
        "--refresh-cache must bypass lookup: {out}");
}
