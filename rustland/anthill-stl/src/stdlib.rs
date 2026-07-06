//! The canonical embedded standard-library source set, shared by every anthill
//! binary (the CLI `run`/`check`/`prove` commands and `anthill-todo`).
//!
//! This list used to be duplicated — one copy in anthill-cli, one in
//! anthill-todo — which DRIFTED apart (each missing files the other carried).
//! It is now the single source of truth both binaries call.
//!
//! ## Why the list is explicit and ORDERED (not an alphabetical dir walk)
//!
//! Load order is significant: operation/spec dispatch resolves against the
//! `provides` facts in load order, so a derived-algebra file (`prelude/algebra`,
//! `prelude/lattice`) loaded *before* the base type files it builds on can
//! hijack `+` / `compare` dispatch and send a primitive operation into infinite
//! recursion. An earlier alphabetical-walk version of this list put `algebra`
//! ahead of `int64`/`numeric`/`string` and overflowed the stack on the first
//! program that sorted or summed (e.g. `anthill-todo status`). The order below
//! is dependency-respecting: primitives → base types → eq/ordered/numeric →
//! collections → derived algebra → the rest. `tests/stdlib_drift_test` walks the
//! source trees and fails loudly if a `.anthill` file is added or removed
//! without being placed here, so completeness is enforced without ceding the
//! ordering to the filesystem.

use anthill_core::parse;
use anthill_core::parse::ir::ParsedFile;

/// `(label, source)` for every embedded `.anthill` file, in load order. The
/// label is a human-readable path used only in parse-error messages, and is
/// the key `tests/stdlib_drift_test` reconciles against the on-disk trees.
pub static SOURCES: &[(&str, &str)] = &[
    // ── prelude (dependency order: base types before derived algebra) ──
    ("anthill/prelude/primitives", include_str!("../../../stdlib/anthill/prelude/primitives.anthill")),
    ("anthill/prelude/bool", include_str!("../../../stdlib/anthill/prelude/bool.anthill")),
    ("anthill/prelude/int64", include_str!("../../../stdlib/anthill/prelude/int64.anthill")),
    ("anthill/prelude/bigint", include_str!("../../../stdlib/anthill/prelude/bigint.anthill")),
    ("anthill/prelude/float", include_str!("../../../stdlib/anthill/prelude/float.anthill")),
    ("anthill/prelude/string", include_str!("../../../stdlib/anthill/prelude/string.anthill")),
    ("anthill/prelude/eq", include_str!("../../../stdlib/anthill/prelude/eq.anthill")),
    ("anthill/prelude/ordered", include_str!("../../../stdlib/anthill/prelude/ordered.anthill")),
    ("anthill/prelude/totalfloat", include_str!("../../../stdlib/anthill/prelude/totalfloat.anthill")),
    ("anthill/prelude/numeric", include_str!("../../../stdlib/anthill/prelude/numeric.anthill")),
    ("anthill/prelude/monad", include_str!("../../../stdlib/anthill/prelude/monad.anthill")),
    ("anthill/prelude/delay", include_str!("../../../stdlib/anthill/prelude/delay.anthill")),
    ("anthill/prelude/option", include_str!("../../../stdlib/anthill/prelude/option.anthill")),
    ("anthill/prelude/list", include_str!("../../../stdlib/anthill/prelude/list.anthill")),
    ("anthill/prelude/pair", include_str!("../../../stdlib/anthill/prelude/pair.anthill")),
    ("anthill/prelude/unit", include_str!("../../../stdlib/anthill/prelude/unit.anthill")),
    ("anthill/prelude/nothing", include_str!("../../../stdlib/anthill/prelude/nothing.anthill")),
    ("anthill/prelude/set", include_str!("../../../stdlib/anthill/prelude/set.anthill")),
    ("anthill/prelude/map", include_str!("../../../stdlib/anthill/prelude/map.anthill")),
    ("anthill/prelude/field", include_str!("../../../stdlib/anthill/prelude/field.anthill")),
    ("anthill/prelude/sort", include_str!("../../../stdlib/anthill/prelude/sort.anthill")),
    ("anthill/prelude/meta", include_str!("../../../stdlib/anthill/prelude/meta.anthill")),
    ("anthill/prelude/function", include_str!("../../../stdlib/anthill/prelude/function.anthill")),
    ("anthill/prelude/collection", include_str!("../../../stdlib/anthill/prelude/collection.anthill")),
    ("anthill/prelude/iteration", include_str!("../../../stdlib/anthill/prelude/iteration.anthill")),
    ("anthill/prelude/iterable", include_str!("../../../stdlib/anthill/prelude/iterable.anthill")),
    ("anthill/prelude/finite_collection", include_str!("../../../stdlib/anthill/prelude/finite_collection.anthill")),
    ("anthill/prelude/mutable_collection", include_str!("../../../stdlib/anthill/prelude/mutable_collection.anthill")),
    ("anthill/prelude/indexed_seq", include_str!("../../../stdlib/anthill/prelude/indexed_seq.anthill")),
    ("anthill/prelude/stream", include_str!("../../../stdlib/anthill/prelude/stream.anthill")),
    ("anthill/prelude/combinators", include_str!("../../../stdlib/anthill/prelude/combinators.anthill")),
    ("anthill/prelude/finite_stream", include_str!("../../../stdlib/anthill/prelude/finite_stream.anthill")),
    ("anthill/prelude/finite_combinators", include_str!("../../../stdlib/anthill/prelude/finite_combinators.anthill")),
    ("anthill/prelude/logical_stream", include_str!("../../../stdlib/anthill/prelude/logical_stream.anthill")),
    ("anthill/prelude/lattice", include_str!("../../../stdlib/anthill/prelude/lattice.anthill")),
    ("anthill/prelude/effects", include_str!("../../../stdlib/anthill/prelude/effects.anthill")),
    ("anthill/prelude/effects-runtime", include_str!("../../../stdlib/anthill/prelude/effects-runtime.anthill")),
    ("anthill/prelude/cell", include_str!("../../../stdlib/anthill/prelude/cell.anthill")),
    ("anthill/prelude/mutable_stack", include_str!("../../../stdlib/anthill/prelude/mutable_stack.anthill")),
    ("anthill/prelude/console", include_str!("../../../stdlib/anthill/prelude/console.anthill")),
    ("anthill/prelude/time", include_str!("../../../stdlib/anthill/prelude/time.anthill")),
    ("anthill/prelude/algebra", include_str!("../../../stdlib/anthill/prelude/algebra.anthill")),
    // ── geometry ──
    ("anthill/geometry", include_str!("../../../stdlib/anthill/geometry.anthill")),
    // ── reflect ──
    ("anthill/reflect/reflect", include_str!("../../../stdlib/anthill/reflect/reflect.anthill")),
    ("anthill/reflect/typing", include_str!("../../../stdlib/anthill/reflect/typing.anthill")),
    ("anthill/reflect/feed", include_str!("../../../stdlib/anthill/reflect/feed.anthill")),
    // ── realization ──
    ("anthill/realization/realization", include_str!("../../../stdlib/anthill/realization/realization.anthill")),
    ("anthill/realization/runtime", include_str!("../../../stdlib/anthill/realization/runtime.anthill")),
    ("anthill/realization/platform", include_str!("../../../stdlib/anthill/realization/platform.anthill")),
    ("anthill/realization/rust_std", include_str!("../../../stdlib/anthill/realization/rust_std.anthill")),
    ("anthill/realization/cpp_std", include_str!("../../../stdlib/anthill/realization/cpp_std.anthill")),
    ("anthill/realization/witness", include_str!("../../../stdlib/anthill/realization/witness.anthill")),
    ("anthill/realization/policy", include_str!("../../../stdlib/anthill/realization/policy.anthill")),
    ("anthill/realization/rust_anthill", include_str!("../../../stdlib/anthill/realization/rust_anthill.anthill")),
    ("anthill/realization/scala_std", include_str!("../../../stdlib/anthill/realization/scala_std.anthill")),
    ("anthill/realization/scala_caps", include_str!("../../../stdlib/anthill/realization/scala_caps.anthill")),
    // ── persistence ──
    ("anthill/persistence/store", include_str!("../../../stdlib/anthill/persistence/store.anthill")),
    ("anthill/persistence/filesystem", include_str!("../../../stdlib/anthill/persistence/filesystem.anthill")),
    ("anthill/persistence/sql", include_str!("../../../stdlib/anthill/persistence/sql.anthill")),
    // ── cli ──
    ("anthill/cli/main", include_str!("../../../stdlib/anthill/cli/main.anthill")),
    ("anthill/cli/spec", include_str!("../../../stdlib/anthill/cli/spec.anthill")),
    ("anthill/cli/parse", include_str!("../../../stdlib/anthill/cli/parse.anthill")),
    ("anthill/cli/help", include_str!("../../../stdlib/anthill/cli/help.anthill")),
    // ── kernel + logic (resolver primitives / proof-axiom schemas; consumed
    //    by `prove … by derivation`, inert for ordinary evaluation) ──
    ("anthill/kernel/kernel", include_str!("../../../stdlib/anthill/kernel/kernel.anthill")),
    ("anthill/logic/minimal", include_str!("../../../stdlib/anthill/logic/minimal.anthill")),
    ("anthill/logic/constructive", include_str!("../../../stdlib/anthill/logic/constructive.anthill")),
    ("anthill/logic/classical", include_str!("../../../stdlib/anthill/logic/classical.anthill")),
    // ── Rust-language spec-satisfaction bindings (this crate's own anthill/
    //    tree). These carry `fact Eq[T = String]`, `fact Numeric[T = Int64]`,
    //    etc. — the impls the typer's spec dispatch resolves against. Loaded
    //    last so they refine the base definitions above. ──
    ("rustland/anthill-stl/bool", include_str!("../anthill/bool.anthill")),
    ("rustland/anthill-stl/int64", include_str!("../anthill/int64.anthill")),
    ("rustland/anthill-stl/bigint", include_str!("../anthill/bigint.anthill")),
    ("rustland/anthill-stl/float", include_str!("../anthill/float.anthill")),
    ("rustland/anthill-stl/string", include_str!("../anthill/string.anthill")),
    ("rustland/anthill-stl/geometry", include_str!("../anthill/geometry.anthill")),
];

// Build-time tripwire: a fully-empty embedded set means the layout moved or the
// list was wrongly cleared. `include_str!` already fails the compile loudly if
// a listed file vanishes; this covers the emptied-list case (the deleted
// anthill-cli build.rs panicked the build on an empty stdlib root — restore a
// build-time guard rather than relying on `tests/stdlib_drift_test` alone).
const _: () = assert!(!SOURCES.is_empty());

/// Parse all embedded stdlib sources, in load order. Returns (parsed files,
/// parse errors). A non-empty errors vec means the embedded sources are
/// malformed at compile time — a build regression, not a user-facing condition.
pub fn parse_embedded() -> (Vec<ParsedFile>, Vec<String>) {
    let mut files = Vec::new();
    let mut errors = Vec::new();

    for &(path, source) in SOURCES {
        match parse::parse(source) {
            Ok(parsed) => files.push(parsed),
            Err(errs) => {
                for e in &errs {
                    errors.push(format!("stdlib {path}: {e}"));
                }
            }
        }
    }

    (files, errors)
}
