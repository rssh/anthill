/// Embedded standard library sources for standalone binary distribution.
///
/// All `.anthill` files from `stdlib/anthill/` are compiled into the binary
/// via `include_str!()`. Use `parse_embedded_stdlib()` to get parsed files.
///
/// During development, pass `-p path/to/stdlib/anthill` to load from disk instead.

use anthill_core::parse;
use anthill_core::parse::ir::ParsedFile;

static STDLIB_SOURCES: &[(&str, &str)] = &[
    // prelude
    ("anthill/prelude/primitives", include_str!("../../../stdlib/anthill/prelude/primitives.anthill")),
    ("anthill/prelude/bool", include_str!("../../../stdlib/anthill/prelude/bool.anthill")),
    ("anthill/prelude/int", include_str!("../../../stdlib/anthill/prelude/int.anthill")),
    ("anthill/prelude/bigint", include_str!("../../../stdlib/anthill/prelude/bigint.anthill")),
    ("anthill/prelude/float", include_str!("../../../stdlib/anthill/prelude/float.anthill")),
    ("anthill/prelude/string", include_str!("../../../stdlib/anthill/prelude/string.anthill")),
    ("anthill/prelude/eq", include_str!("../../../stdlib/anthill/prelude/eq.anthill")),
    ("anthill/prelude/ordered", include_str!("../../../stdlib/anthill/prelude/ordered.anthill")),
    ("anthill/prelude/numeric", include_str!("../../../stdlib/anthill/prelude/numeric.anthill")),
    ("anthill/prelude/option", include_str!("../../../stdlib/anthill/prelude/option.anthill")),
    ("anthill/prelude/list", include_str!("../../../stdlib/anthill/prelude/list.anthill")),
    ("anthill/prelude/pair", include_str!("../../../stdlib/anthill/prelude/pair.anthill")),
    ("anthill/prelude/unit", include_str!("../../../stdlib/anthill/prelude/unit.anthill")),
    ("anthill/prelude/nothing", include_str!("../../../stdlib/anthill/prelude/nothing.anthill")),
    ("anthill/prelude/set", include_str!("../../../stdlib/anthill/prelude/set.anthill")),
    ("anthill/prelude/map", include_str!("../../../stdlib/anthill/prelude/map.anthill")),
    ("anthill/prelude/sort", include_str!("../../../stdlib/anthill/prelude/sort.anthill")),
    ("anthill/prelude/meta", include_str!("../../../stdlib/anthill/prelude/meta.anthill")),
    ("anthill/prelude/function", include_str!("../../../stdlib/anthill/prelude/function.anthill")),
    ("anthill/prelude/collection", include_str!("../../../stdlib/anthill/prelude/collection.anthill")),
    ("anthill/prelude/iteration", include_str!("../../../stdlib/anthill/prelude/iteration.anthill")),
    ("anthill/prelude/indexed_seq", include_str!("../../../stdlib/anthill/prelude/indexed_seq.anthill")),
    ("anthill/prelude/stream", include_str!("../../../stdlib/anthill/prelude/stream.anthill")),
    ("anthill/prelude/logical_stream", include_str!("../../../stdlib/anthill/prelude/logical_stream.anthill")),
    ("anthill/prelude/lattice", include_str!("../../../stdlib/anthill/prelude/lattice.anthill")),
    ("anthill/prelude/effects", include_str!("../../../stdlib/anthill/prelude/effects.anthill")),
    ("anthill/prelude/effect-set", include_str!("../../../stdlib/anthill/prelude/effect-set.anthill")),
    ("anthill/prelude/algebra", include_str!("../../../stdlib/anthill/prelude/algebra.anthill")),
    // geometry
    ("anthill/geometry", include_str!("../../../stdlib/anthill/geometry.anthill")),
    // reflect
    ("anthill/reflect/reflect", include_str!("../../../stdlib/anthill/reflect/reflect.anthill")),
    ("anthill/reflect/typing", include_str!("../../../stdlib/anthill/reflect/typing.anthill")),
    // realization
    ("anthill/realization/realization", include_str!("../../../stdlib/anthill/realization/realization.anthill")),
    ("anthill/realization/platform", include_str!("../../../stdlib/anthill/realization/platform.anthill")),
    ("anthill/realization/rust_std", include_str!("../../../stdlib/anthill/realization/rust_std.anthill")),
    ("anthill/realization/cpp_std", include_str!("../../../stdlib/anthill/realization/cpp_std.anthill")),
    // persistence
    ("anthill/persistence/store", include_str!("../../../stdlib/anthill/persistence/store.anthill")),
    ("anthill/persistence/filesystem", include_str!("../../../stdlib/anthill/persistence/filesystem.anthill")),
    ("anthill/persistence/sql", include_str!("../../../stdlib/anthill/persistence/sql.anthill")),
    // cli
    ("anthill/cli/main", include_str!("../../../stdlib/anthill/cli/main.anthill")),
    ("anthill/cli/spec", include_str!("../../../stdlib/anthill/cli/spec.anthill")),
    ("anthill/cli/parse", include_str!("../../../stdlib/anthill/cli/parse.anthill")),
    ("anthill/cli/help", include_str!("../../../stdlib/anthill/cli/help.anthill")),
];

/// Parse all embedded stdlib sources.
pub fn parse_embedded_stdlib() -> (Vec<ParsedFile>, Vec<String>) {
    let mut files = Vec::new();
    let mut errors = Vec::new();

    for &(path, source) in STDLIB_SOURCES {
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
