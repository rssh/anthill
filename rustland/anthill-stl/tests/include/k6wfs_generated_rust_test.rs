//! K6WFS: the Rust `anthill codegen rust` writes for a program over prelude sorts
//! compiles against this crate.
//!
//! `fixtures/k6wfs_result.rs` is the generator's output for `fixtures/k6wfs_result.anthill`,
//! checked in. `include!` compiles it here, as part of this test binary, against the
//! `anthill` crate it `use`s — so a `use anthill::prelude::{…}` naming something the
//! crate does not export, or a host type it writes wrongly, fails the build of the
//! suite. The test beside it holds the checked-in file to what the generator writes
//! today, so the file compiled is the generator's. MEASURED before the change: the
//! generator wrote `use anthill::prelude::{Int64, String, Option, Result, List, Pair};`,
//! of which `Int64` and `Result` do not resolve here, and `Result<Boom, i64>`.

#[allow(dead_code)]
mod generated {
    include!("../fixtures/k6wfs_result.rs");
}

#[test]
fn the_compiled_file_is_what_the_generator_writes() {
    let source = include_str!("../fixtures/k6wfs_result.anthill");
    let parsed = anthill_core::parse::parse(source).expect("the fixture parses");
    let generated = anthill_core::codegen::generate_rust(&parsed)
        .unwrap_or_else(|e| panic!("the fixture generates: {e:?}"));
    assert_eq!(
        generated,
        include_str!("../fixtures/k6wfs_result.rs"),
        "the generator's output moved; regenerate the fixture with \
         `anthill codegen rust -o anthill-stl/tests/fixtures \
         anthill-stl/tests/fixtures/k6wfs_result.anthill` (from rustland/) and read the diff"
    );
    // The two the ticket is about, said where a reader of this test looks.
    assert!(generated.contains("fn check(n: i64) -> Result<i64, Boom>;"));
    assert!(
        !generated.contains("Int64"),
        "the anthill `Int64` is written `i64`"
    );
}
