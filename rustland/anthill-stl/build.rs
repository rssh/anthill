use std::collections::HashMap;
use std::path::PathBuf;

use anthill_core::codegen::{CodegenConfig, generate_rust_with_config, collect_trait_sorts};
use anthill_core::parse;

fn main() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let stdlib_dir = manifest_dir.join("../../stdlib/anthill");
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());

    let config = CodegenConfig {
        flatten_top_namespace: true,
        emit_fn_bodies: true,
        // WI-535: the opaque `Term` sort binds to the carrier-faithful
        // `Value` (not a bare `TermId`). A generated host op over a `Term`
        // (e.g. `Store.persist(fact: Term)`) thus carries an occurrence/entity
        // without lowering it to a hash-consed id.
        carrier_bindings: HashMap::from([
            ("Term".into(), "anthill_core::eval::Value".into()),
            ("FactId".into(), "anthill_core::kb::RuleId".into()),
        ]),
        namespace_map: HashMap::from([
            ("anthill".into(), "crate".into()),
        ]),
        derives: vec!["Clone".into(), "Debug".into()],
        default_pub: true,
        boxed_trait_objects: false,
        emit_only: None,
        suppress_imports: false,
    };

    // WI-540: the reflect interface (`KB`/`Substitution` traits + data types)
    // is GENERATED-AND-USED — `reflect/mod.rs` `include!`s it and `KbBridge`
    // implements it, so the compiler enforces bridge == spec. Two reflect-only
    // knobs vs the base config:
    //   * `boxed_trait_objects` — `KB` must be `&dyn KB`-usable and `Solution`
    //     carries a `Substitution` trait object, so trait-typed positions emit
    //     `Box<dyn _>` / `&dyn _` (object-safe) instead of `impl _`.
    //   * the reflect `Term`/`Symbol` are DISTINCT, opaque reflect types (NOT
    //     the rust-internal `Value`/`Symbol`): the API never names the carrier;
    //     `KbBridge` converts `Term`/`Symbol` ↔ `Value`/`TermId`/`intern::Symbol`
    //     at the impl boundary. Bound to the hand-written newtypes in `mod.rs`.
    let reflect_config = CodegenConfig {
        carrier_bindings: HashMap::from([
            ("Term".into(), "ReflectTerm".into()),
            ("Symbol".into(), "ReflectSymbol".into()),
            // WI-545: `NodeOccurrence` (declared in reflect.anthill, so the
            // codegen carrier-alias fires) binds to an opaque `Value` carrier so
            // `OperationInfo.requires`/`ensures` can hold the loader's stored
            // clause Values.
            ("NodeOccurrence".into(), "ReflectNodeOccurrence".into()),
            ("FactId".into(), "anthill_core::kb::RuleId".into()),
        ]),
        boxed_trait_objects: true,
        // Generate only the KB-bridge subset of reflect.anthill — the `KB` /
        // `Substitution` traits + `Solution` / `LogicalQuery` + the introspection
        // data types + the opaque carriers they reference. The occurrence IR
        // (`Expr` / `Pattern` / …) and the free reflect ops stay interpreter-only.
        emit_only: Some(vec![
            "Term".into(), "Symbol".into(), "FactId".into(),
            "ConstraintId".into(), "NodeOccurrence".into(),
            "KB".into(), "Substitution".into(),
            "Solution".into(), "LogicalQuery".into(),
            "TermRepr".into(), "LiteralRepr".into(),
            "SortInfo".into(), "OperationInfo".into(),
            "FieldInfo".into(), "DescriptionInfo".into(),
        ]),
        ..config.clone()
    };

    // WI-553: `stream.rs` is GENERATED-AND-USED (like reflect). The `Stream`
    // trait must be object-safe — the host `KB.execute` returns `Box<dyn
    // Stream<Solution, Error>>` and `split_first` carries a `Box<dyn Stream>`
    // tail — so `boxed_trait_objects` boxes self-returns and `Self: Sized`-bounds
    // the generic fold methods. `suppress_imports` drops the spec's body/rule
    // imports (value ctors, `Numeric`, `Iterable`/`Modify`), which the
    // signature-only output never references; the `prelude::stream` shim supplies
    // the one import the signatures need (`Pair`).
    let stream_config = CodegenConfig {
        boxed_trait_objects: true,
        suppress_imports: true,
        ..config.clone()
    };

    // Source → generated output mapping
    let files = [
        ("prelude/stream.anthill", "stream.rs"),
        ("prelude/logical_stream.anthill", "logical_stream.rs"),
        ("prelude/meta.anthill", "meta.rs"),
        ("reflect/reflect.anthill", "reflect.rs"),
        ("persistence/store.anthill", "store.rs"),
        ("persistence/filesystem.anthill", "filesystem.rs"),
        ("persistence/sql.anthill", "sql.rs"),
    ];

    // Parse all files
    let mut parsed_files = Vec::new();
    for (src, _) in &files {
        let source_path = stdlib_dir.join(src);
        let source = std::fs::read_to_string(&source_path)
            .unwrap_or_else(|e| panic!("read {}: {}", source_path.display(), e));
        let parsed = parse::parse(&source)
            .unwrap_or_else(|e| panic!("parse {}: {:?}", source_path.display(), e));
        parsed_files.push(parsed);
    }

    // Collect trait sorts across all files for cross-file impl Trait wrapping
    let refs: Vec<_> = parsed_files.iter().collect();
    let global_traits = collect_trait_sorts(&refs);

    // Generate each file (reflect uses the generated-and-used reflect_config).
    for (i, (_, dst)) in files.iter().enumerate() {
        let cfg = match *dst {
            "reflect.rs" => &reflect_config,
            "stream.rs" => &stream_config,
            _ => &config,
        };
        let code = generate_rust_with_config(&parsed_files[i], &global_traits, cfg)
            .unwrap_or_else(|e| panic!("codegen {}: {:?}", dst, e));
        let out_path = out_dir.join(dst);
        std::fs::write(&out_path, &code)
            .unwrap_or_else(|e| panic!("write {}: {}", out_path.display(), e));
    }

    // Rerun if source changes
    println!("cargo:rerun-if-changed=../../stdlib/anthill");
}
