//! WI-20261009-D0SD4 — a deep copy of a loaded knowledge base, driven from outside the
//! crate: what a copy ANSWERS, and a copy taken on another thread.
//!
//! The claim that a copy shares no `Rc` with its original — what the `unsafe impl Send`
//! of `common::SendableKb` rests on — is not checked here. It needs the KB's private
//! fields and is checked where it is made (`kb/deep_clone.rs`, with the back-outs each
//! row fails on). These rows are about the copy being a KB one can USE.

use std::sync::{LazyLock, Mutex};

use anthill_core::eval::builtins::register_standard_builtins;
use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::deep_clone::DeepCloneError;
use anthill_core::kb::extent::{ArgKey, InMemoryExtentSource};
use anthill_core::kb::load::LoadOptions;
use anthill_core::kb::KnowledgeBase;

use crate::common::rendered_load_errors as rendered;
use crate::common::{expect_loaded, load_in_a_later_call, load_stdlib_kb, SendableKb};

const WELL: &str = r#"
namespace test.d0sd4
  sort Box
    entity box(n: Int64)
  end
  fact box(n: 1)
  fact box(n: 2)

  operation double(x: Int64) -> Int64 = x + x
end
"#;

/// Refused by the typer through what the load of [`WELL`] recorded about `box`.
const ILL: &str = r#"
namespace test.d0sd4.cand
  import test.d0sd4.Box.{box}
  fact box(n: "seven")
end
"#;

fn box_facts(kb: &KnowledgeBase) -> usize {
    let Some(functor) = kb.try_resolve_symbol("test.d0sd4.Box.box") else {
        return 0;
    };
    kb.rules_by_functor(functor)
        .into_iter()
        .filter(|rid| kb.is_fact(*rid))
        .count()
}

/// `double(n)`, run over `kb`. An `i64` and not the `Value`: a `Value` holds an `Rc`
/// and may not leave the thread it was made on.
fn doubled(kb: KnowledgeBase, n: i64) -> i64 {
    let mut interp = Interpreter::new(kb);
    register_standard_builtins(&mut interp).expect("register standard eval builtins");
    match interp.call("test.d0sd4.double", &[Value::Int(n)]) {
        Ok(Value::Int(doubled)) => doubled,
        other => panic!("`double({n})` did not run to an Int64: {other:?}"),
    }
}

/// A file loaded into a COPY of the stdlib loads as it does into the stdlib itself,
/// gets the refusal it gets there, and runs.
///
/// Each KB here is used after the other was changed, so this also reads that the two
/// are apart: the copy is taken BEFORE either load, and each sees its own two facts.
///
/// FAILS when the copy loses what a later load reads — measured with
/// `entity_field_types` left empty in `deep_clone`, which fails this row and the
/// thread row below. PASSES either way by design: the count of facts, which a
/// shallow copy of the clause store gets right too.
#[test]
fn a_file_loads_into_a_copy_as_it_does_into_the_original() {
    let mut original = load_stdlib_kb();
    let mut copy = original.deep_clone().expect("a loaded stdlib copies");

    expect_loaded(load_in_a_later_call(&mut original, WELL, LoadOptions::default()));
    assert_eq!(box_facts(&copy), 0, "a load into the original reached the copy");
    expect_loaded(load_in_a_later_call(&mut copy, WELL, LoadOptions::default()));
    assert_eq!((box_facts(&original), box_facts(&copy)), (2, 2));

    // A copy of a KB that holds the user's file too, taken before the refusals below.
    let second = copy.deep_clone().expect("a KB with a user file copies");

    let refusal = |kb: &mut KnowledgeBase| match load_in_a_later_call(kb, ILL, LoadOptions::default())
    {
        Err(errors) => rendered(errors),
        Ok(_) => panic!("`fact box(n: \"seven\")` over `box(n: Int64)` must not load"),
    };
    let from_original = refusal(&mut original);
    assert!(
        from_original
            .iter()
            .any(|e| e.contains("box.n") && e.contains("expected Int64")),
        "the original's refusal names the field and its type; got {from_original:?}"
    );
    assert_eq!(refusal(&mut copy), from_original, "the copy refuses as the original does");

    assert_eq!(box_facts(&second), 2);
    assert_eq!(doubled(second, 21), 42, "an operation body copied twice over still runs");
}

/// ONE loaded stdlib, held in a `static`, and a copy of it taken by each of several
/// threads at once — the shape WI-059 puts under every test.
///
/// What this row can and cannot say: it DRIVES the path — a copy made under the lock
/// on one thread, loaded into and evaluated on another, the base read again after —
/// and fails if a copy is unusable or if one thread's load shows up in another's KB.
/// It cannot show a data race absent: that is `SendableKb`'s argument, and the rows in
/// `kb/deep_clone.rs` are what check it. It passes with a deep copy that shares an
/// `Rc`, most runs.
#[test]
fn a_copy_of_one_base_is_taken_on_each_of_several_threads() {
    static BASE: LazyLock<Mutex<SendableKb>> = LazyLock::new(|| {
        Mutex::new(SendableKb::copy_of(&load_stdlib_kb()).expect("a loaded stdlib copies"))
    });

    let workers: Vec<_> = (0..8_i64)
        .map(|i| {
            std::thread::spawn(move || {
                let mut kb = BASE.lock().expect("the base's lock").instance();
                expect_loaded(load_in_a_later_call(&mut kb, WELL, LoadOptions::default()));
                let extra = format!(
                    "namespace test.d0sd4.t{i}\n  import test.d0sd4.Box.{{box}}\n  fact box(n: {})\nend\n",
                    100 + i
                );
                expect_loaded(load_in_a_later_call(&mut kb, &extra, LoadOptions::default()));
                (box_facts(&kb), doubled(kb, i))
            })
        })
        .collect();
    for (i, worker) in workers.into_iter().enumerate() {
        let (facts, value) = worker.join().expect("a worker thread");
        assert_eq!(facts, 3, "thread {i}: the file's two facts and this thread's own");
        assert_eq!(value, 2 * i as i64, "thread {i}");
    }

    let after = BASE.lock().expect("the base's lock").instance();
    assert_eq!(box_facts(&after), 0, "what the threads loaded is not in the base");
}

/// A KB with a mounted extent source holds a live host backend, which a copy could
/// neither duplicate nor leave out. FAILS when `ExtentRegistry::deep_clone_refusal`
/// answers `None`: the copy is then `Ok`, without the mount.
#[test]
fn a_kb_with_a_mounted_backend_is_refused() {
    // An entity with NO resident facts: a mount over one that has some is a collision.
    const MOUNTED: &str = r#"
namespace test.d0sd4.mounted
  sort Item
    entity item(id: Int64)
  end
end
"#;
    let mut kb = load_stdlib_kb();
    expect_loaded(load_in_a_later_call(&mut kb, MOUNTED, LoadOptions::default()));
    assert!(kb.deep_clone().is_ok(), "the control: before the mount it copies");

    let key = ArgKey::Named(kb.intern("id"));
    let source = InMemoryExtentSource::new(&kb, "test.d0sd4.mounted.Item.item", key, vec![])
        .expect("an empty in-memory source");
    kb.register_extent_owner(Box::new(source))
        .expect("mount the source");
    let refused = kb.deep_clone().err();
    assert!(
        matches!(
            refused,
            Some(DeepCloneError::LiveBackend {
                sources: 1,
                mirrors: 0,
                records
            }) if records > 0
        ),
        "one source, and the mount that names it; got {refused:?}"
    );
}
