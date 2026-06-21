#![allow(unused_imports)]

pub mod bridge;
pub mod builtins;

use anthill_core::eval::Value;
use anthill_core::intern::Symbol as CoreSymbol;

// ── Distinct reflect carriers (WI-540) ──────────────────────────
//
// The reflect API exposes its OWN `Term` / `Symbol`; the rust-internal
// `Value` / `TermId` / `intern::Symbol` never appear in a reflect signature.
// These opaque newtypes encapsulate the carrier (PRIVATE field) — `KbBridge`
// converts at the impl boundary. `Value` stays carrier-faithful inside (a
// `Value::Node` keeps its occurrence identity/span), so a floundered
// `Solution`'s residual remains occurrence-faithful. `build.rs` carrier-binds
// the generated `Term` → `ReflectTerm` and `Symbol` → `ReflectSymbol`.

/// The host realization of the reflect `Term`.
#[derive(Clone, Debug)]
pub struct ReflectTerm(Value);

impl ReflectTerm {
    pub(crate) fn new(v: Value) -> Self {
        ReflectTerm(v)
    }
    pub(crate) fn value(&self) -> &Value {
        &self.0
    }
    pub(crate) fn into_value(self) -> Value {
        self.0
    }
}

/// The host realization of the reflect `Symbol` (a sort/op/field name
/// reference). Wraps the interned `intern::Symbol`.
#[derive(Clone, Debug)]
pub struct ReflectSymbol(CoreSymbol);

impl ReflectSymbol {
    pub(crate) fn new(s: CoreSymbol) -> Self {
        ReflectSymbol(s)
    }
    pub(crate) fn symbol(&self) -> CoreSymbol {
        self.0
    }
}

// ── Error (Rust-only infra) ─────────────────────────────────────

#[derive(Clone, Debug)]
pub struct Error(pub String);

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for Error {}

// ── Generated reflect interface (WI-540) ────────────────────────
//
// The `KB` / `Substitution` traits, `Solution` / `LogicalQuery`, and the
// introspection data types (`TermRepr` / `SortInfo` / `OperationInfo` /
// `FieldInfo` / `DescriptionInfo` / `LiteralRepr`) are GENERATED from
// `reflect.anthill` (the single source of truth) and implemented by
// `KbBridge` / `SubstBridge` in `bridge.rs` — so the compiler enforces
// bridge == spec. The occurrence IR and the free reflect ops are
// interpreter-only (excluded via the build.rs `emit_only` subset).
include!(concat!(env!("OUT_DIR"), "/reflect.rs"));

// ── SubstBridge (Rust-only infra) ───────────────────────────────

use std::cell::RefCell;
use std::rc::Rc;
use anthill_core::kb::KnowledgeBase;

/// Host realization of the reflect `Substitution` (implements the generated
/// trait in `bridge.rs`). Wraps a core substitution and carries its own
/// `KnowledgeBase` handle, so `apply`/`compose`/`lookup` need only the
/// substitution — the trait's `&dyn KB` arg is the spec shape, unused here.
pub struct SubstBridge {
    pub inner: anthill_core::kb::subst::Substitution,
    pub(crate) kb: Rc<RefCell<KnowledgeBase>>,
}

impl SubstBridge {
    pub fn from_core(s: anthill_core::kb::subst::Substitution, kb: Rc<RefCell<KnowledgeBase>>) -> Self {
        Self { inner: s, kb }
    }
}
