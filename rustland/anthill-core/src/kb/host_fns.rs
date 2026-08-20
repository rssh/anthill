//! WI-1122 — the EMBEDDER half of the `operation_map` host-function registry.
//!
//! WI-876 gave `operation_map` a DATA half that is open — any `.anthill` file may
//! write `operation_map { squish: "my_key" }` — and a FUNCTION half that is closed:
//! [`crate::eval::builtins::HOST_FNS`] is a `const` slice compiled into anthill-core,
//! and `host_fn_by_key` consulted only that. So a key the runtime does not ship was
//! an `EvalError::Internal`, and an embedder binding a carrier of its own could not
//! name its own functions at all.
//!
//! This is not a third registration tier. It is the missing half of the second one:
//! the same keys, the same arity check, the same loud refusal on a miss — with the
//! table extensible at runtime instead of frozen at compile time.
//!
//! It reaches `const_map` as well as `operation_map`, because `register_const_mappings`
//! resolves its keys through the same `host_fn_by_key`. That is a consequence of
//! sharing the lookup rather than a second feature, and the alternative — teaching the
//! lookup which caller it is serving so it could refuse one of them — would be an
//! arbitrary asymmetry with nothing behind it. WI-889 made the two channels peers
//! deliberately; they stay peers here.
//!
//! ## Why the registry lives on the `KnowledgeBase` and not on the `Interpreter`
//!
//! LOAD-BEARING, and the reason a first attempt at this ticket would be wrong.
//! `register_operation_mappings` runs for EVERY interpreter built over the program,
//! and the embedder builds only one of them. `KnowledgeBase::run_in_bridge_interp`
//! (`kb/resolve.rs`) `mem::take`s the KB and constructs a FRESH `Interpreter` per
//! bridged evaluation — one per `[simp]` fire, per bridged `eq` dispatch — then runs
//! `register_standard_builtins` on it. An embedder table held by the embedder's own
//! interpreter is simply absent there, and because an unknown key is FATAL the
//! scratch interpreter would fail to build at all: writing one `operation_map` entry
//! would break resolution program-wide, at call sites having nothing to do with the
//! mapping.
//!
//! The KB is what survives the `mem::take`, so it is the only place the embedder's
//! functions can be sitting when the scratch interpreter registers its builtins. The
//! stdlib's own hardcoded registrations survive for the analogous reason and it is
//! worth being precise about the difference: they are not carried by the interpreter
//! either, they are re-derived on each one from a function compiled into
//! anthill-core. An embedder has no such function, so it needs a home for the data,
//! and the KB is it.
//!
//! `KnowledgeBase::register_extent_owner` is the same seam in the same place, for the
//! same reason — an embedder mounting its own runtime behavior on the KB.
//!
//! ## Ordering: register BEFORE load
//!
//! Not merely before the embedder's own interpreter. LOAD ITSELF builds interpreters
//! — `build_host_op_mappings`' doc lists the crossings, and a `[simp]` macro fire
//! during load is one of them — so a table registered after `load_all` can already be
//! too late, and the failure is the fatal unknown-key one rather than a missing
//! implementation at the call.
//!
//! Registering early is also what makes the load-time promise honest:
//! `is_interpreter_mapped_op` tells the typer that this process's interpreter has an
//! implementation for a `lang == "rust"` mapping, and it answers off the mapping's
//! LANGUAGE — it does not, and cannot, check that the key resolves to anything.

use std::collections::HashMap;
use std::sync::Arc;

use crate::eval::{EvalError, Interpreter, Value};

/// A host function this process exposes to an `operation_map` clause, with the ARITY
/// it accepts.
///
/// WI-876 — the arity is carried because the registry is CLOSED, so it is known here
/// and nowhere else. Without it a mapping may bind an operation to a host function
/// that cannot take its arguments; MEASURED there: `operation squish(a: Widget) ->
/// Int64` mapped to `"ordered_compare"` (which is `expect_args::<2>`) loaded clean,
/// passed `anthill check`, and died `ArityMismatch { expected: 2, got: 1 }` on the
/// first call.
///
/// WI-1122 — an EMBEDDER entry carries it the same way and is checked by the same
/// code, which is the whole reason this type is shared rather than duplicated: the
/// arity check in `register_operation_mappings` reads `HostFn::arity` and does not
/// know or care which registry the entry came from.
///
/// THE ARITY OF AN EMBEDDER ENTRY IS TAKEN ON TRUST — it is the embedder's contract,
/// not a checked fact, and this is the one place WI-876's guarantee is weaker for the
/// open half. The runtime's own entries are audited by
/// `builtins::tests::every_host_fn_key_declares_the_arity_its_function_accepts`, which
/// probes each function with `arity` operands; no such audit is possible here, because
/// a Rust function's expected argument count is not introspectable. So an embedder
/// that declares 1 for a function doing `expect_args::<2>` reproduces exactly the
/// WI-876 defect — loads clean, passes `anthill check`, dies `ArityMismatch` at the
/// first call. An embedder wanting the guarantee should write the equivalent probe
/// over its own table.
#[derive(Clone)]
pub struct HostFn {
    pub arity: usize,
    pub f: HostFnImpl,
}

/// What actually backs a [`HostFn`]. Two variants rather than one, so that binding a
/// runtime entry stays allocation-free while an embedder can still close over state.
#[derive(Clone)]
pub enum HostFnImpl {
    /// A plain function — what `eval::builtins::HOST_FNS` holds. Costs no allocation
    /// on lookup, which matters because the lookup runs once per mapping for EVERY
    /// interpreter built over the program, including the scratch one per bridged
    /// evaluation.
    Static(fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError>),
    /// A closure over the EMBEDDER's own state. Load-bearing for the seam's purpose: a
    /// host binding a carrier of its own generally needs configuration to do it — a
    /// client, a token, a repo handle, a channel — and a bare `fn` can capture none of
    /// it, which would force every embedder into a `static`/thread-local or into
    /// smuggling config through KB facts. The layer beneath already accepts any
    /// `Fn + 'static` (`Interpreter::register_builtin_sym`), so this costs nothing but
    /// the `Arc`.
    Dynamic(Arc<dyn Fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError>>),
}

impl HostFn {
    /// Invoke it, whichever half it came from. Consumed only by tests today
    /// (`#[allow(dead_code)]`, as on `EqChange` in `kb::resolve`) — kept compiled rather
    /// than `#[cfg(test)]`-gated so a change to `HostFnImpl` or to the function signature
    /// still breaks a plain `cargo build`. The sole caller is WI-881's
    /// `every_host_fn_key_declares_the_arity_its_function_accepts`, which probes every
    /// entry of the CLOSED `HOST_FNS` table; it does NOT reach the embedder registry,
    /// whose arity stays taken on trust for the reason this type's own doc gives above.
    /// Production dispatch goes through [`Self::register_on`] into the interpreter's
    /// builtin map, never through here.
    #[allow(dead_code)]
    pub(crate) fn call(
        &self,
        interp: &mut Interpreter,
        args: &[Value],
    ) -> Result<Value, EvalError> {
        match &self.f {
            HostFnImpl::Static(f) => f(interp, args),
            HostFnImpl::Dynamic(f) => f(interp, args),
        }
    }

    /// Bind it into `interp`'s builtin map under `sym`. The one place the two variants
    /// are told apart at registration, so neither call site has to.
    pub(crate) fn register_on(&self, interp: &mut Interpreter, sym: crate::intern::Symbol) {
        match &self.f {
            HostFnImpl::Static(f) => interp.register_builtin_sym(sym, *f),
            HostFnImpl::Dynamic(f) => {
                let f = Arc::clone(f);
                interp.register_builtin_sym(sym, move |i: &mut Interpreter, a: &[Value]| f(i, a));
            }
        }
    }
}

/// Why [`crate::kb::KnowledgeBase::register_host_fn`] refused an entry.
///
/// Both arms are COLLISIONS, and both are refused rather than resolved by a
/// precedence rule. A precedence rule would mean one of two working programs
/// silently changes behavior when the other side later adds the same key — the
/// runtime growing a `HOST_FNS` entry would silently capture an embedder's
/// operations, or the embedder would silently shadow a stdlib binding. Neither is
/// visible at the mapping site, which spells only the key. Refusing keeps the
/// registry CLOSED in the sense WI-876 cares about: a key names exactly one
/// function, and which one is decidable by reading the two registries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HostFnRegError {
    /// The key is one this runtime already ships in `HOST_FNS`.
    ShadowsBuiltin { key: String },
    /// The key was already registered by this embedder.
    Duplicate { key: String },
    /// Registered AFTER the loader built its host-mapping cache — too late to be
    /// honored, and refused rather than documented-against (WI-1122 review finding 1).
    ///
    /// The ordering rule is in this module's header; what makes a late registration
    /// worth a hard refusal rather than a doc line is HOW it fails otherwise. The
    /// scratch interpreter's build error is an `EvalError::Internal`, and both bridge
    /// callers residualize one: `simp_rewrite.rs`'s macro-expansion arm and
    /// `resolve.rs`'s `bridge_op_to_eval` each `debug_assert!` on `Internal` and then
    /// return "no answer". In a DEBUG build that assert fires; in a RELEASE build the
    /// macro silently does not expand and the rule silently does not answer, and the
    /// program loads clean. A silent wrong answer is exactly what the repo's
    /// loud-over-silent rule exists to prevent, so the refusal moves to the seam where
    /// it can still be loud.
    AfterLoad { key: String },
}

impl std::fmt::Display for HostFnRegError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HostFnRegError::ShadowsBuiltin { key } => write!(
                f,
                "register_host_fn: {key:?} is a host function this runtime already \
                 provides, so registering it would silently change which \
                 implementation every `operation_map {{ …: {key:?} }}` binds to. \
                 Choose a key of your own."
            ),
            HostFnRegError::Duplicate { key } => write!(
                f,
                "register_host_fn: {key:?} is already registered by this embedder. A \
                 key names exactly one host function; register it once."
            ),
            HostFnRegError::AfterLoad { key } => write!(
                f,
                "register_host_fn: {key:?} was registered after the program was loaded, \
                 which is too late — the loader has already built its host-mapping cache, \
                 and load itself may have built interpreters that needed this key. \
                 Register every host function on the KnowledgeBase BEFORE calling \
                 load_all."
            ),
        }
    }
}

impl std::error::Error for HostFnRegError {}

/// The embedder-supplied half of the host-function table. Empty by default — a
/// program that registers nothing behaves exactly as it did before WI-1122.
#[derive(Default)]
pub struct HostFnRegistry {
    by_key: HashMap<String, HostFn>,
    /// Set once the loader has built its host-mapping cache; a registration after that
    /// point is [`HostFnRegError::AfterLoad`]. See that variant for why it is a refusal.
    sealed: bool,
}

impl HostFnRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register `key`, refusing a collision with either registry. See
    /// [`HostFnRegError`] for why a collision is refused rather than ordered.
    pub(crate) fn register(
        &mut self,
        key: &str,
        arity: usize,
        f: HostFnImpl,
    ) -> Result<(), HostFnRegError> {
        if self.sealed {
            return Err(HostFnRegError::AfterLoad {
                key: key.to_string(),
            });
        }
        if crate::eval::builtins::is_builtin_host_fn_key(key) {
            return Err(HostFnRegError::ShadowsBuiltin {
                key: key.to_string(),
            });
        }
        if self.by_key.contains_key(key) {
            return Err(HostFnRegError::Duplicate {
                key: key.to_string(),
            });
        }
        self.by_key.insert(key.to_string(), HostFn { arity, f });
        Ok(())
    }

    /// The entry for `key`, or `None`. The fallback leg of `host_fn_by_key`; a miss
    /// here is still the WI-876 refusal, not a silent skip.
    pub(crate) fn get(&self, key: &str) -> Option<HostFn> {
        self.by_key.get(key).cloned()
    }

    /// Close the registry to further entries. Called once, from
    /// `KnowledgeBase::set_host_op_mappings` — i.e. when the loader has built the cache
    /// that decides which keys are demanded — so that a late registration is refused
    /// where it can still be reported. Idempotent.
    pub(crate) fn seal(&mut self) {
        self.sealed = true;
    }
}
