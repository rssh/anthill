//! Goal-routing registry for queryable persistence backends.
//!
//! Proposal 007 §11 + 026.1 Q4 (Stage B). When the resolver encounters a
//! goal whose head functor is registered here, it consults the
//! [`RouteHandler`] before (in addition to) the discrim-tree lookup. The
//! handler returns an [`ExternalStream`] whose `Value::Entity` rows enter
//! σ via `bind_value` — no `TermStore` allocation per row.
//!
//! ## Scope (Stage B v1)
//!
//! - Registry keyed by **head functor symbol**. One handler per functor.
//!   Multiple sorts routing to the same store register the same handler
//!   under each functor.
//! - Lookup is direct (`HashMap<Symbol, …>`); the anthill-level
//!   `route(GoalSort(?))` rule is *not* yet consulted at resolution time.
//!   Wiring the route-rule path is downstream — see proposal 007 §11
//!   "Q4 implementation contract (landed)".
//! - Eager drain at `step_init`: every row matching the goal is converted
//!   to a candidate `Substitution` before the choice point is built. Lazy
//!   per-iteration pumping is a follow-up; the eager path is correct, just
//!   memory-proportional to the matching row count.
//!
//! ## Lifecycle
//!
//! Handlers live for the lifetime of the [`KnowledgeBase`]. They are
//! registered once (typically at startup, after stdlib load) and consulted
//! on every routed goal. A handler must produce a fresh stream per
//! `retrieve` call — concurrent / nested resolutions each get an
//! independent cursor.

use std::collections::HashMap;

use crate::intern::Symbol;

use super::KnowledgeBase;
use crate::eval::stream::ExternalStream;
use crate::eval::value::Value;

/// Trait-driven row source for a routed goal. The `pattern` argument is the
/// goal as a carrier-neutral [`Value`] (WI-696) as it appears in the resolver — a
/// `Value::Term`, or a `Value::Node` occurrence goal that has no hash-consed twin
/// — read through [`TermView`](super::term_view::TermView)
/// (`pattern.head(kb).functor_sym()`, `pattern.pos_arg(kb, i)`, …). The handler
/// may inspect arguments to push filters down to its backend, or ignore them and
/// stream every row.
///
/// Stateless by convention: a single registered handler may be invoked
/// many times across resolutions. Per-call state (open cursors, file
/// handles) lives inside the returned [`ExternalStream`].
pub trait RouteHandler {
    fn retrieve(&self, kb: &KnowledgeBase, pattern: &Value) -> Box<dyn ExternalStream>;
}

/// Blanket impl for closures: lets callers register a backend with
/// `kb.register_route_handler(sym, |kb, pattern| Box::new(...))` instead
/// of declaring a struct + impl per backend.
impl<F> RouteHandler for F
where
    F: Fn(&KnowledgeBase, &Value) -> Box<dyn ExternalStream>,
{
    fn retrieve(&self, kb: &KnowledgeBase, pattern: &Value) -> Box<dyn ExternalStream> {
        (self)(kb, pattern)
    }
}

/// Per-KB registry. Held inside [`KnowledgeBase`]; not exposed publicly
/// except via `register_route_handler` / `route_handler_for`.
#[derive(Default)]
pub(crate) struct RouteRegistry {
    handlers: HashMap<Symbol, Box<dyn RouteHandler>>,
}

impl RouteRegistry {
    pub(crate) fn new() -> Self { Self::default() }

    pub(crate) fn register(&mut self, functor: Symbol, handler: Box<dyn RouteHandler>) {
        self.handlers.insert(functor, handler);
    }

    pub(crate) fn get(&self, functor: Symbol) -> Option<&dyn RouteHandler> {
        self.handlers.get(&functor).map(|b| b.as_ref())
    }

    #[allow(dead_code)]
    pub(crate) fn is_empty(&self) -> bool { self.handlers.is_empty() }
}

impl KnowledgeBase {
    /// Register an external-source backend for a goal head functor.
    /// Subsequent resolutions of `functor(...)` consult this handler in
    /// addition to the discrim-tree rule lookup.
    ///
    /// Replacing an existing handler is allowed; the prior one is dropped.
    pub fn register_route_handler<H>(&mut self, functor: Symbol, handler: H)
    where
        H: RouteHandler + 'static,
    {
        self.routes.register(functor, Box::new(handler));
    }

    /// Look up the registered handler for `functor`. Returns `None` if no
    /// handler is registered — the resolver then falls through to the
    /// in-KB discrim-tree path only.
    pub fn route_handler_for(&self, functor: Symbol) -> Option<&dyn RouteHandler> {
        self.routes.get(functor)
    }
}
