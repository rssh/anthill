//! WI-20261001-KDMQS — A `const` IN A CLAUSE'S DATA SLOT IS ITS VALUE, and this module
//! owns which value that is.
//!
//! Spec §5.9 calls a const "a name that IS a value at every term position". An operation
//! body honours that lazily: eval forces the const on first demand (`force_const`). A
//! clause's data slot is not evaluated, it is MATCHED. The discrimination tree indexes
//! whatever the loader stored, so `fact f(v: D_MIN)` stored the SYMBOL, and neither the
//! query `f(v: 1.5)` nor a join against a computed `1.5` could find it. The IEEE specials
//! were worse. Their only spelling is the const's (`Float.infinity`), so a persisted
//! `+∞` reloaded as the structure `field_access(Float, infinity)`, with nothing said.
//!
//! So the loader folds a const in a data slot to its value WHEN THE CLAUSE CONVERTS, in
//! every walk that builds one side of a match (fact and rule heads, rule and constraint
//! bodies, query patterns). Folding at conversion means the value must be known before the
//! typer runs, and this module states what that allows. The declaration pass records each
//! const's value SOURCE before any clause converts; [`KnowledgeBase::const_slot_value`]
//! reads it back:
//!
//!  - a LITERAL body (`const D_MIN: Float = 1.5`, `const B: Int64 = -1`) is its own value;
//!  - a body that NAMES another const has that const's value (a cycle is refused);
//!  - a `language rust` `const_map` entry is the interpreter's registered host value. It
//!    takes precedence over a body, as it does in `force_const`;
//!  - any other body is COMPUTED. Its value needs the evaluator over a typed KB, which no
//!    clause conversion has. A data slot that names one is refused loudly, and the slot
//!    never stores the symbol (storing it was the silent miss this ticket removes).
//!
//! A QUERY pattern is the one walk that may do better: it converts against a loaded
//! program, so a const with no load-time value is asked of the evaluator there
//! ([`KnowledgeBase::evaluated_const_literal`]).
//!
//! Operation bodies are not touched. They keep the symbol and fold lazily at eval, which
//! is also what keeps a program whose binding layer is not the interpreter's (cpp-gen)
//! loadable: only a data slot asks for the value at load.

use crate::intern::Symbol;
use crate::kb::term::Literal;
use crate::kb::KnowledgeBase;

/// Where a const's load-time value comes from, recorded by the declaration pass.
#[derive(Clone, Debug)]
pub(crate) enum ConstSource {
    /// `const N: T = <literal>`.
    Literal(Literal),
    /// `const A: T = B`. The body names another const, and `A` has `B`'s value.
    Alias(Symbol),
    /// Any other body. Its value needs the evaluator, which a clause conversion cannot run.
    Computed,
    /// A `language rust` binding block's `const_map` entry: the key the interpreter's host
    /// registry holds the value source under.
    Host(String),
}

/// Why a const has no load-time value. Carries the const the chain STOPPED at, which is
/// not the one the slot named when the slot named an alias.
#[derive(Clone, Debug)]
pub(crate) struct ConstUnavailable {
    pub(crate) at: Symbol,
    pub(crate) why: ConstUnavailableWhy,
}

#[derive(Clone, Debug)]
pub(crate) enum ConstUnavailableWhy {
    /// The body computes the value (`2.0 * D_MIN`, a call, …).
    Computed,
    /// Bodyless, and no `language rust` binding block maps it.
    NoInterpreterBinding,
    /// The `const_map` key names nothing in the interpreter's host registry.
    UnknownHostKey(String),
    /// The `const_map` key names a host function that takes arguments.
    HostNotNullary { key: String, arity: usize },
    /// The host value source ran and failed.
    HostFailed { key: String, message: String },
    /// The host value source returned something that is not a scalar literal.
    HostNotScalar { key: String },
    /// The alias chain comes back to a const it already passed.
    Cycle,
}

impl ConstUnavailable {
    /// The reason, as a clause of a sentence about the const `named` in a data slot.
    pub(crate) fn describe(&self, kb: &KnowledgeBase, named: Symbol) -> String {
        let at = kb.qualified_name_of(self.at);
        let via = if self.at == named {
            String::new()
        } else {
            format!(" (its value is `{at}`'s)")
        };
        let why = match &self.why {
            ConstUnavailableWhy::Computed => format!(
                "`{at}`'s body computes its value, and a computed value needs the evaluator, \
                 which a clause does not have when it loads. Only a literal-bodied or \
                 host-supplied const has a value there"
            ),
            ConstUnavailableWhy::NoInterpreterBinding => format!(
                "`{at}` is host-supplied, and no `language rust` binding block gives it a \
                 value (`const_map`)"
            ),
            ConstUnavailableWhy::UnknownHostKey(key) => format!(
                "the `const_map` entry for `{at}` names host value {key:?}, which this runtime \
                 does not provide"
            ),
            ConstUnavailableWhy::HostNotNullary { key, arity } => format!(
                "the `const_map` entry for `{at}` names {key:?}, which takes {arity} \
                 argument(s); a const's value source takes none"
            ),
            ConstUnavailableWhy::HostFailed { key, message } => {
                format!("`{at}`'s host value source {key:?} failed: {message}")
            }
            ConstUnavailableWhy::HostNotScalar { key } => {
                format!("`{at}`'s host value source {key:?} returned a value that is not a literal")
            }
            ConstUnavailableWhy::Cycle => {
                format!("`{at}` is defined through itself, so it has no value")
            }
        };
        format!("{why}{via}")
    }
}

impl KnowledgeBase {
    /// Record `sym`'s value source (the declaration pass). A host source is never replaced
    /// by a body source, which is `force_const`'s precedence.
    ///
    /// Clears every memoized value rather than `sym`'s alone, because an alias chain can run
    /// THROUGH `sym`. A later load phase may bring the binding block for a const an earlier
    /// phase declared, so this is not only a first-write path.
    pub(crate) fn record_const_source(&mut self, sym: Symbol, source: ConstSource) {
        if matches!(self.const_sources.get(&sym), Some(ConstSource::Host(_)))
            && !matches!(source, ConstSource::Host(_))
        {
            return;
        }
        self.const_sources.insert(sym, source);
        self.const_slot_values.clear();
    }

    /// The value a data slot that names the const `sym` holds, memoized. See the module doc
    /// for what has a value at load and what does not.
    pub(crate) fn const_slot_value(&mut self, sym: Symbol) -> Result<Literal, ConstUnavailable> {
        if let Some(memo) = self.const_slot_values.get(&sym) {
            return memo.clone();
        }
        let mut seen: Vec<Symbol> = Vec::new();
        let mut at = sym;
        let answer = loop {
            if seen.contains(&at) {
                break Err(ConstUnavailableWhy::Cycle);
            }
            seen.push(at);
            match self.const_sources.get(&at).cloned() {
                Some(ConstSource::Literal(lit)) => break Ok(lit),
                Some(ConstSource::Alias(next)) => at = next,
                Some(ConstSource::Computed) => break Err(ConstUnavailableWhy::Computed),
                Some(ConstSource::Host(key)) => {
                    break crate::eval::builtins::host_const_literal(self, &key)
                }
                None => break Err(ConstUnavailableWhy::NoInterpreterBinding),
            }
        };
        let answer = answer.map_err(|why| ConstUnavailable { at, why });
        self.const_slot_values.insert(sym, answer.clone());
        answer
    }

    /// `sym`'s value from the EVALUATOR (`force_const`), as a literal, or `None` when it
    /// cannot be computed or is not a literal. Only for a QUERY pattern, which converts
    /// against a loaded program. A clause converting mid-load must not call it: the KB it
    /// would lend to the interpreter is half-built.
    pub(crate) fn evaluated_const_literal(&mut self, sym: Symbol) -> Option<Literal> {
        use crate::kb::term_view::TermView;
        let value = self
            .run_in_bridge_interp(|interp| interp.force_const(sym))?
            .ok()?;
        value.as_literal(self)
    }
}
