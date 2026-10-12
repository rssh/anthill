//! WI-20261012-ZZ7PH — THE SORTS OF A DOCUMENT, and a spec's law lowered to one.
//!
//! Every operand this emitter wrote was a `Real`, and every comparison the theory's:
//! `PartialEq.eq` was `=` and `PartialOrd.gt` was `>` whatever a variable ranged over.
//! That is identity and a total order no requirement states, so a claim about a scope's
//! abstract parameter was answered of the reals — `gte(?a, ?a) :- gte(?a, ?b)` proved
//! under `requires PartialOrd[T = T]`, and in a scope that requires nothing — and a law
//! that bounds the carrier's size would have been inconsistent there.
//!
//! WHAT A TERM'S SORT IS READ FROM. Nothing here guesses:
//!
//!   * a variable's BOUND (`?a: T`, [`ProgramClause::type_bounds`]) — a bound is written
//!     on a head variable and nowhere else;
//!   * an operation's declared SIGNATURE (`op_info::lookup_operation_info`): a parameter
//!     typed `Int64` or `Float` is a `Real`, as the emitter models every scalar, one
//!     typed `Bool` a `Bool`, and one typed by a sort's own parameter (`a: T` of
//!     `PartialEq`) has the sort of whatever else stands in a position so typed — which
//!     is how a variable no bound can be written on (`?b` of a body) gets one;
//!   * for a LAW, the bindings of the requirement it is lowered at: an operand group no
//!     operand decides takes what the instance's chain binds the operation's parameter
//!     to ([`Emitter::param_defaults`]). A law has no bounds, and `eq(?a, ?a) <=> true`
//!     written in `Eq` is of the `PartialEq` that `Eq` provides.
//!
//! A proof's own body gets no such default: a variable that neither a bound nor a
//! signature gives a sort is REFUSED when any rule read for the document stands under a
//! scope that has an abstract parameter ([`Emitter::refusal_subject`]), and is a `Real`
//! elsewhere, as it always was — which is what keeps every document that existed before
//! this to the byte.
//!
//! A LAW IS AN ASSUMPTION ABOUT THE CARRIER, AND OF NOTHING ELSE. It is asserted only
//! when every variable it quantifies ranges over a declared sort. `Int64` and `Float`
//! are modelled by the theory's reals: a cited LEMMA over them was proved in that model,
//! but a law was not — `lt(?a, ?b) <=> lte(?a + 1, ?b)` holds of the integers and is
//! false of the reals, and asserted there it proves anything. So at a concrete carrier
//! no law is lowered: over the theory's own sorts a law is a theorem already, or is not
//! known to hold.
//!
//! AN ABSTRACT PARAMETER IS ITS OWN SORT (`declare-sort`), and a spec's operation at it
//! is an UNINTERPRETED FUNCTION, `eq` included: declared once in the consumer's
//! document, and used by the law and by the proof's body alike. Which function is
//! decided by the operation AND the carrier, so `eq` at `T` and `eq` at `U` are two.
//! An operation at theory sorts is what it was: its row of `SMT_BUILTINS`, or the loud
//! "unhandled" it has always been — never an uninterpreted function there, where it
//! would only make a discharge weaker in silence.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::load::{enclosing_scope_names, RequirementInstance};
use anthill_core::kb::node_occurrence::{materialize_from_handle, Expr, NodeOccurrence};
use anthill_core::kb::op_info::lookup_operation_info;
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::kb::typing::{sort_functor_of_view, spec_op_parent_sort, type_param_global_var};
use anthill_core::kb::{ClauseKind, KnowledgeBase, ProgramClause, SpecLaw};

use crate::{occ_as_fn, synthetic_var_name, Emitter, SmtGenError};

/// The SMT sort of a term of a document.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SmtSort {
    /// Every scalar the emitter models: an `Int64` and a `Float` alike.
    Real,
    Bool,
    /// A sort the document declares: a scope's abstract parameter, by its qualified
    /// name (`test.sg.Scope.T`).
    Declared(String),
}

impl SmtSort {
    fn is_declared(&self) -> bool {
        matches!(self, SmtSort::Declared(_))
    }
}

impl fmt::Display for SmtSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtSort::Real => f.write_str("Real"),
            SmtSort::Bool => f.write_str("Bool"),
            SmtSort::Declared(name) => f.write_str(&smt_symbol(name)),
        }
    }
}

/// `name` as an SMT-LIB symbol. A qualified name is a SIMPLE symbol as it stands — the
/// standard admits `.` and `@` in one — and is written so, which keeps a document
/// readable; anything else is quoted.
fn smt_symbol(name: &str) -> String {
    let simple = |c: char| c.is_ascii_alphanumeric() || "~!@$%^&*_-+=<>.?/".contains(c);
    let starts_plain = name
        .chars()
        .next()
        .is_some_and(|c| !c.is_ascii_digit() && c != '.' && c != '@');
    if starts_plain && name.chars().all(simple) {
        name.to_owned()
    } else {
        format!("|{}|", name.replace(['|', '\\'], "_"))
    }
}

/// What a document declares before it uses it: the sorts the theory does not have, and
/// the functions on them. One set a document, whoever asked — the proof's own body, a
/// law, a cited lemma — so a function is declared once.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Declarations {
    sorts: BTreeSet<String>,
    funs: BTreeMap<String, (Vec<SmtSort>, SmtSort)>,
}

impl Declarations {
    pub fn is_empty(&self) -> bool {
        self.sorts.is_empty() && self.funs.is_empty()
    }

    fn declare_sort(&mut self, sort: &SmtSort) {
        if let SmtSort::Declared(name) = sort {
            self.sorts.insert(name.clone());
        }
    }

    /// A function's name holds the carrier it is at, so one name at two signatures is
    /// two operations that came to one name — refused, not declared twice.
    fn declare_fun(
        &mut self,
        name: String,
        params: Vec<SmtSort>,
        result: SmtSort,
    ) -> Result<(), SmtGenError> {
        for sort in params.iter().chain(std::iter::once(&result)) {
            self.declare_sort(sort);
        }
        match self.funs.get(&name) {
            Some(declared) if *declared != (params.clone(), result.clone()) => {
                Err(SmtGenError::new(format!(
                    "`{name}` is declared at two signatures in one document: ({}) {} and ({}) {}",
                    sort_list(&declared.0),
                    declared.1,
                    sort_list(&params),
                    result
                )))
            }
            Some(_) => Ok(()),
            None => {
                self.funs.insert(name, (params, result));
                Ok(())
            }
        }
    }

    /// Add what `other` declares.
    pub fn merge(&mut self, other: &Declarations) -> Result<(), SmtGenError> {
        self.sorts.extend(other.sorts.iter().cloned());
        for (name, (params, result)) in &other.funs {
            self.declare_fun(name.clone(), params.clone(), result.clone())?;
        }
        Ok(())
    }

    /// Nothing, for a document that declares nothing: such a document is the one it was.
    pub(crate) fn render(&self, out: &mut String) {
        if self.is_empty() {
            return;
        }
        out.push_str(
            "; Declared: a scope's abstract parameter is a sort of its own, and a spec's\n\
             ; operation at it an uninterpreted function.\n",
        );
        for sort in &self.sorts {
            out.push_str(&format!("(declare-sort {} 0)\n", smt_symbol(sort)));
        }
        for (name, (params, result)) in &self.funs {
            out.push_str(&format!(
                "(declare-fun {} ({}) {result})\n",
                smt_symbol(name),
                sort_list(params)
            ));
        }
        out.push('\n');
    }
}

fn sort_list(sorts: &[SmtSort]) -> String {
    sorts
        .iter()
        .map(SmtSort::to_string)
        .collect::<Vec<_>>()
        .join(" ")
}

/// THE LOGIC A DOCUMENT IS CHECKED UNDER: the one written (or the default), and what
/// the document needs beyond it. The written logic names the proof's own arithmetic; a
/// declared function needs `UF` — z3 refuses one under `LRA`, "logic does not support
/// uninterpreted functions", and then answers `sat` — and a quantified hypothesis needs
/// the logic not to be quantifier-free. A document that declares nothing keeps its
/// logic as it is written.
pub(crate) fn document_logic(
    written: &str,
    declarations: &Declarations,
    quantified: bool,
) -> String {
    if declarations.is_empty() || written == "ALL" {
        return written.to_owned();
    }
    let (quantifier_free, rest) = match written.strip_prefix("QF_") {
        Some(rest) => (!quantified, rest),
        None => (false, written),
    };
    let with_uf = if rest.contains("UF") {
        rest.to_owned()
    } else if let Some(arrays) = rest.strip_prefix('A') {
        // `AUFLIA`: the arrays' `A` stands in front of `UF`.
        format!("AUF{arrays}")
    } else {
        format!("UF{rest}")
    };
    if quantifier_free {
        format!("QF_{with_uf}")
    } else {
        with_uf
    }
}

/// The tokens of an SMT fragment: what stands between parentheses and blanks, a quoted
/// symbol whole. A variable is one whole token — `var_1` inside the name of a declared
/// function (`ns.var_1.Scope.T`) is not one.
pub(crate) fn smt_tokens(text: &str) -> Vec<&str> {
    let mut tokens = Vec::new();
    let mut start: Option<usize> = None;
    let mut quoted = false;
    for (at, c) in text.char_indices() {
        if c == '|' {
            quoted = !quoted;
            start.get_or_insert(at);
        } else if !quoted && (c == '(' || c == ')' || c.is_whitespace()) {
            if let Some(from) = start.take() {
                tokens.push(&text[from..at]);
            }
        } else {
            start.get_or_insert(at);
        }
    }
    if let Some(from) = start {
        tokens.push(&text[from..]);
    }
    tokens
}

/// How one parameter, or the result, of an operation is typed — as far as this emitter
/// reads a type.
#[derive(Clone, Debug)]
pub(crate) enum SigType {
    /// A type parameter: a sort's own (`T` of `sort T = ?`) or the operation's. The
    /// positions typed by one parameter are of one sort, which a call's operands decide.
    Param(Symbol),
    /// A type the emitter has a sort for.
    Fixed(SmtSort),
    /// Any other: an entity, a `String`, a `List[…]`. No sort; a term of it is read by
    /// the channels the emitter already has (an entity's fields), or not at all.
    Other,
}

/// An operation's declared signature.
pub(crate) struct Signature {
    params: Vec<(Symbol, SigType)>,
    result: SigType,
}

impl Signature {
    /// The type parameters the signature is over, in the order it first names them.
    fn type_params(&self) -> Vec<Symbol> {
        let mut seen = Vec::new();
        for ty in self
            .params
            .iter()
            .map(|(_, ty)| ty)
            .chain(std::iter::once(&self.result))
        {
            if let SigType::Param(param) = ty {
                if !seen.contains(param) {
                    seen.push(*param);
                }
            }
        }
        seen
    }
}

/// The sort of each type parameter of one call's signature.
type Instance = HashMap<Symbol, SmtSort>;

/// The argument of a call that stands in parameter `index`, named `name`.
fn argument<'a>(
    kb: &KnowledgeBase,
    index: usize,
    name: Symbol,
    pos_args: &'a [Rc<NodeOccurrence>],
    named_args: &'a [(Symbol, Rc<NodeOccurrence>)],
) -> Option<&'a Rc<NodeOccurrence>> {
    pos_args.get(index).or_else(|| {
        named_args
            .iter()
            .find(|(key, _)| *key == name || kb.local_name_of(*key) == kb.local_name_of(name))
            .map(|(_, arg)| arg)
    })
}

/// A lowered law: its `(assert …)`, and what that uses and the theory does not have.
#[derive(Clone, Debug)]
pub struct LoweredLaw {
    pub assertion: String,
    pub declarations: Declarations,
}

/// WI-20261012-ZZ7PH — ONE LAW OF A SPEC ([`KnowledgeBase::spec_laws`]) AS A HYPOTHESIS
/// of a proof under a requirement of it: `(assert (forall (…) …))` over the sorts the
/// requirement's bindings are, at `instance`
/// (`anthill_core::kb::load::requirement_chain`).
///
///   * an EQUATION — `lhs <=> rhs`, stored `anthill.kernel.unify(lhs, rhs)` — is
///     `(= lhs rhs)`, a side that is `Bool`-valued a formula and not an arithmetic term;
///     a guarded one is that under its guard;
///   * a rule with a conclusion is `(=> premises conclusion)`, as a cited lemma is;
///   * a `constraint name: conclusion :- guard` is `(=> guard conclusion)`.
///
/// `Err` is a law that is NOT lowered, and says why. The caller leaves it out and says
/// so: a hypothesis left out can only lose an `unsat`. What is refused, beyond a shape
/// this does not read:
///
///   * a law that quantifies over a variable of a theory sort, or names nothing the
///     document declares — it is asserted of a carrier's own sort only (the module doc);
///   * a law one of whose premises is a rule's predicate. A cited lemma's is passed over
///     (the consumer's own body is where it is read); a law's would be DROPPED, and a
///     law without its premise states more than its spec does;
///   * a law that reads an entity's facts, which are of one KB and not of every provider.
pub fn lower_spec_law(
    kb: &KnowledgeBase,
    law: &SpecLaw,
    instance: &RequirementInstance,
) -> Result<LoweredLaw, SmtGenError> {
    let mut emitter = Emitter::new(kb);
    emitter.abstract_mode = true;
    emitter.lowering_law = Some(instance.spec_text.clone());
    emitter.seed_param_defaults(instance);
    if law.clause.clause_kind == ClauseKind::Constraint {
        emitter.collect_constraint_law(&law.clause)?;
    } else {
        emitter.collect_rule_clause(&instance.spec_text, &law.clause)?;
    }
    if !emitter.referenced_entities.is_empty() {
        return Err(SmtGenError::new(format!(
            "a law that reads the facts of an entity ({}) is not lowered: a fact is of one \
             KB, and a law is of every provider",
            emitter
                .referenced_entities
                .iter()
                .cloned()
                .collect::<Vec<_>>()
                .join(", ")
        )));
    }
    let of_a_theory_sort = emitter
        .free_vars
        .iter()
        .any(|v| !emitter.var_sorts.get(v).is_some_and(SmtSort::is_declared));
    if of_a_theory_sort || emitter.declarations.is_empty() {
        return Err(SmtGenError::new(
            "a law is asserted of a carrier's own sort, and this one quantifies over a \
             scalar or names nothing of a carrier: `Int64` and `Float` are modelled by the \
             theory's reals, where a law is a theorem already or is not known to hold",
        ));
    }
    let conclusion = match emitter.conclusion_assertions.as_slice() {
        [] => {
            return Err(SmtGenError::new(
                "the law states no conclusion this reads: an equation, a rule with a \
                 conclusion, or a `constraint conclusion :- guard`",
            ))
        }
        [one] => one.clone(),
        many => format!("(and {})", many.join(" ")),
    };
    let stated = match emitter.assertions.as_slice() {
        [] => conclusion,
        [one] => format!("(=> {one} {conclusion})"),
        many => format!("(=> (and {}) {conclusion})", many.join(" ")),
    };
    let quantified = emitter.quantifier_declarations();
    let assertion = if quantified.is_empty() {
        format!("(assert {stated})")
    } else {
        format!("(assert (forall ({quantified}) {stated}))")
    };
    Ok(LoweredLaw {
        assertion,
        declarations: emitter.declarations,
    })
}

/// What is said of a variable that nothing gives a sort, where that is refused
/// ([`Emitter::refusal_subject`]). `of` is what the variable is of; `in_a_step` says the
/// clause read is a step of a structured proof, which can write no bound of its own.
pub(crate) fn no_sort_refusal(of: &str, variable: &str, in_a_step: bool) -> SmtGenError {
    let advice = if in_a_step {
        "A step of a structured proof writes no bound: its variables take the sorts of the \
         bounds on its parent rule's head, so use a variable of that head, or compare this \
         one with a term that has a sort"
    } else {
        "Write its bound on the rule's head (`?x: T`, `?x: Float`), or the bound of a \
         variable it is compared with"
    };
    SmtGenError::new(format!(
        "{of}: nothing gives `?{variable}` a sort — neither a bound nor the signature of an \
         operation it is an operand of — and under a scope that has an abstract parameter \
         it may range over that carrier or over a scalar. {advice}"
    ))
}

/// Is `rule_qn` in a scope that has an abstract parameter — a sort with a `sort T = ?`
/// of its own, at any depth above the rule?
pub(crate) fn under_an_abstract_parameter(kb: &KnowledgeBase, rule_qn: &str) -> bool {
    enclosing_scope_names(rule_qn).iter().any(|scope| {
        kb.try_resolve_symbol(scope)
            .is_some_and(|scope| !kb.type_param_syms_of(scope).is_empty())
    })
}

impl<'kb> Emitter<'kb> {
    /// The name a clause variable goes by in the document, or `None` for one the
    /// current clause has not named (a resolution-time variable of no clause).
    pub(crate) fn var_name(&self, var: &Var) -> Option<String> {
        match var {
            Var::DeBruijn(index) => Some(synthetic_var_name(*index)),
            Var::Global(vid) => self
                .global_names
                .iter()
                .find(|(named, _)| named == vid)
                .map(|(_, name)| name.clone()),
            _ => None,
        }
    }

    /// WHAT A VARIABLE THAT NOTHING GIVES A SORT IS REFUSED OF, or `None` where it is the
    /// `Real` it always was (decided with the user, 2026-10-12). A law is lowered whole
    /// or not at all. A proof's document is refused when ANY rule read for it stands
    /// under a scope that has an abstract parameter — the rule proved, a rule it cites,
    /// a rule inlined into it: there the variable may range over the carrier or over a
    /// scalar, and the source does not say which. Asked of every rule read and not of
    /// the one proved, because a rule of a parametric scope inlined from outside it is
    /// the same body read the same way.
    pub(crate) fn refusal_subject(&self) -> Option<String> {
        if let Some(instance) = &self.lowering_law {
            return Some(format!("a law of `{instance}`"));
        }
        self.visited_rules
            .iter()
            .find(|rule| under_an_abstract_parameter(self.kb, rule))
            .map(|rule| format!("`{rule}`"))
    }

    /// The sort of the variable named `name`: what its bound or a signature gave it, and
    /// a `Real` otherwise. Declared for the document as it is read.
    pub(crate) fn declared_var_sort(&mut self, name: &str) -> SmtSort {
        let sort = self.var_sorts.get(name).cloned().unwrap_or(SmtSort::Real);
        self.declarations.declare_sort(&sort);
        sort
    }

    /// `(v Sort) …` for a quantifier over the clause's free variables.
    pub(crate) fn quantifier_declarations(&mut self) -> String {
        let free: Vec<String> = self.free_vars.iter().cloned().collect();
        free.iter()
            .map(|v| format!("({v} {})", self.declared_var_sort(v)))
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// The sort of a type the emitter has one for.
    fn scalar_sort(&self, sort: Symbol) -> Option<SmtSort> {
        match self.kb.qualified_name_of(sort) {
            "anthill.prelude.Int64" | "anthill.prelude.Float" => Some(SmtSort::Real),
            "anthill.prelude.Bool" => Some(SmtSort::Bool),
            _ => None,
        }
    }

    fn sig_type(&self, ty: &Value, type_params: &[(Symbol, Var)]) -> SigType {
        if let Value::Term { id, .. } = ty {
            if let Term::Var(var) = self.kb.get_term(*id) {
                // The operation's own bracket parameter (`unify[T](a: T, b: T)`).
                return type_params
                    .iter()
                    .find(|(_, param)| same_var(param, var))
                    .map_or(SigType::Other, |(name, _)| SigType::Param(*name));
            }
        }
        match sort_functor_of_view(self.kb, ty) {
            Some(sort) if type_param_global_var(self.kb, sort).is_some() => SigType::Param(sort),
            Some(sort) => self
                .scalar_sort(sort)
                .map_or(SigType::Other, SigType::Fixed),
            None => SigType::Other,
        }
    }

    pub(crate) fn signature(&self, operation: Symbol) -> Option<Signature> {
        let info = lookup_operation_info(self.kb, operation)?;
        Some(Signature {
            params: info
                .params
                .iter()
                .map(|(name, ty)| (*name, self.sig_type(ty, &info.type_params)))
                .collect(),
            result: self.sig_type(&info.return_type, &info.type_params),
        })
    }

    /// The sort a type is, for a bound or a requirement's binding: a declared type
    /// parameter is its own sort, a scalar a `Real`.
    fn type_sort(&self, ty: &Value) -> Option<SmtSort> {
        match self.sig_type(ty, &[]) {
            SigType::Param(param) => Some(SmtSort::Declared(
                self.kb.qualified_name_of(param).to_owned(),
            )),
            SigType::Fixed(sort) => Some(sort),
            SigType::Other => None,
        }
    }

    /// THE BOUNDS OF A CLAUSE'S HEAD VARIABLES, each as the sort it says. A bound that
    /// names the enclosing sort's parameter is a variable of the clause's frame
    /// ([`ProgramClause::frame_type_params`] says which parameter); any other is a type.
    /// One with no SMT sort — an entity, a `String`, a type with a variable of its own —
    /// is refused: the generated goals that test it are not read ([`Self::is_generated`]),
    /// so leaving the bound out would drop what the head says.
    pub(crate) fn seed_bounds(&mut self, clause: &ProgramClause) -> Result<(), SmtGenError> {
        for (index, bound) in &clause.type_bounds {
            let name = synthetic_var_name(*index);
            let frame_param = match bound {
                Value::Term { id, .. } => match self.kb.get_term(*id) {
                    Term::Var(Var::DeBruijn(slot)) => clause
                        .frame_type_params
                        .iter()
                        .find(|(at, _)| at == slot)
                        .map(|(_, param)| *param),
                    _ => None,
                },
                _ => None,
            };
            let named = match frame_param {
                Some(param) => SigType::Param(param),
                None => self.sig_type(bound, &[]),
            };
            let sort = match named {
                SigType::Param(param) => self.parameter_sort(param)?,
                SigType::Fixed(sort) => sort,
                SigType::Other => {
                    return Err(SmtGenError::new(format!(
                        "the bound of `?{name}` has no SMT sort: a bound is lowered when it is \
                         `Int64`, `Float`, `Bool` or an abstract parameter of an enclosing sort"
                    )))
                }
            };
            self.set_var_sort(&name, &sort)?;
        }
        Ok(())
    }

    /// A STEP OF A STRUCTURED PROOF borrows its parent rule's frame — its leading
    /// variables ARE the parent's (`ProgramClause::shared_arity`) — and is stored under
    /// the parent's name (`<rule>.<step>`), with no bound of its own: the bound is
    /// written on the parent's head. So a step's variable has the sort the parent's
    /// bound gives it, slot for slot. Without this a step about the carrier had a
    /// variable nothing gave a sort, and was refused.
    pub(crate) fn seed_parent_bounds(&mut self, step_qn: &str) -> Result<(), SmtGenError> {
        let Some((parent_qn, _)) = step_qn.rsplit_once('.') else {
            return Ok(());
        };
        // The step is synthesized in the frame of the parent's FIRST clause
        // (`rule_id_by_qn`), which is the one whose bounds its slots are.
        match self.kb.program_clauses_by_qn(parent_qn).first() {
            Some(parent) => self.seed_bounds(parent),
            None => Ok(()),
        }
    }

    /// THE SORT A DECLARED TYPE PARAMETER IS, for a variable bounded by it. In a proof's
    /// clause the parameter is an enclosing scope's own, and is its own sort. In a LAW's
    /// it is the SPEC's — `?a: T` written in `Spec` — and the law is lowered at a
    /// requirement, so it is what the requirement binds `Spec.T` to. Taken for a sort of
    /// its own there, the law was about a carrier no proof names: it constrained
    /// nothing, and counted as lowered.
    fn parameter_sort(&self, param: Symbol) -> Result<SmtSort, SmtGenError> {
        if self.lowering_law.is_none() {
            return Ok(SmtSort::Declared(
                self.kb.qualified_name_of(param).to_owned(),
            ));
        }
        self.param_defaults.get(&param).cloned().ok_or_else(|| {
            SmtGenError::new(format!(
                "the law bounds a variable by `{}`, which the requirement does not bind to \
                 one sort",
                self.kb.qualified_name_of(param)
            ))
        })
    }

    /// Give the variable named `name` the sort `sort`. `Ok(true)` when it had none.
    /// Two sorts for one variable are refused when either is a declared one; two theory
    /// sorts are left to the solver, which is where they were always found.
    fn set_var_sort(&mut self, name: &str, sort: &SmtSort) -> Result<bool, SmtGenError> {
        match self.var_sorts.get(name) {
            None => {
                self.var_sorts.insert(name.to_owned(), sort.clone());
                Ok(true)
            }
            Some(had) if had != sort && (had.is_declared() || sort.is_declared()) => Err(
                SmtGenError::new(format!("`?{name}` is used at two sorts: {had} and {sort}")),
            ),
            Some(_) => Ok(false),
        }
    }

    /// The sort of a term, where a bound, a signature or a literal says it.
    pub(crate) fn sort_of_occ(&self, occ: &Rc<NodeOccurrence>) -> Option<SmtSort> {
        match occ.as_expr()? {
            Expr::Const(Literal::Float(_)) | Expr::Const(Literal::Int(_)) => Some(SmtSort::Real),
            Expr::Const(Literal::Bool(_)) => Some(SmtSort::Bool),
            Expr::Const(_) => None,
            Expr::Var(var) => self.var_sorts.get(&self.var_name(var)?).cloned(),
            Expr::If {
                then_branch,
                else_branch,
                ..
            } => self
                .sort_of_occ(then_branch)
                .or_else(|| self.sort_of_occ(else_branch)),
            Expr::Ref(symbol) | Expr::Ident(symbol) => {
                let signature = self.signature(*symbol)?;
                if !signature.params.is_empty() {
                    return None;
                }
                match signature.result {
                    SigType::Fixed(sort) => Some(sort),
                    SigType::Param(param) => self.param_defaults.get(&param).cloned(),
                    SigType::Other => None,
                }
            }
            _ => {
                if self.as_field_access(occ).is_some() {
                    return self
                        .resolve_field_access(occ)
                        .ok()
                        .and_then(|field| self.sort_of_occ(&field));
                }
                let (functor, pos_args, named_args) = occ_as_fn(occ)?;
                if self.builtins.is_ite(functor) {
                    return pos_args
                        .get(1)
                        .and_then(|branch| self.sort_of_occ(branch))
                        .or_else(|| pos_args.get(2).and_then(|branch| self.sort_of_occ(branch)));
                }
                if self.is_eq_functor(functor)
                    || self.builtins.inequality(functor).is_some()
                    || self.builtins.bool_connective(functor).is_some()
                {
                    return Some(SmtSort::Bool);
                }
                let signature = self.signature(functor)?;
                match &signature.result {
                    SigType::Fixed(sort) => Some(sort.clone()),
                    SigType::Param(param) => self
                        .call_instance(functor, &signature, pos_args, named_args)
                        .ok()?
                        .get(param)
                        .cloned(),
                    SigType::Other => None,
                }
            }
        }
    }

    /// The sort of each type parameter of a call, as its OPERANDS say: every operand in
    /// a position typed by one parameter is of one sort.
    fn operand_instance(
        &self,
        functor: Symbol,
        signature: &Signature,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
    ) -> Result<Instance, SmtGenError> {
        let mut instance = Instance::new();
        for (index, (name, ty)) in signature.params.iter().enumerate() {
            let SigType::Param(param) = ty else { continue };
            let Some(sort) = argument(self.kb, index, *name, pos_args, named_args)
                .and_then(|arg| self.sort_of_occ(arg))
            else {
                continue;
            };
            match instance.get(param) {
                Some(had) if *had != sort && (had.is_declared() || sort.is_declared()) => {
                    return Err(SmtGenError::new(format!(
                        "the operands of `{}` are of two sorts, {had} and {sort}, where its \
                         signature has one type",
                        self.kb.qualified_name_of(functor)
                    )))
                }
                Some(_) => {}
                None => {
                    instance.insert(*param, sort);
                }
            }
        }
        Ok(instance)
    }

    /// [`Self::operand_instance`], and for a parameter no operand decides, what the law
    /// being lowered is at ([`Self::param_defaults`] — empty for a proof's own body).
    fn call_instance(
        &self,
        functor: Symbol,
        signature: &Signature,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
    ) -> Result<Instance, SmtGenError> {
        let mut instance = self.operand_instance(functor, signature, pos_args, named_args)?;
        for param in signature.type_params() {
            if let Some(default) = self.param_defaults.get(&param) {
                instance.entry(param).or_insert_with(|| default.clone());
            }
        }
        Ok(instance)
    }

    /// THE SORTS OF A CLAUSE'S VARIABLES, as far as its goals say them, to a fixed point —
    /// `gte(?a, ?b)` gives `?b` the sort of a bounded `?a` whichever goal is read first.
    /// Run before a goal is translated, because WHICH function an application is depends
    /// on its operands' sorts.
    ///
    /// A sort goes BOTH WAYS through an application. Up: the operands in the positions one
    /// type parameter types are of one sort, and that is the sort of a result so typed.
    /// Down: a position whose sort is known gives it to what stands there — a variable,
    /// and the result of a nested call, and so that call's own operands (`lt(?d + ?step,
    /// 3.0)`: the literal makes `add`'s result a `Real`, and `?d` and `?step` with it).
    /// A variable an entity's field binds has the field's declared type.
    ///
    /// The operands decide first; only where nothing more follows from them does a law
    /// take its requirement's bindings for a group no operand decided, and then the
    /// operands are read again.
    pub(crate) fn infer_var_sorts(
        &mut self,
        goals: &[Rc<NodeOccurrence>],
    ) -> Result<(), SmtGenError> {
        loop {
            let mut changed = false;
            for goal in goals {
                self.infer_in(goal, None, false, &mut changed)?;
            }
            if changed {
                continue;
            }
            if !self.param_defaults.is_empty() {
                for goal in goals {
                    self.infer_in(goal, None, true, &mut changed)?;
                }
            }
            if !changed {
                return Ok(());
            }
        }
    }

    /// One term of a clause, standing where `expected` is the sort — when the position
    /// has one.
    fn infer_in(
        &mut self,
        occ: &Rc<NodeOccurrence>,
        expected: Option<&SmtSort>,
        with_defaults: bool,
        changed: &mut bool,
    ) -> Result<(), SmtGenError> {
        if let (Some(sort), Some(Expr::Var(var))) = (expected, occ.as_expr()) {
            if let Some(name) = self.var_name(var) {
                *changed |= self.set_var_sort(&name, sort)?;
            }
            return Ok(());
        }
        if let Some(Expr::If {
            condition,
            then_branch,
            else_branch,
        }) = occ.as_expr()
        {
            self.infer_in(condition, None, with_defaults, changed)?;
            return self.infer_branches(then_branch, else_branch, expected, with_defaults, changed);
        }
        let Some((functor, pos_args, named_args)) = occ_as_fn(occ) else {
            return Ok(());
        };
        if self.builtins.is_ite(functor) {
            if let [condition, then_branch, else_branch] = pos_args {
                self.infer_in(condition, None, with_defaults, changed)?;
                return self.infer_branches(
                    then_branch,
                    else_branch,
                    expected,
                    with_defaults,
                    changed,
                );
            }
        }
        // An entity destructured (`Limits(max: ?m)`): each field's declared type.
        if let Some(fields) = self.kb.entity_field_types(functor) {
            let field_sorts: Vec<(Symbol, Option<SmtSort>)> = fields
                .iter()
                .map(|(field, ty)| (*field, self.type_sort(ty)))
                .collect();
            for (index, arg) in pos_args.iter().enumerate() {
                let sort = field_sorts.get(index).and_then(|(_, sort)| sort.clone());
                self.infer_in(arg, sort.as_ref(), with_defaults, changed)?;
            }
            for (key, arg) in named_args {
                let sort = field_sorts
                    .iter()
                    .find(|(field, _)| {
                        field == key || self.kb.local_name_of(*field) == self.kb.local_name_of(*key)
                    })
                    .and_then(|(_, sort)| sort.clone());
                self.infer_in(arg, sort.as_ref(), with_defaults, changed)?;
            }
            return Ok(());
        }
        let Some(signature) = self.signature(functor) else {
            // No declared types to read: a rule's predicate, a connective.
            for arg in pos_args.iter().chain(named_args.iter().map(|(_, arg)| arg)) {
                self.infer_in(arg, None, with_defaults, changed)?;
            }
            return Ok(());
        };
        let mut instance = if with_defaults {
            self.call_instance(functor, &signature, pos_args, named_args)?
        } else {
            self.operand_instance(functor, &signature, pos_args, named_args)?
        };
        self.result_decides(functor, &signature, expected, &mut instance)?;
        for (index, (name, ty)) in signature.params.iter().enumerate() {
            let Some(arg) = argument(self.kb, index, *name, pos_args, named_args) else {
                continue;
            };
            let sort = match ty {
                SigType::Param(param) => instance.get(param).cloned(),
                SigType::Fixed(sort) => Some(sort.clone()),
                SigType::Other => None,
            };
            self.infer_in(arg, sort.as_ref(), with_defaults, changed)?;
        }
        Ok(())
    }

    /// The branches of a conditional are of one sort: the one the conditional stands at,
    /// or the one either branch has.
    fn infer_branches(
        &mut self,
        then_branch: &Rc<NodeOccurrence>,
        else_branch: &Rc<NodeOccurrence>,
        expected: Option<&SmtSort>,
        with_defaults: bool,
        changed: &mut bool,
    ) -> Result<(), SmtGenError> {
        let sort = expected
            .cloned()
            .or_else(|| self.sort_of_occ(then_branch))
            .or_else(|| self.sort_of_occ(else_branch));
        self.infer_in(then_branch, sort.as_ref(), with_defaults, changed)?;
        self.infer_in(else_branch, sort.as_ref(), with_defaults, changed)
    }

    /// The position a call stands in says what its RESULT is, and so what the type
    /// parameter its result is typed by is, where no operand of the call said.
    fn result_decides(
        &self,
        functor: Symbol,
        signature: &Signature,
        expected: Option<&SmtSort>,
        instance: &mut Instance,
    ) -> Result<(), SmtGenError> {
        let (Some(sort), SigType::Param(param)) = (expected, &signature.result) else {
            return Ok(());
        };
        match instance.get(param) {
            None => {
                instance.insert(*param, sort.clone());
                Ok(())
            }
            Some(had) if had != sort && (had.is_declared() || sort.is_declared()) => {
                Err(SmtGenError::new(format!(
                    "`{}` is of sort {had} by its operands, and stands where a {sort} does",
                    self.kb.qualified_name_of(functor)
                )))
            }
            Some(_) => Ok(()),
        }
    }

    /// WHY AN OPERATION WITH NO ROW WAS NOT LOWERED, where the reason is its operands'
    /// sort and not the operation: where an unsorted variable is refused
    /// ([`Self::refusal_subject`]), a variable operand standing where the signature has a
    /// type parameter that nothing decided. `neq(?a, ?a)` with no bound on `?a` is then
    /// "nothing gives `?a` a sort", which is what the author can act on, and not
    /// "unhandled functor `neq`", which reads as if a bound would not help.
    pub(crate) fn unsorted_operand_refusal(
        &self,
        functor: Symbol,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
    ) -> Option<SmtGenError> {
        let of = self.refusal_subject()?;
        let signature = self.signature(functor)?;
        let instance = self
            .call_instance(functor, &signature, pos_args, named_args)
            .ok()?;
        signature
            .params
            .iter()
            .enumerate()
            .filter(
                |(_, (_, ty))| matches!(ty, SigType::Param(param) if !instance.contains_key(param)),
            )
            .filter_map(|(index, (name, _))| argument(self.kb, index, *name, pos_args, named_args))
            .find_map(|operand| match operand.as_expr() {
                Some(Expr::Var(var)) => self.var_name(var),
                _ => None,
            })
            .map(|variable| no_sort_refusal(&of, &variable, self.reading_step))
    }

    /// A SPEC'S OPERATION AT A DECLARED SORT IS AN UNINTERPRETED FUNCTION. `Ok(None)` for
    /// anything else, which is read as it always was — by its row, by its rule's body,
    /// or refused:
    ///
    ///   * a functor that is no operation, or an operation of no spec. A FREE operation's
    ///     body is its definition, and making the operation uninterpreted would drop it;
    ///     a spec's is a DEFAULT a carrier may replace, so at an abstract carrier the
    ///     operation is whatever the carrier has, and only the spec's laws say what;
    ///   * an operation whose operands are all of theory sorts;
    ///   * an application that is not of the signature's arity — the relational form of
    ///     a call, which a rule's body is read for.
    ///
    /// `expected` is the sort of the position the call stands in, when it is an operand
    /// of another: it decides a result no operand of the call does (`lub(top, bottom)`).
    ///
    /// The function is named by the operation and the carrier it is at
    /// (`anthill.prelude.PartialEq.eq@test.sg.Scope.T`), so the law that states it and
    /// the body that uses it name one function, and the same operation at another
    /// parameter is another.
    pub(crate) fn uninterpreted_call(
        &mut self,
        functor: Symbol,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
        expected: Option<&SmtSort>,
        bindings: &BTreeMap<String, String>,
    ) -> Result<Option<(String, SmtSort)>, SmtGenError> {
        if spec_op_parent_sort(self.kb, functor).is_none() {
            return Ok(None);
        }
        let Some(signature) = self.signature(functor) else {
            return Ok(None);
        };
        if pos_args.len() + named_args.len() != signature.params.len() {
            return Ok(None);
        }
        let mut instance = self.call_instance(functor, &signature, pos_args, named_args)?;
        self.result_decides(functor, &signature, expected, &mut instance)?;
        if !instance.values().any(SmtSort::is_declared) {
            return Ok(None);
        }
        let operation = self.kb.qualified_name_of(functor);
        let sort_of = |ty: &SigType, what: &str| match ty {
            SigType::Param(param) => instance.get(param).cloned().ok_or_else(|| {
                SmtGenError::new(format!(
                    "nothing gives {what} of `{operation}` a sort: its type is the \
                     parameter `{}`, which no operand of the call is of",
                    self.kb.qualified_name_of(*param)
                ))
            }),
            SigType::Fixed(sort) => Ok(sort.clone()),
            SigType::Other => Err(SmtGenError::new(format!(
                "{what} of `{operation}` is of a type with no SMT sort"
            ))),
        };
        let mut param_sorts = Vec::with_capacity(signature.params.len());
        for (name, ty) in &signature.params {
            param_sorts.push(sort_of(
                ty,
                &format!("the parameter `{}`", self.kb.local_name_of(*name)),
            )?);
        }
        let result = sort_of(&signature.result, "the result")?;
        let carriers: Vec<String> = signature
            .type_params()
            .iter()
            .filter_map(|param| instance.get(param))
            .map(|sort| match sort {
                SmtSort::Declared(name) => name.clone(),
                theory => theory.to_string(),
            })
            .collect();
        let name = format!("{operation}@{}", carriers.join("@"));

        let mut args = Vec::with_capacity(signature.params.len());
        for (index, ((param, _), sort)) in signature.params.iter().zip(&param_sorts).enumerate() {
            let arg = argument(self.kb, index, *param, pos_args, named_args).ok_or_else(|| {
                SmtGenError::new(format!(
                    "`{operation}` is applied without its parameter `{}`",
                    self.kb.local_name_of(*param)
                ))
            })?;
            args.push(self.translate_operand(arg, sort, bindings)?);
        }
        self.declarations
            .declare_fun(name.clone(), param_sorts, result.clone())?;
        let symbol = smt_symbol(&name);
        Ok(Some(if args.is_empty() {
            (symbol, result)
        } else {
            (format!("({symbol} {})", args.join(" ")), result)
        }))
    }

    /// One operand of an uninterpreted function, which is of `sort`.
    fn translate_operand(
        &mut self,
        operand: &Rc<NodeOccurrence>,
        sort: &SmtSort,
        bindings: &BTreeMap<String, String>,
    ) -> Result<String, SmtGenError> {
        // A nullary operation named bare — `top` in `lub(?a, top)` — as a HEAD's term
        // stores it: a `Ref`, which this position gives its sort.
        if let Some(Expr::Ref(symbol) | Expr::Ident(symbol)) = operand.as_expr() {
            if let Some(constant) = self.nullary_constant(*symbol, Some(sort))? {
                return Ok(constant);
            }
        }
        // A nested call, whose result this position decides where its operands do not —
        // and `top` as a BODY stores it is one, of no arguments.
        if let Some((functor, pos_args, named_args)) = occ_as_fn(operand) {
            if let Some((applied, found)) =
                self.uninterpreted_call(functor, pos_args, named_args, Some(sort), bindings)?
            {
                return if found == *sort {
                    Ok(applied)
                } else {
                    Err(SmtGenError::new(format!(
                        "an operand of sort {found} stands where the signature has {sort}"
                    )))
                };
            }
        }
        if let Some(found) = self.sort_of_occ(operand) {
            if found != *sort && (found.is_declared() || sort.is_declared()) {
                return Err(SmtGenError::new(format!(
                    "an operand of sort {found} stands where the signature has {sort}"
                )));
            }
        }
        self.translate_term(operand, bindings)
    }

    /// A NULLARY operation named bare (`zero`, `top`) at a declared sort: an
    /// uninterpreted constant. The sort is the one the position it stands in has, or —
    /// in a law — what the requirement binds the operation's parameter to. `Ok(None)`
    /// for a symbol that is no such operation, or one at a theory sort.
    pub(crate) fn nullary_constant(
        &mut self,
        symbol: Symbol,
        expected: Option<&SmtSort>,
    ) -> Result<Option<String>, SmtGenError> {
        let Some(signature) = self.signature(symbol) else {
            return Ok(None);
        };
        let SigType::Param(param) = signature.result else {
            return Ok(None);
        };
        if !signature.params.is_empty() {
            return Ok(None);
        }
        let Some(sort) = expected
            .or_else(|| self.param_defaults.get(&param))
            .cloned()
        else {
            return Ok(None);
        };
        let SmtSort::Declared(carrier) = &sort else {
            return Ok(None);
        };
        let name = format!("{}@{carrier}", self.kb.qualified_name_of(symbol));
        self.declarations
            .declare_fun(name.clone(), Vec::new(), sort.clone())?;
        Ok(Some(smt_symbol(&name)))
    }

    /// A term that is a formula or a value, by its shape: `(= lhs rhs)` holds either on
    /// each side.
    pub(crate) fn translate_term(
        &mut self,
        occ: &Rc<NodeOccurrence>,
        bindings: &BTreeMap<String, String>,
    ) -> Result<String, SmtGenError> {
        let formula = match occ.as_expr() {
            Some(Expr::Const(Literal::Bool(_))) => true,
            _ => occ_as_fn(occ).is_some_and(|(functor, _, _)| {
                self.is_eq_functor(functor)
                    || self.builtins.inequality(functor).is_some()
                    || self.builtins.bool_connective(functor).is_some()
            }),
        };
        if formula {
            self.translate_condition(occ, bindings)
        } else {
            self.translate_expr(occ, bindings)
        }
    }

    /// WHAT A LAW IS LOWERED AT: every type parameter the requirement's instance binds,
    /// and those of what its spec requires or provides in turn — `eq` in a law of `Eq`
    /// is the `eq` of the `PartialEq[T = T]` that `Eq` provides. A parameter bound to
    /// two sorts along two paths says nothing, and is left out; so is one whose binding
    /// has no SMT sort. A law that needed either is then not lowered, and said.
    fn seed_param_defaults(&mut self, instance: &RequirementInstance) {
        let mut contested: HashSet<Symbol> = HashSet::new();
        let mut pending = vec![instance];
        while let Some(at) = pending.pop() {
            for (param, ty) in &at.bindings {
                let Some(sort) = self.type_sort(ty) else {
                    continue;
                };
                if contested.contains(param) {
                    continue;
                }
                match self.param_defaults.get(param) {
                    Some(had) if *had != sort => {
                        self.param_defaults.remove(param);
                        contested.insert(*param);
                    }
                    Some(_) => {}
                    None => {
                        self.param_defaults.insert(*param, sort);
                    }
                }
            }
            pending.extend(at.in_turn.iter());
        }
    }

    /// A `constraint name: conclusion :- guard` written in a spec: stored as the inert
    /// fact `Constraint(head(conclusion…), guard(guard…))`, its variables the loader's
    /// own and not a frame's. The guard is the premise set and the head the conclusion.
    /// A denial (`constraint name :- goals`, no head) and a quantified constraint are
    /// other shapes, and are not read here.
    fn collect_constraint_law(&mut self, clause: &ProgramClause) -> Result<(), SmtGenError> {
        let unread = || {
            SmtGenError::new(
                "a constraint is lowered when it is `constraint name: conclusion :- guard`",
            )
        };
        let Value::Term { id, .. } = &clause.head else {
            return Err(unread());
        };
        let goals_under = |tid: TermId, wrapper: &str| match self.kb.get_term(tid) {
            Term::Fn {
                functor,
                pos_args,
                named_args,
            } if named_args.is_empty() && self.kb.local_name_of(*functor) == wrapper => {
                Some(pos_args.to_vec())
            }
            _ => None,
        };
        let Term::Fn { pos_args, .. } = self.kb.get_term(*id) else {
            return Err(unread());
        };
        let [head, guard] = pos_args.as_slice() else {
            return Err(unread());
        };
        let (Some(conclusions), Some(premises)) =
            (goals_under(*head, "head"), goals_under(*guard, "guard"))
        else {
            return Err(unread());
        };
        for goal in premises.iter().chain(&conclusions) {
            self.name_global_vars(*goal);
        }
        let materialize = |goals: &[TermId]| -> Vec<Rc<NodeOccurrence>> {
            goals
                .iter()
                .map(|goal| materialize_from_handle(self.kb, *goal))
                .collect()
        };
        let premises = materialize(&premises);
        let conclusions = materialize(&conclusions);
        let all: Vec<Rc<NodeOccurrence>> = premises.iter().chain(&conclusions).cloned().collect();
        self.infer_var_sorts(&all)?;
        let mut bindings = BTreeMap::new();
        for goal in &premises {
            self.process_body_goal(goal, &mut bindings)?;
        }
        let stated = self.assertions.len();
        for goal in &conclusions {
            self.process_body_goal(goal, &mut bindings)?;
        }
        self.conclusion_assertions = self.assertions.split_off(stated);
        self.note_free_vars(&bindings)
    }

    /// Name the variables of a stored fact's term, which are no frame's: `var_0`, … in
    /// the order they are first met.
    fn name_global_vars(&mut self, tid: TermId) {
        match self.kb.get_term(tid) {
            Term::Var(Var::Global(vid)) => {
                if !self.global_names.iter().any(|(named, _)| named == vid) {
                    let name = synthetic_var_name(self.global_names.len() as u32);
                    self.global_names.push((*vid, name));
                }
            }
            Term::Fn {
                pos_args,
                named_args,
                ..
            } => {
                let children: Vec<TermId> = pos_args
                    .iter()
                    .copied()
                    .chain(named_args.iter().map(|(_, arg)| *arg))
                    .collect();
                for child in children {
                    self.name_global_vars(child);
                }
            }
            _ => {}
        }
    }
}

fn same_var(a: &Var, b: &Var) -> bool {
    match (a, b) {
        (Var::DeBruijn(x), Var::DeBruijn(y)) => x == y,
        (Var::Global(x), Var::Global(y)) => x == y,
        _ => false,
    }
}
