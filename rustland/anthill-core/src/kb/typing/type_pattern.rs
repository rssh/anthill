//! Type patterns (proposal 071 §1.1, §1.5): whether a type is admitted by a type that may
//! have open slots. The one subtype test `TypePattern.admits` runs, through the reflect
//! operation `type_admits` (`stdlib/anthill/reflect/reflect.anthill`).
//!
//! A pattern `P` admits `t` when `t` is a subtype of an instance of `P`. An open slot — an
//! argument left out — on either side admits every type, so the question is one relation,
//! [`below`] — `a` is a subtype of an instance of `b` — and the pattern's question is
//! `below(t, P)`.
//!
//! NOMINAL ON THE HEAD, BY VARIANCE ON THE ARGUMENTS. A sort is below what
//! [`sort_sym_compatible`] climbs to: itself, an entity's own sort, and what it refines
//! through `requires`. Two applications of one sort compare each argument by the declared
//! variance of its parameter ([`declared_variances`]): covariant, below; contravariant,
//! above; both, either; no fact, equal ([`equal`]). A variant's arguments are its sort's
//! ([`KnowledgeBase::type_arg_owner`]): two applications of one variant compare as the
//! sort's do, and a variant is below its own sort at the same arguments. An arrow is the
//! `Function` it is (`kernel-language.md` §4.4: `(A) -> B` is `Function[A, B, E = {}]`), and
//! is compared as that application ([`arrow_as_function`]). The provider leg the typer's
//! `bare_sort_compatible` adds (`List` where `Stream` is expected) is not one of them: the
//! run-time boundary never read it (`payload_matches` was `sort_sym_compatible` on the head
//! until WI-20261016-YM8HD made the boundary ask `TypePattern.admits`, which runs this
//! test).
//!
//! ONE WALK FOR THE RUN AND FOR THE TYPER'S DISCHARGE (071 §1.5). The typer discharges an
//! `Error` label at a boundary where the pattern admits its payload ([`pattern_discharges`]),
//! the run's question asked of a type the typer knows less of: a slot the payload leaves out,
//! or holds a type pattern's open slot, is the type of a value that stands there, admitted only
//! by a pattern open at that slot; and a rigid is one type, admitted by itself. A raised type
//! has neither, so the two answer alike on every type a raise carries. A type pattern's OPEN
//! SLOT ([`KnowledgeBase::pattern_slot`]) admits every type on the pattern's side, at any
//! depth and as the whole pattern `?`, and is a type not known on the side asked about — the
//! run asks about a raise of the unknown type so.
//!
//! PURE, OVER AN IMMUTABLE KB, AND BOUNDED. No substitution and no `&mut`: the run time
//! calls it from a builtin, and the typer's discharge from a site already deep in the
//! expression walk, where a full `types_compatible` descent once overflowed the stack — see
//! [`labels_match_by_subsumption`]. The recursion follows the two type terms and nothing
//! else, and stops at [`NESTING_LIMIT`] (MEASURED: two types nested 5 500 deep overflowed
//! the stack of the debug build with no bound).
//!
//! A SORT THAT REFINES ANOTHER THROUGH `requires` IS EACH INSTANCE OF IT ITS CLAUSES GIVE IT
//! ([`instances_through_requires`]): `sort Narrow requires Wide[W = Int64]` is admitted by a
//! pattern at `Wide[W = Int64]` and not by one at `Wide[W = String]`, its own arguments put
//! for the parameters a clause names.
//!
//! WHAT IT DOES NOT JUDGE IS AN ERROR ([`UnjudgedType`]), never an answer: two named tuples,
//! two effect rows that are not one row, an effect row beside anything else, a type
//! variable, a polymorphic type, a type read off a value, and a data value standing where a
//! type is asked for. [`form`] is the list. The pattern `TypePattern`'s one row answers
//! (`TypeValuePattern`'s, at a type with a `TypeValue`) holds none of them, a former having
//! no `TypeValue` instance and a sort holding one among its arguments none either.
//!
//! AN ANSWER DECIDED BY ONE ARGUMENT IS NOT UNDONE BY ANOTHER THAT IS NOT JUDGED: an
//! argument that is not below its pattern makes the whole `false`, whatever the others
//! are, and one direction of a bivariant parameter that holds makes it `true`. An error
//! is the answer only where nothing decided it, so the verdict does not follow the order a
//! sort declares its parameters in.

use super::*;

/// How deep the walk descends into two types — and into one, to tell a type from a data
/// value. Deeper, the pair is not judged ([`UnjudgedType::TooDeep`]).
const NESTING_LIMIT: usize = 512;

/// [`NESTING_LIMIT`], for a walk beside this one over the same two types (a boundary's pattern
/// read at its variables, `slots::read_at_variables`).
pub(super) const TYPE_NESTING_LIMIT: usize = NESTING_LIMIT;

/// A pair of types [`type_pattern_admits`] does not judge, and why — its caller reports it
/// as an error, rendered by [`Self::detail`]. It holds the values rather than their text:
/// the walk keeps the first of several and drops it where another argument decides
/// ([`arguments_relate`], [`either`]), so most are never shown.
#[derive(Clone, Debug)]
pub(crate) enum UnjudgedType {
    /// `value` is no form the walk compares; `what` is which.
    Form { value: Value, what: &'static str },
    /// Two named tuples.
    TwoTuples { a: Value, b: Value },
    /// Two effect rows that are not one row.
    TwoRows { a: Value, b: Value },
    /// `pattern` writes `param` of `sort`, which `t` refines with no `requires` clause naming
    /// it to read the argument from.
    AcrossRequires {
        pattern: Value,
        t: Value,
        param: Symbol,
        sort: Symbol,
    },
    /// The two types nest deeper than [`NESTING_LIMIT`].
    TooDeep,
}

impl UnjudgedType {
    pub(crate) fn detail(&self, kb: &KnowledgeBase) -> String {
        match self {
            UnjudgedType::Form { value, what } => format!(
                "`{}` is {what}, and a type pattern is judged over sorts, their applications \
                 and `Nothing`",
                type_display_name_value(kb, value)
            ),
            UnjudgedType::TwoTuples { a, b } => format!(
                "`{}` and `{}` are both named tuples, and a type pattern does not compare two \
                 of them",
                type_display_name_value(kb, a),
                type_display_name_value(kb, b)
            ),
            UnjudgedType::TwoRows { a, b } => format!(
                "`{}` and `{}` are two effect rows, and a type pattern compares a row only with \
                 the same row",
                type_display_name_value(kb, a),
                type_display_name_value(kb, b)
            ),
            UnjudgedType::AcrossRequires {
                pattern,
                t,
                param,
                sort,
            } => format!(
                "the pattern `{}` writes `{}` of `{}`, which `{}` refines with no `requires` \
                 clause naming it, so no argument for it is read",
                type_display_name_value(kb, pattern),
                kb.local_name_of(*param),
                kb.local_name_of(*sort),
                type_display_name_value(kb, t),
            ),
            UnjudgedType::TooDeep => format!(
                "the two types nest deeper than {NESTING_LIMIT} levels, and a type pattern is \
                 not judged deeper"
            ),
        }
    }
}

/// Whether the type `pattern` admits the type `t`: whether `t` is a subtype of an
/// instance of `pattern`, an open slot on either side admitting every type. See the
/// module header.
pub(crate) fn type_pattern_admits<P: TermView, T: TermView>(
    kb: &KnowledgeBase,
    pattern: &P,
    t: &T,
) -> Result<bool, UnjudgedType> {
    below(kb, t, pattern, Mode::RUN, 0)
}

/// Does a boundary whose pattern is `pattern` discharge an `Error` label whose payload is
/// `payload` (071 §1.5)? The run's question, asked of a type the typer knows less of: a slot
/// the payload leaves open, or holds a type not known, is the type of a value that stands
/// there, and only a pattern open at that slot admits it whatever it is. A type the run
/// asks about is a raised type, which has neither, so the two answer alike on every type a
/// raise carries. A rigid is one type, the same rigid on both sides admitting; a pair the
/// test does not judge is not discharged, and the label stays in the caller's row.
pub(crate) fn pattern_discharges<P: TermView, T: TermView>(
    kb: &KnowledgeBase,
    pattern: &P,
    payload: &T,
) -> bool {
    below(kb, payload, pattern, Mode::DISCHARGE, 0).unwrap_or(false)
}

/// Who asks [`below`] and [`equal`], and which of their two sides is the pattern.
#[derive(Clone, Copy)]
struct Mode {
    /// The typer's discharge ([`pattern_discharges`]), not the run ([`type_pattern_admits`]).
    discharge: bool,
    /// The pattern is the first side: a contravariant argument turns the question round.
    flipped: bool,
}

impl Mode {
    const RUN: Mode = Mode {
        discharge: false,
        flipped: false,
    };
    const DISCHARGE: Mode = Mode {
        discharge: true,
        flipped: false,
    };

    fn flip(self) -> Mode {
        Mode {
            flipped: !self.flipped,
            ..self
        }
    }

    /// The answer an open slot on a side gives, where one decides: a pattern's admits every
    /// type; a type pattern's open slot ([`MintedParam::PatternSlot`]) on the side asked
    /// about is a type not known, which no pattern admits but an open one; an argument the
    /// side asked about leaves out admits at run time (the reflect operation's rule, decided
    /// 2026-10-20) and is a type not known to the discharge. `a_open`/`b_open` say which
    /// side is open, `left_out` whether as an argument left out rather than a slot.
    fn open(self, a_open: bool, b_open: bool, left_out: bool) -> Option<bool> {
        let (pattern_open, asked_open) = if self.flipped {
            (a_open, b_open)
        } else {
            (b_open, a_open)
        };
        if pattern_open {
            Some(true)
        } else if asked_open {
            Some(left_out && !self.discharge)
        } else {
            None
        }
    }
}

/// Is `v` a type pattern's open slot ([`KnowledgeBase::pattern_slot`])?
pub(crate) fn is_pattern_slot<V: TermView>(kb: &KnowledgeBase, v: &V) -> bool {
    matches!(type_head(kb, v), TypeHead::Skolem(vid) if kb.is_pattern_slot(vid))
}

/// Is `v` a type the call states in full, its type patterns' open slots counted as stated: no
/// variable, no parameter, and no rigid but a pattern's open slot?
pub(crate) fn stated_but_pattern_slots(kb: &KnowledgeBase, v: &Value) -> bool {
    fn other_rigid<V: TermView>(kb: &KnowledgeBase, v: &V, depth: usize) -> bool {
        match v.head(kb) {
            ViewHead::Var(Var::Rigid(vid)) => !kb.is_pattern_slot(vid),
            ViewHead::Functor { pos_arity, .. } if depth <= NESTING_LIMIT => {
                view_any_child(kb, v, pos_arity, |c| other_rigid(kb, c, depth + 1))
            }
            _ => false,
        }
    }
    type_is_determined(kb, v) && !other_rigid(kb, v, 0)
}

/// [`below`] and [`equal`]'s first questions: an open slot on either side
/// ([`Mode::open`]), and, for the discharge, one type on both.
fn decided_before_forms<A: TermView, B: TermView>(
    kb: &KnowledgeBase,
    a: &A,
    b: &B,
    mode: Mode,
) -> Option<bool> {
    if let Some(answer) = mode.open(is_pattern_slot(kb, a), is_pattern_slot(kb, b), false) {
        return Some(answer);
    }
    (mode.discharge && views_structurally_equal(kb, a, b)).then_some(true)
}

/// Proposal 071 §1.6, §7 Q1 (decided with the user 2026-10-27) — the LEAST PATTERN that
/// admits both `a` and `b`, two types a boundary's argument raises at: the one type where
/// they are one; one sort's application where both are of that sort, an argument the two
/// disagree on open where its parameter is invariant and their least pattern where it is
/// covariant; and the wider sort where one refines the other through `requires`, the
/// narrower read as the instance its clause gives it. `None` where no one sort heads them —
/// two sorts neither refines, a tuple or an arrow beside another type. An argument a side
/// leaves out is a type not known, and the pattern is open there.
pub(crate) fn least_pattern(kb: &mut KnowledgeBase, a: &Value, b: &Value) -> Option<Value> {
    least_pattern_at(kb, a, b, 0)
}

fn least_pattern_at(kb: &mut KnowledgeBase, a: &Value, b: &Value, depth: usize) -> Option<Value> {
    if depth > NESTING_LIMIT {
        return None;
    }
    if is_pattern_slot(kb, a) || views_structurally_equal(kb, a, b) {
        return Some(a.clone());
    }
    if is_pattern_slot(kb, b) {
        return Some(b.clone());
    }
    match (type_head(kb, a), type_head(kb, b)) {
        (TypeHead::Nothing, _) => return Some(b.clone()),
        (_, TypeHead::Nothing) => return Some(a.clone()),
        _ => {}
    }
    let (sa, sb) = (sort_head(kb, a)?, sort_head(kb, b)?);
    let (oa, ob) = (
        kb.type_arg_owner(sa).unwrap_or(sa),
        kb.type_arg_owner(sb).unwrap_or(sb),
    );
    if same_sort_canonical(kb, oa, ob) {
        let head = if same_sort_canonical(kb, sa, sb) { sa } else { oa };
        return Some(joined_application(kb, a, b, head, oa, depth));
    }
    if sort_sym_compatible(kb, oa, ob) {
        let a = instance_at(kb, a, sa, ob, depth)?;
        return least_pattern_at(kb, &a, b, depth + 1);
    }
    if sort_sym_compatible(kb, ob, oa) {
        let b = instance_at(kb, b, sb, oa, depth)?;
        return least_pattern_at(kb, a, &b, depth + 1);
    }
    None
}

/// The head of a sort-headed type: a sort reference or an application of one.
fn sort_head<V: TermView>(kb: &KnowledgeBase, v: &V) -> Option<Symbol> {
    match type_head(kb, v) {
        TypeHead::SortRef(s) | TypeHead::Parameterized { base: s } => Some(s),
        _ => None,
    }
}

/// `v` as an instance of the sort `target`: itself where it is one of `target`'s, the one
/// instance its `requires` clauses give it where its sort refines `target`; `None` otherwise.
pub(crate) fn instance_of_sort(kb: &KnowledgeBase, v: &Value, target: Symbol) -> Option<Value> {
    let head = sort_head(kb, v)?;
    let owner = kb.type_arg_owner(head).unwrap_or(head);
    let target = kb.type_arg_owner(target).unwrap_or(target);
    if same_sort_canonical(kb, owner, target) {
        return Some(v.clone());
    }
    instance_at(kb, v, head, target, 0)
}

/// `v`, headed by `head`, as the one instance of `target` its `requires` clauses give it
/// ([`instances_through_requires`]); `None` where they give none or several.
fn instance_at(kb: &KnowledgeBase, v: &Value, head: Symbol, target: Symbol, depth: usize) -> Option<Value> {
    let mut instances = instances_through_requires(kb, v, head, target, depth).ok()?;
    (instances.len() == 1).then(|| instances.swap_remove(0))
}

/// `head` applied at each parameter of `owner` to what [`least_pattern`] makes of `a`'s and
/// `b`'s arguments there ([`least_pattern`]'s argument rule), every slot no default fills
/// written ([`fill_open_slots`]).
fn joined_application(
    kb: &mut KnowledgeBase,
    a: &Value,
    b: &Value,
    head: Symbol,
    owner: Symbol,
    depth: usize,
) -> Value {
    let params: SmallVec<[Symbol; 4]> = kb.type_param_syms_of(owner).iter().copied().collect();
    let variances = declared_variances(kb, owner, &params);
    let (a_args, b_args) = (arguments(kb, a), arguments(kb, b));
    let mut bindings: Vec<(Symbol, Value)> = Vec::with_capacity(params.len());
    for (&param, variance) in params.iter().zip(variances) {
        let av = binding_for_param(kb, &a_args, param, BindingKeyMatch::Label).cloned();
        let bv = binding_for_param(kb, &b_args, param, BindingKeyMatch::Label).cloned();
        let value = match (av, bv) {
            (None, None) if slot_left_out(kb, owner, param) => continue,
            (Some(x), Some(y)) if views_structurally_equal(kb, &x, &y) => fill_open_slots(kb, &x),
            (Some(x), Some(y)) if matches!(variance, Variance::Covariant) => {
                match least_pattern_at(kb, &x, &y, depth + 1) {
                    Some(joined) => fill_open_slots(kb, &joined),
                    None => Value::term(kb.pattern_slot()),
                }
            }
            _ => Value::term(kb.pattern_slot()),
        };
        let key = kb.intern(kb.local_name_of(param).to_owned().as_str());
        bindings.push((key, value));
    }
    let (span, site) = site_of(a);
    let base = kb.make_sort_ref(head);
    parameterized_value(kb, base, &bindings, span, site)
}

/// Is a parameter of `owner` that an application leaves out the slot's own value rather
/// than a type not known: one that declares a default, which the slot then holds, and an
/// effect row's, which a pattern does not judge?
fn slot_left_out(kb: &mut KnowledgeBase, owner: Symbol, param: Symbol) -> bool {
    kb.sort_param_defaults.contains_key(&param) || sort_param_sym_is_effect_row(kb, owner, param)
}

/// `v` with each slot it leaves out a type pattern's open slot ([`KnowledgeBase::pattern_slot`]),
/// at every depth: a slot no default fills, of a type a boundary's pattern is read from — a
/// slot left out is a type not known, which only an open pattern admits. `v` itself where it
/// leaves none out.
pub(crate) fn fill_open_slots(kb: &mut KnowledgeBase, v: &Value) -> Value {
    fill_open_slots_at(kb, v, 0)
}

fn fill_open_slots_at(kb: &mut KnowledgeBase, v: &Value, depth: usize) -> Value {
    let Some(head) = sort_head(kb, v).filter(|_| depth <= NESTING_LIMIT) else {
        return v.clone();
    };
    let owner = kb.type_arg_owner(head).unwrap_or(head);
    let params: SmallVec<[Symbol; 4]> = kb.type_param_syms_of(owner).iter().copied().collect();
    if params.is_empty() {
        return v.clone();
    }
    let args = arguments(kb, v);
    let mut changed = false;
    let mut bindings: Vec<(Symbol, Value)> = Vec::with_capacity(params.len());
    for &param in &params {
        let value = match binding_for_param(kb, &args, param, BindingKeyMatch::Label).cloned() {
            Some(arg) => {
                let filled = fill_open_slots_at(kb, &arg, depth + 1);
                changed |= !views_structurally_equal(kb, &filled, &arg);
                filled
            }
            None if slot_left_out(kb, owner, param) => continue,
            None => {
                changed = true;
                Value::term(kb.pattern_slot())
            }
        };
        let key = kb.intern(kb.local_name_of(param).to_owned().as_str());
        bindings.push((key, value));
    }
    if !changed {
        return v.clone();
    }
    let (span, site) = site_of(v);
    let base = kb.make_sort_ref(head);
    parameterized_value(kb, base, &bindings, span, site)
}

/// What [`below`] and [`equal`] read of one side, by [`type_head`]. An open slot is an
/// argument left out, so it is read where the arguments are paired ([`arguments_relate`])
/// and is no form of its own.
enum Form {
    /// The bottom type.
    Bottom,
    /// A sort reference, an application of one, or a variant's: its head, and the sort whose
    /// parameters its arguments bind.
    Sort { head: Symbol, owner: Symbol },
    /// A named tuple.
    Tuple,
    /// An arrow, as the `Function` application it is ([`arrow_as_function`]).
    Arrow(Value),
}

/// The form of one side, or why it is not judged — the one list of what is not.
fn form<V: TermView>(kb: &KnowledgeBase, v: &V, depth: usize) -> Result<Form, UnjudgedType> {
    let what = match type_head(kb, v) {
        TypeHead::Nothing => return Ok(Form::Bottom),
        TypeHead::SortRef(head) | TypeHead::Parameterized { base: head } => {
            match type_application_owner(kb, v, head, depth)? {
                Some(owner) => return Ok(Form::Sort { head, owner }),
                None => "a data value, not a type",
            }
        }
        TypeHead::NamedTuple => return Ok(Form::Tuple),
        TypeHead::Arrow => match arrow_as_function(kb, v) {
            Some(function) => return Ok(Form::Arrow(function)),
            None => "an arrow whose parts are not read",
        },
        TypeHead::EffectsRows => "an effect row",
        TypeHead::TypeVar(_) | TypeHead::Skolem(_) | TypeHead::FlexVar(_) => "a type variable",
        TypeHead::PolyType => "a polymorphic type",
        TypeHead::Denoted | TypeHead::ExprCarried | TypeHead::RigidProjection => {
            "a type read off a value"
        }
        TypeHead::Error => "not a type",
    };
    Err(UnjudgedType::Form {
        value: value_of(v),
        what,
    })
}

/// The sort whose parameters a sort-headed term's arguments bind, when the term is a type:
/// its head is a sort or a variant of one, every argument it writes is keyed by a type
/// parameter of that sort, and no argument is a data value ([`is_data`]). `None` for a
/// data value read where a type is asked for — `boom(reason: "s")`, a free-standing
/// entity's `Point(x: 3)`, a rule body's tuple literal `TupleLiteral(..)`, and `crate(V:
/// 3)` of `sort Crate { sort V = ?  entity crate(V: V) }`, whose field is keyed like the
/// parameter and holds a number.
fn type_application_owner<V: TermView>(
    kb: &KnowledgeBase,
    v: &V,
    head: Symbol,
    depth: usize,
) -> Result<Option<Symbol>, UnjudgedType> {
    if depth > NESTING_LIMIT {
        return Err(UnjudgedType::TooDeep);
    }
    let Some(owner) = kb.type_arg_owner(head) else {
        return Ok(None);
    };
    let params = kb.type_param_syms_of(owner);
    for (key, arg) in arguments(kb, v) {
        if !params.iter().any(|&p| p == key || same_label(kb, key, p)) || is_data(kb, &arg, depth)? {
            return Ok(None);
        }
    }
    Ok(Some(owner))
}

/// An argument that is a data value, not a type: a literal, or a sort-headed term that is no
/// type ([`type_application_owner`]). Every other form an argument takes — a type read off
/// a value (a value parameter's), an effect row, a type variable, a tuple or an arrow — is
/// a type's, and is judged where it is compared.
fn is_data<V: TermView>(kb: &KnowledgeBase, v: &V, depth: usize) -> Result<bool, UnjudgedType> {
    Ok(match type_head(kb, v) {
        TypeHead::Error => true,
        TypeHead::SortRef(head) | TypeHead::Parameterized { base: head } => {
            type_application_owner(kb, v, head, depth + 1)?.is_none()
        }
        _ => false,
    })
}

/// An arrow as the `Function` application it is: its parameter's type — the tuple of its
/// parameters where it takes more than one — at `A`, its result at `B`, its effect row at
/// `E`, keyed by `Function`'s own parameters. `None` where the arrow's parts are not read.
fn arrow_as_function<V: TermView>(kb: &KnowledgeBase, v: &V) -> Option<Value> {
    let TypeExtractor::Arrow {
        param,
        result,
        effects,
        ..
    } = extract_type(kb, v)
    else {
        return None;
    };
    let function = kb.try_resolve_symbol(FUNCTION_SPEC_QNAME)?;
    let named: Vec<(Symbol, Value)> = kb
        .type_param_syms_of(function)
        .iter()
        .map(|&p| {
            let part = match kb.local_name_of(p) {
                "A" => param.clone(),
                "B" => result.clone(),
                "E" => effects.clone(),
                _ => return None,
            };
            Some((p, part))
        })
        .collect::<Option<_>>()?;
    Some(Value::Entity {
        functor: function,
        pos: Rc::from(Vec::new()),
        named: named.into(),
    })
}

/// `a` is a subtype of an instance of `b`, an open slot on either side admitting every
/// type.
fn below<A: TermView, B: TermView>(
    kb: &KnowledgeBase,
    a: &A,
    b: &B,
    mode: Mode,
    depth: usize,
) -> Result<bool, UnjudgedType> {
    if depth > NESTING_LIMIT {
        return Err(UnjudgedType::TooDeep);
    }
    if let Some(answer) = decided_before_forms(kb, a, b, mode) {
        return Ok(answer);
    }
    if let Some(same) = two_rows(kb, a, b) {
        return same;
    }
    match (form(kb, a, depth)?, form(kb, b, depth)?) {
        (Form::Bottom, _) => Ok(true),
        (_, Form::Bottom) => Ok(false),
        (Form::Arrow(fa), Form::Arrow(fb)) => below(kb, &fa, &fb, mode, depth + 1),
        (Form::Arrow(fa), _) => below(kb, &fa, b, mode, depth + 1),
        (_, Form::Arrow(fb)) => below(kb, a, &fb, mode, depth + 1),
        (Form::Sort { head: sa, .. }, Form::Sort { head: sb, owner }) => {
            sort_below(kb, a, sa, b, sb, owner, mode, depth)
        }
        (Form::Tuple, Form::Tuple) => Err(UnjudgedType::TwoTuples {
            a: value_of(a),
            b: value_of(b),
        }),
        // Nominal: a sort is no tuple, and no tuple is a sort.
        (Form::Sort { .. }, Form::Tuple) | (Form::Tuple, Form::Sort { .. }) => Ok(false),
    }
}

/// Where both sides are effect rows: one row is admitted by itself, and any other pair is
/// not judged. `None` where they are not two rows.
///
/// THE EMPTY ROW HAS TWO SPELLINGS beside a row: `{}` as written, and `Nothing`, where a
/// `TypeValue` reports it — `Function[A = Int64, B = Int64, E = {}]`'s instance answers
/// `Function(A: Int64, B: Int64, E: Nothing)` (MEASURED), and a pattern read through
/// `TypePattern`'s row is that answer.
fn two_rows<A: TermView, B: TermView>(
    kb: &KnowledgeBase,
    a: &A,
    b: &B,
) -> Option<Result<bool, UnjudgedType>> {
    let same = match (type_head(kb, a), type_head(kb, b)) {
        (TypeHead::EffectsRows, TypeHead::EffectsRows) => views_structurally_equal(kb, a, b),
        (TypeHead::EffectsRows, TypeHead::Nothing) => is_empty_row(kb, a),
        (TypeHead::Nothing, TypeHead::EffectsRows) => is_empty_row(kb, b),
        _ => return None,
    };
    Some(if same {
        Ok(true)
    } else {
        Err(UnjudgedType::TwoRows {
            a: value_of(a),
            b: value_of(b),
        })
    })
}

/// The empty effect row, `{}`.
fn is_empty_row<V: TermView>(kb: &KnowledgeBase, v: &V) -> bool {
    let TypeExtractor::EffectsRows(expression) = extract_type(kb, v) else {
        return false;
    };
    matches!(
        expression.head(kb),
        ViewHead::Functor { functor: f, .. }
            if kb.qualified_name_of(f) == "anthill.prelude.EffectExpression.empty_row"
    )
}

/// [`below`] for two sort-headed types; `owner` is the sort whose parameters `b`'s arguments
/// bind.
#[allow(clippy::too_many_arguments)]
fn sort_below<A: TermView, B: TermView>(
    kb: &KnowledgeBase,
    a: &A,
    sa: Symbol,
    b: &B,
    sb: Symbol,
    owner: Symbol,
    mode: Mode,
    depth: usize,
) -> Result<bool, UnjudgedType> {
    // One sort, or a variant of `b`'s sort, which is that sort at the same arguments
    // (`kernel-language.md` §8.2): a value typed `Option.some[T = Cat]` is an `Option[T =
    // Cat]`.
    if same_sort_canonical(kb, sa, sb)
        || kb
            .type_arg_owner(sa)
            .is_some_and(|sort| same_sort_canonical(kb, sort, sb))
    {
        return arguments_relate(kb, a, b, owner, Relation::Below, mode, depth);
    }
    if !sort_sym_compatible(kb, sa, sb) {
        return Ok(false);
    }
    // `sa` refines `sb` through `requires`: `a` is each instance of `sb` its clauses give it,
    // and is admitted where one of them is.
    let instances = instances_through_requires(kb, a, sa, sb, depth)?;
    if instances.is_empty() {
        return match arguments(kb, b).first() {
            None => Ok(true),
            Some((param, _)) => Err(UnjudgedType::AcrossRequires {
                pattern: value_of(b),
                t: value_of(a),
                param: *param,
                sort: sb,
            }),
        };
    }
    let mut unjudged: Option<UnjudgedType> = None;
    for instance in &instances {
        match arguments_relate(kb, instance, b, owner, Relation::Below, mode, depth + 1) {
            Ok(true) => return Ok(true),
            Ok(false) => {}
            Err(e) => {
                unjudged.get_or_insert(e);
            }
        }
    }
    unjudged.map_or(Ok(false), Err)
}

/// The instances of `sb` the `requires` clauses give `a`, whose head `sa` refines `sb`, with
/// `a`'s own arguments put for the parameters a clause names: `sort Narrow requires Wide[W =
/// Int64]` gives `Narrow` the instance `Wide[W = Int64]`, and `sort Narrow2 { sort Q = ?
/// requires Wide[W = Q] }` gives `Narrow2[Q = String]` the instance `Wide[W = String]`. A
/// parameter `a` leaves out is left out of the instance too, an open slot. Every path of
/// clauses to `sb`, one instance per path.
fn instances_through_requires<A: TermView>(
    kb: &KnowledgeBase,
    a: &A,
    sa: Symbol,
    sb: Symbol,
    depth: usize,
) -> Result<Vec<Value>, UnjudgedType> {
    let sort = kb.type_arg_owner(sa).unwrap_or(sa);
    let a_args = arguments(kb, a);
    let sigma: Vec<(Symbol, Value)> = kb
        .type_param_syms_of(sort)
        .iter()
        .filter_map(|&p| {
            binding_for_param(kb, &a_args, p, BindingKeyMatch::Label).map(|v| (p, v.clone()))
        })
        .collect();
    let mut instances = Vec::new();
    instances_below(kb, sort, &sigma, sb, depth, &mut instances)?;
    Ok(instances)
}

/// [`instances_through_requires`] from `sort`, whose parameters `sigma` binds.
fn instances_below(
    kb: &KnowledgeBase,
    sort: Symbol,
    sigma: &[(Symbol, Value)],
    target: Symbol,
    depth: usize,
    instances: &mut Vec<Value>,
) -> Result<(), UnjudgedType> {
    if depth > NESTING_LIMIT {
        return Err(UnjudgedType::TooDeep);
    }
    let params = kb.type_param_syms_of(sort);
    for entry in direct_requires(kb, sort) {
        let required = entry.required_sort;
        if !sort_sym_compatible(kb, required, target) {
            continue;
        }
        let Some((_, bindings)) = unwrap_spec_view_value(kb, &entry.spec) else {
            continue;
        };
        let named: Vec<(Symbol, Value)> = bindings
            .iter()
            .filter_map(|(key, v)| substituted(kb, v, params, sigma).map(|v| (*key, v)))
            .collect();
        if same_sort_canonical(kb, required, target) {
            instances.push(Value::Entity {
                functor: required,
                pos: Rc::from(Vec::new()),
                named: named.into(),
            });
        } else {
            let next: Vec<(Symbol, Value)> = kb
                .type_param_syms_of(required)
                .iter()
                .filter_map(|&p| {
                    binding_for_param(kb, &named, p, BindingKeyMatch::Label).map(|v| (p, v.clone()))
                })
                .collect();
            instances_below(kb, required, &next, target, depth + 1, instances)?;
        }
    }
    Ok(())
}

/// `v`, a binding a `requires` clause of a sort with the parameters `params` writes, with
/// `sigma` put for each parameter it names; `None` where it names one `sigma` leaves out — an
/// open slot. A parameter is known by its symbol.
fn substituted<V: TermView>(
    kb: &KnowledgeBase,
    v: &V,
    params: &[Symbol],
    sigma: &[(Symbol, Value)],
) -> Option<Value> {
    let same = |x: Symbol, y: Symbol| x == y || kb.canonical_sym(x) == kb.canonical_sym(y);
    if let Some(param) = view_ref_symbol(kb, v).filter(|&s| params.iter().any(|&p| same(p, s))) {
        return sigma
            .iter()
            .find(|(p, _)| same(*p, param))
            .map(|(_, value)| value.clone());
    }
    match extract_type(kb, v) {
        TypeExtractor::Parameterized { base, bindings } => {
            let named: Vec<(Symbol, Value)> = bindings
                .iter()
                .filter_map(|(key, b)| substituted(kb, b, params, sigma).map(|b| (*key, b)))
                .collect();
            Some(Value::Entity {
                functor: base,
                pos: Rc::from(Vec::new()),
                named: named.into(),
            })
        }
        _ => Some(value_of(v)),
    }
}

/// What [`arguments_relate`] asks of each pair of arguments: by the parameter's declared
/// variance, or equality for every parameter ([`equal`], what an invariant parameter
/// asks).
#[derive(Clone, Copy)]
enum Relation {
    Below,
    Equal,
}

/// Two applications of one sort, `owner` — or of variants of it, whose arguments are its:
/// each argument by `relation`, an argument left out on either side being an open slot.
///
/// AN OPEN SLOT ADMITS ON BOTH SIDES AT RUN TIME. The pattern's slot is a wildcard by
/// definition. A slot of the type asked about is the open side a branch join meets
/// (`kernel-language.md` §5.4: "the open side, which every instance admits"); a raised type
/// has none, since a `TypeValue` answers one type without holes. To the typer's discharge it
/// is a type not known ([`Mode::open`]).
fn arguments_relate<A: TermView, B: TermView>(
    kb: &KnowledgeBase,
    a: &A,
    b: &B,
    owner: Symbol,
    relation: Relation,
    mode: Mode,
    depth: usize,
) -> Result<bool, UnjudgedType> {
    let a_args = arguments(kb, a);
    let b_args = arguments(kb, b);
    let params = kb.type_param_syms_of(owner);
    let variances = match relation {
        Relation::Below => declared_variances(kb, owner, params),
        Relation::Equal => vec![Variance::Invariant; params.len()],
    };
    let mut unjudged: Option<UnjudgedType> = None;
    for (&param, variance) in params.iter().zip(variances) {
        let (av, bv) = (
            binding_for_param(kb, &a_args, param, BindingKeyMatch::Label),
            binding_for_param(kb, &b_args, param, BindingKeyMatch::Label),
        );
        let (Some(av), Some(bv)) = (av, bv) else {
            // An argument left out on a side: the side's own slot of `param`, open.
            let other_slot = |v: Option<&Value>| v.is_some_and(|v| is_pattern_slot(kb, v));
            let a_open = av.is_none() || other_slot(av);
            let b_open = bv.is_none() || other_slot(bv);
            match mode.open(a_open, b_open, true) {
                Some(false) => return Ok(false),
                _ => continue,
            }
        };
        let deeper = depth + 1;
        let holds = match variance {
            Variance::Covariant => below(kb, av, bv, mode, deeper),
            Variance::Contravariant => below(kb, bv, av, mode.flip(), deeper),
            Variance::Invariant => equal(kb, av, bv, mode, deeper),
            Variance::Bivariant => either(below(kb, av, bv, mode, deeper), || {
                below(kb, bv, av, mode.flip(), deeper)
            }),
        };
        match holds {
            Ok(true) => {}
            Ok(false) => return Ok(false),
            Err(e) => {
                unjudged.get_or_insert(e);
            }
        }
    }
    unjudged.map_or(Ok(true), Err)
}

/// `first || second`, where a `true` either side decides and an error is the answer only
/// where neither does.
fn either(
    first: Result<bool, UnjudgedType>,
    second: impl FnOnce() -> Result<bool, UnjudgedType>,
) -> Result<bool, UnjudgedType> {
    match first {
        Ok(true) => Ok(true),
        Ok(false) => second(),
        Err(e) => match second() {
            Ok(true) => Ok(true),
            _ => Err(e),
        },
    }
}

/// `a` and `b` are one type once each open slot is filled: what an invariant parameter
/// asks of its two arguments.
fn equal<A: TermView, B: TermView>(
    kb: &KnowledgeBase,
    a: &A,
    b: &B,
    mode: Mode,
    depth: usize,
) -> Result<bool, UnjudgedType> {
    if depth > NESTING_LIMIT {
        return Err(UnjudgedType::TooDeep);
    }
    if let Some(answer) = decided_before_forms(kb, a, b, mode) {
        return Ok(answer);
    }
    if let Some(same) = two_rows(kb, a, b) {
        return same;
    }
    match (form(kb, a, depth)?, form(kb, b, depth)?) {
        (Form::Bottom, Form::Bottom) => Ok(true),
        (Form::Arrow(fa), Form::Arrow(fb)) => equal(kb, &fa, &fb, mode, depth + 1),
        (Form::Arrow(fa), Form::Sort { .. }) => equal(kb, &fa, b, mode, depth + 1),
        (Form::Sort { .. }, Form::Arrow(fb)) => equal(kb, a, &fb, mode, depth + 1),
        (Form::Sort { head: sa, .. }, Form::Sort { head: sb, owner }) => {
            if !same_sort_canonical(kb, sa, sb) {
                return Ok(false);
            }
            arguments_relate(kb, a, b, owner, Relation::Equal, mode, depth)
        }
        (Form::Tuple, Form::Tuple) => Err(UnjudgedType::TwoTuples {
            a: value_of(a),
            b: value_of(b),
        }),
        _ => Ok(false),
    }
}

/// The arguments a sort-headed type writes, keyed by parameter; none for a bare sort.
fn arguments<V: TermView>(kb: &KnowledgeBase, v: &V) -> Vec<(Symbol, Value)> {
    match extract_type(kb, v) {
        TypeExtractor::Parameterized { bindings, .. } => bindings,
        _ => Vec::new(),
    }
}

/// One side as a value, for an [`UnjudgedType`] to hold.
fn value_of<V: TermView>(v: &V) -> Value {
    match v.as_bind_value() {
        BindValue::Term(t) => Value::term(t),
        BindValue::Value(v) => v,
        BindValue::Path(_) => {
            unreachable!("a concrete type view cannot be an unresolved extraction path")
        }
    }
}

/// Proposal 071 §1.2 — every `TypePattern` provision but its one row, `TypeValuePattern`'s,
/// as a load error ([`LoadError::HandWrittenTypePattern`]), one per provider, in name order.
///
/// THE ONE ROW IS KNOWN BY ITS CONTENT, not by the load that brought it. The stdlib and a
/// program are one load under one recipe and two under another, and the verdict must not
/// follow the recipe. `provides TypePattern[T = T] :- TypeValue[T = T]` is the only row
/// whose provider is `TypeValuePattern` and whose `T` is that sort's own parameter. A
/// program can name `TypeValuePattern` as a provider — a `namespace
/// anthill.reflect.TypeValuePattern` block — but it writes that row only as the row itself,
/// which is the same fact; at another binding it writes a row of its own, refused here. A
/// second CLAUSE of the row, another `:-` alternative or one with no condition, is not
/// refused here: the row's `where` block refuses it in any load (proposal 066 §7.5, a block
/// member backs only its own clause), and a later load's clause is a clause written into a
/// sealed provision as well (`typing::sealed`).
pub(crate) fn written_type_pattern_provisions(kb: &KnowledgeBase) -> Vec<LoadError> {
    let (Some(pattern), Some(row_sort)) = (
        kb.try_resolve_symbol("anthill.reflect.TypePattern"),
        kb.try_resolve_symbol("anthill.reflect.TypeValuePattern"),
    ) else {
        return Vec::new();
    };
    let row_params = kb.type_param_syms_of(row_sort);
    let mut providers: Vec<String> = provides_rows_of_spec(kb, pattern)
        .filter(|row| {
            let own = same_sort_canonical(kb, row.provider, row_sort)
                && matches!(
                    row.bindings(kb).as_slice(),
                    [(_, t)] if impl_param_ref(kb, t, row_params).is_some()
                );
            !own
        })
        .map(|row| kb.qualified_name_of(row.provider).to_string())
        .collect();
    providers.sort();
    providers.dedup();
    providers
        .into_iter()
        .map(|provider| LoadError::HandWrittenTypePattern { provider })
        .collect()
}

/// Proposal 071 §1.3 — where a host operation's raise takes its type from. An operation
/// that raises requires the `TypeValue` of what it raises, and the dictionary reaches a
/// host function the way every requirement reaches an operation — threaded by its caller
/// (decided with the user, 2026-10-24). One reading, for the load rule that refuses a host
/// operation stating no clause (`LoadError::HostRaiseWithoutTypeValue`) and for the run
/// time that takes the dictionary out of the frame (`Interpreter::raise_error`).
#[derive(Debug)]
pub(crate) enum HostRaiseType {
    /// The position, in the operation's dictionary chain ([`op_dict_entries`]), of the
    /// `requires TypeValue[T = X]` its one written `Error[X]` label states — the operation's
    /// own clause or its sort's: its frame slot is that chain's `names` at this index.
    Slot(usize),
    /// Its one `Error` label is bare — `Error[T = ?]`: what it raises is of the unknown type
    /// (WI-20260910-6ARRN's), caught only by a boundary whose pattern is `?`.
    Unknown,
    /// Its row declares no `Error`: a raise of the host function is of the unknown type, and
    /// a handler's throw for it is refused (`HandlerErrorReason::ThrowNotAdmitted`) — a caller
    /// is typed as catching nothing from it.
    NoErrorLabel,
    /// No written `Error` label, and an element a call resolves — a projection (`s.E`), a row
    /// variable — which may carry one: the type of what it raises is the call's, which
    /// nothing threads to the host function, and its raise is refused at run time.
    Projected,
    /// `Error` labels the clauses do not answer: one written `Error[X]` with no `requires
    /// TypeValue[T = X]`, or more than one label (a bare `Error` among them), of which a raise
    /// would have to say which it is.
    Unanswered { written: Vec<Value>, bare: bool },
    /// No operation of that name is declared: nothing states what it raises.
    NoDeclaration,
}

/// [`HostRaiseType`] of `op`, read off its declared effect row and its `requires` chain.
/// A guarded label (`{ Error[X] :- eq(b, 0) }`) is its label.
pub(crate) fn host_raise_type(kb: &mut KnowledgeBase, op: Symbol) -> HostRaiseType {
    // A KB that declares no `Error` (no prelude) has no raise to type and no boundary.
    let (Some(error), Some(type_value)) = (
        kb.error_sort_sym,
        kb.try_resolve_symbol("anthill.reflect.TypeValue"),
    ) else {
        return HostRaiseType::Unknown;
    };
    let Some(info) = crate::kb::op_info::lookup_operation_info(kb, op) else {
        return HostRaiseType::NoDeclaration;
    };
    let mut written: Vec<Value> = Vec::new();
    let mut bare = false;
    let mut projected = false;
    for e in &info.effects {
        let guarded = guarded_effect_label(kb, e);
        let label = guarded.as_ref().unwrap_or(e);
        if effect_label_names_sort(kb, label, error) {
            // `Error[T = ?]` is the bare `Error` once lowered: an identical substitution is
            // not written (§8.1).
            match extract_type_param(kb, label, "T") {
                Some(payload) => written.push(payload),
                None => bare = true,
            }
        } else if !matches!(
            type_head(kb, label),
            TypeHead::SortRef(_) | TypeHead::Parameterized { .. }
        ) {
            projected = true;
        }
    }
    let payload = match (written.as_slice(), bare) {
        ([payload], false) => payload.clone(),
        ([], true) => return HostRaiseType::Unknown,
        ([], false) if projected => return HostRaiseType::Projected,
        ([], false) => return HostRaiseType::NoErrorLabel,
        _ => {
            return HostRaiseType::Unanswered { written, bare }
        }
    };
    let chain = op_dict_entries(kb, op);
    let found = chain.entries().iter().position(|entry| {
        kb.canonical_sort_sym(entry.required_sort) == kb.canonical_sort_sym(type_value)
            && extract_type_param(kb, &entry.spec, "T").is_some_and(|t| same_type(kb, &t, &payload))
    });
    match found {
        Some(i) => HostRaiseType::Slot(i),
        None => HostRaiseType::Unanswered {
            written: vec![payload],
            bare: false,
        },
    }
}

/// `a` and `b` are one written type: structurally, a sort named by two of its symbols
/// (an alias, a re-export) being the one sort, and a type parameter by its two spellings — a
/// row holds an operation's own parameter as its variable (`Error[P]`), a clause as its name
/// (`requires TypeValue[T = P]`).
fn same_type(kb: &KnowledgeBase, a: &Value, b: &Value) -> bool {
    if crate::kb::term_view::views_structurally_equal(kb, a, b) {
        return true;
    }
    if let (Some(x), Some(y)) = (named_type_param(kb, a), named_type_param(kb, b)) {
        return kb.canonical_sym(x) == kb.canonical_sym(y);
    }
    match (type_head(kb, a), type_head(kb, b)) {
        (TypeHead::SortRef(x), TypeHead::SortRef(y)) => same_sort_canonical(kb, x, y),
        _ => false,
    }
}

/// A payload of a host operation's row as its author writes it: a type parameter by its name
/// (`P`, where the row holds its variable), anything else as displayed.
pub(crate) fn host_raise_payload_display(kb: &KnowledgeBase, v: &Value) -> String {
    match named_type_param(kb, v) {
        Some(param) => type_param_display_name(kb, param),
        None => type_display_name_value(kb, v),
    }
}

/// The type parameter `v` is, by its name or by its variable.
fn named_type_param(kb: &KnowledgeBase, v: &Value) -> Option<Symbol> {
    match type_head(kb, v) {
        TypeHead::SortRef(sym) | TypeHead::TypeVar(sym) if is_sort_param_symbol(kb, sym) => Some(sym),
        TypeHead::FlexVar(vid) => kb.type_param_of_canonical_var(vid),
        _ => None,
    }
}

/// Proposal 071 §1.3 — the `TypeValue` evidence of `sort`, a sort the RUNTIME raises a value
/// of with no operation behind the raise to thread it: a `match` with no arm that fits, a
/// stream pulled. Its type is fixed, so its evidence is a constant (user, 2026-10-24):
/// `sort`'s derived row, which must be unconditional — a sort with no type parameter and no
/// `requires`, whose dictionary is `Dictionary(impl: sort)`. `None` where it is not, which
/// the caller reports as a library its evaluator was not written for.
pub(crate) fn account_type_value_evidence(
    kb: &mut KnowledgeBase,
    sort: Symbol,
) -> Option<crate::eval::value::Dictionary> {
    let type_value = kb.try_resolve_symbol("anthill.reflect.TypeValue")?;
    let derived = provides_rows_of_provider(kb, sort)
        .any(|row| same_sort_canonical(kb, row.spec_base, type_value));
    if !derived || dict_layout(kb, type_value, sort, None).arity() != 0 {
        return None;
    }
    crate::eval::value::Dictionary::build(kb, sort, [])
}
