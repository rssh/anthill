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
//! test), and the label discharge reads `sort_refines`.
//!
//! PURE, OVER AN IMMUTABLE KB, AND BOUNDED. No substitution and no `&mut`: the run time
//! calls it from a builtin, and the typer's discharge of an `Error` label is to read the
//! same predicate (071 §4, stage (e)) from a site already deep in the expression walk,
//! where a full `types_compatible` descent once overflowed the stack — see
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
    below(kb, t, pattern, 0)
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
    depth: usize,
) -> Result<bool, UnjudgedType> {
    if depth > NESTING_LIMIT {
        return Err(UnjudgedType::TooDeep);
    }
    if let Some(same) = two_rows(kb, a, b) {
        return same;
    }
    match (form(kb, a, depth)?, form(kb, b, depth)?) {
        (Form::Bottom, _) => Ok(true),
        (_, Form::Bottom) => Ok(false),
        (Form::Arrow(fa), Form::Arrow(fb)) => below(kb, &fa, &fb, depth + 1),
        (Form::Arrow(fa), _) => below(kb, &fa, b, depth + 1),
        (_, Form::Arrow(fb)) => below(kb, a, &fb, depth + 1),
        (Form::Sort { head: sa, .. }, Form::Sort { head: sb, owner }) => {
            sort_below(kb, a, sa, b, sb, owner, depth)
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
        ViewHead::Functor { functor: Some(f), .. }
            if kb.qualified_name_of(f) == "anthill.prelude.EffectExpression.empty_row"
    )
}

/// [`below`] for two sort-headed types; `owner` is the sort whose parameters `b`'s arguments
/// bind.
fn sort_below<A: TermView, B: TermView>(
    kb: &KnowledgeBase,
    a: &A,
    sa: Symbol,
    b: &B,
    sb: Symbol,
    owner: Symbol,
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
        return arguments_relate(kb, a, b, owner, Relation::Below, depth);
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
        match arguments_relate(kb, instance, b, owner, Relation::Below, depth + 1) {
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
/// AN OPEN SLOT ADMITS ON BOTH SIDES. The pattern's slot is a wildcard by definition. A
/// slot of the type asked about is the open side a branch join meets (`kernel-language.md`
/// §5.4: "the open side, which every instance admits"); a raised type has none, since a
/// `TypeValue` answers one type without holes.
fn arguments_relate<A: TermView, B: TermView>(
    kb: &KnowledgeBase,
    a: &A,
    b: &B,
    owner: Symbol,
    relation: Relation,
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
        let (Some(av), Some(bv)) = (
            binding_for_param(kb, &a_args, param, BindingKeyMatch::Label),
            binding_for_param(kb, &b_args, param, BindingKeyMatch::Label),
        ) else {
            continue;
        };
        let deeper = depth + 1;
        let holds = match variance {
            Variance::Covariant => below(kb, av, bv, deeper),
            Variance::Contravariant => below(kb, bv, av, deeper),
            Variance::Invariant => equal(kb, av, bv, deeper),
            Variance::Bivariant => either(below(kb, av, bv, deeper), || below(kb, bv, av, deeper)),
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
    depth: usize,
) -> Result<bool, UnjudgedType> {
    if depth > NESTING_LIMIT {
        return Err(UnjudgedType::TooDeep);
    }
    if let Some(same) = two_rows(kb, a, b) {
        return same;
    }
    match (form(kb, a, depth)?, form(kb, b, depth)?) {
        (Form::Bottom, Form::Bottom) => Ok(true),
        (Form::Arrow(fa), Form::Arrow(fb)) => equal(kb, &fa, &fb, depth + 1),
        (Form::Arrow(fa), Form::Sort { .. }) => equal(kb, &fa, b, depth + 1),
        (Form::Sort { .. }, Form::Arrow(fb)) => equal(kb, a, &fb, depth + 1),
        (Form::Sort { head: sa, .. }, Form::Sort { head: sb, owner }) => {
            if !same_sort_canonical(kb, sa, sb) {
                return Ok(false);
            }
            arguments_relate(kb, a, b, owner, Relation::Equal, depth)
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
