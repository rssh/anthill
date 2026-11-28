//! WI-20261127-3R78F — whether a call at `[Spec = W]` can be built, asked before any call:
//! the dictionary a call's dispatch at that selection is handed, or why none is.

use super::*;

/// Why a call that selects `W` for `Spec` cannot be built ([`dictionary_at_selection`]). The
/// reason alone: the host that asked names the spec and the witness.
#[derive(Debug, Clone)]
pub enum SelectionRefusal {
    /// The bracket is refused, as the call's is, before any dictionary is sought: a key that
    /// names nothing, a value with no sort head ([`TypeError::SelectionValueNotASort`]), a
    /// witness that writes no provision of the spec ([`TypeError::WitnessDoesNotProvide`],
    /// 058 §4.4 check 1 — a provision only through another spec, `W provides Mid` beside `Mid
    /// provides Spec`, is none) or none at the spec's arguments the bracket writes (its
    /// binding-precise half), or a named slot of the witness bound to a value that selects
    /// nothing. There is no call, so the error's operation is the spec.
    Selection(TypeError),
    /// `spec` is no sort a provider may provide: not a sort, or a sort with constructors,
    /// whose operations are its own (kernel-language §5.1).
    NotASpec { spec: Symbol },
    /// The bracket's key of the spec's short name selects no provider for its dispatch: a
    /// key reaches a declared type parameter of that name first (058 §4.2 rule 1), and binds
    /// it.
    NoSelection { spec: Symbol },
    /// The spec's parameter `param` is fixed by nothing: the bracket leaves it unwritten, and
    /// the witness's provisions of the spec do not all say it alike at a type of their own.
    /// A dictionary is of a spec at its arguments — `Dictionary.instance` is refused at an
    /// application that leaves one unwritten — and a call fixes them by its arguments, which
    /// the question has none of. It is no verdict on the witness: written, the parameter is
    /// asked.
    ParameterUnwritten { spec: Symbol, param: Symbol },
    /// The selection names a provider, and the dictionary cannot be built at it.
    Dictionary(DictionaryRefusal),
}

impl SelectionRefusal {
    /// The reason as one sentence, in the words the call's refusal has.
    pub fn message(&self, kb: &KnowledgeBase) -> String {
        match self {
            SelectionRefusal::Selection(e) => e.format(kb),
            SelectionRefusal::NotASpec { spec } => format!(
                "`{}` is no spec: only a sort without constructors is provided, and dispatched",
                kb.qualified_name_of(*spec),
            ),
            SelectionRefusal::NoSelection { spec } => {
                let spec = kb.qualified_name_of(*spec);
                let short = short_name_of(spec);
                format!(
                    "the bracket selects no provider for the dispatch of `{spec}`: its key \
                     `{short}` binds a type parameter of that name"
                )
            }
            SelectionRefusal::ParameterUnwritten { spec, param } => {
                let short = short_name_of(kb.qualified_name_of(*param));
                format!(
                    "nothing fixes `{short}` of `{}`: the selected provider's provisions do not \
                     say it alike, and the bracket does not write it — write it beside the \
                     selection, `[{short} = …]`, as a call's arguments fix it",
                    kb.qualified_name_of(*spec),
                )
            }
            SelectionRefusal::Dictionary(DictionaryRefusal::Unresolved(failure)) => {
                unmet_clause(failure)
            }
            SelectionRefusal::Dictionary(DictionaryRefusal::Ambiguous(tie)) => {
                let spec = kb.qualified_name_of(tie.spec);
                let (candidates, repair) = render_instance_tie(kb, tie);
                format!(
                    "{} and nothing selects one{}",
                    instances_provide(spec, &candidates),
                    tie_repair_advice(spec, &repair),
                )
            }
        }
    }
}

/// WI-20261127-3R78F — the dictionary a host's call of a body-less operation of `spec` that
/// selects `witness` for it — `Spec.op[Spec = W, …](…)` through
/// [`crate::eval::Interpreter::call_bracketed`] — is handed, or the refusal that call makes,
/// answered with no operation and no argument. `spec_args` are the rest of the call's
/// bracket, by key or by position, as the call writes them: the spec's own type arguments
/// (`[(Some("T"), int64)]`), and a provider of one of its `requires` by that spec's short name.
///
/// IT IS THE CALL'S OWN CODE, in the scope a host's call is typed in, which requires nothing
/// (no enclosing declaration a value could name a requirement of, no frame a goal could be
/// answered from): the bracket's reading and each selection's checks
/// ([`spec_dispatch_bracket`] — the spec's parameters bound, the witness's sort, 058 §4.4
/// check 1 and its binding-precise half, the witness's own slot bindings and type arguments),
/// and the dispatch's search at the pinned goal ([`dispatch_dictionary`] — the provision at
/// the witness, a clause of it whose conditions hold, every requirement of the witness's
/// frame, each as the dictionary build resolves it, the default withheld from a named slot as
/// there).
///
/// ONE READING IS THE QUESTION'S OWN, standing for the call's arguments: a parameter of the
/// spec the bracket leaves unwritten is read from the witness's provisions of the spec where
/// they all say it alike, at a type of their own (`MemStore provides Store[C = MemStore, Key =
/// Int64]` says `C` and `Key`; `LBox[A] provides S[T = A]` says `T` at `LBox[A = Int64]`) — a
/// call at the witness whose arguments fix it otherwise is refused at the selection's
/// bindings, so that is the one type a call there runs at. Not said so, it is refused
/// ([`SelectionRefusal::ParameterUnwritten`]). A call whose arguments fix nothing of it is
/// the operation's to answer, where the question holds: `S.g[S = One]()` runs `One`'s own
/// member, and `S.g[S = LBox[A = Int64]]()` is refused, nothing fixing its `T`.
///
/// What a call adds is not asked: what the provider supplies for one operation — two
/// suppliers, or none that runs — is asked at the call of that operation. A witness with type
/// parameters is answered at what `witness` writes of them, as the call is: at the bare sort,
/// a parameter its frame's `requires` reads is fixed by nothing, and refused.
pub fn dictionary_at_selection(
    kb: &mut KnowledgeBase,
    spec: Symbol,
    witness: &Value,
    spec_args: &[(Option<&str>, Value)],
) -> Result<ResolvedRequiresNode, SelectionRefusal> {
    let spec = kb.canonical_sort_sym(spec);
    if !kb.has_kind(spec, crate::intern::SymbolKind::Sort) || !sort_may_be_provided(kb, spec) {
        return Err(SelectionRefusal::NotASpec { spec });
    }
    let spec_short = short_name_of(kb.qualified_name_of(spec)).to_string();
    let spec_key = kb.intern(&spec_short);
    let mut type_args: Vec<(Option<Symbol>, Value)> = spec_args
        .iter()
        .map(|(k, t)| (k.map(|k| kb.intern(k)), t.clone()))
        .collect();
    type_args.push((Some(spec_key), witness.clone()));
    let env = TypingEnv::empty();
    // A selection the bracket makes for a requirement of the spec (`[Desc2 = DA]`) is held
    // to its goal there and goes no further: no search below reads it. Its tie cannot reach
    // a call — each provision's contract, the spec's `requires` at its bindings, is resolved
    // at load, where two providers of one is refused ("MORE THAN ONE provider matches").
    let (mut subst, selections) =
        spec_dispatch_bracket(kb, &env, spec, &type_args).map_err(SelectionRefusal::Selection)?;
    let Some((selection, provider)) = pinned_selection_for(kb, &selections, spec)
        .and_then(|s| s.witness().map(|w| (s.clone(), w)))
    else {
        return Err(SelectionRefusal::NoSelection { spec });
    };
    bind_what_the_provider_says(kb, &mut subst, spec, provider, witness);
    if let Some((param, _)) = spec_param_vars(kb, spec)
        .into_iter()
        .find(|(_, vid)| spec_param_binding(kb, &subst, *vid).is_none())
    {
        return Err(SelectionRefusal::ParameterUnwritten { spec, param });
    }
    let goal = sort_goal_from_subst(kb, &subst, spec, None);
    let sigma = SigmaCtx {
        subst: &subst,
        param_rigids: &[],
    };
    let scope = ResolutionScope {
        available_requires: &[],
        sigma: Some(&sigma),
        pin: Some(&selection),
        sub_goal_requires: &[],
    };
    dispatch_dictionary(kb, &goal, &scope).map_err(SelectionRefusal::Dictionary)
}

/// Each parameter of `spec` that `subst` leaves unbound, bound to what every provision of
/// `spec` that `provider` writes says of it at the witness as the bracket writes it
/// (`witness`, `List[T = Int64]`) — each binding read as a call reads it at a receiver
/// ([`provision_binding_at_receiver`]) — where they all say it alike, at a ground type. One
/// provision that leaves it out or to a parameter the witness does not write, or two that
/// say it apart, leave it unbound.
fn bind_what_the_provider_says(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    spec: Symbol,
    provider: Symbol,
    witness: &Value,
) {
    let views: Vec<Value> = provides_rows_of_provider(kb, provider)
        .filter(|row| same_sort_canonical(kb, row.spec_base, spec))
        .map(|row| row.spec_view)
        .collect();
    if views.is_empty() {
        return;
    }
    let written = parameterized_vid_bindings(kb, witness, provider);
    for (param, vid) in spec_param_vars(kb, spec) {
        if spec_param_binding(kb, subst, vid).is_some() {
            continue;
        }
        let short = short_name_of(kb.qualified_name_of(param)).to_string();
        let mut said: Option<Value> = None;
        let mut alike = true;
        for view in &views {
            let binding = spec_view_bindings_value(kb, view)
                .into_iter()
                .find(|(k, _)| short_name_of(kb.local_name_of(*k)) == short)
                .map(|(_, v)| v);
            let value = binding
                .and_then(|b| provision_binding_at_receiver(kb, &b, provider, &written))
                .filter(|v| type_is_ground(kb, v) && !view_contains_type_param(kb, v));
            match (value, &said) {
                (Some(v), Some(first)) if views_structurally_equal(kb, first, &v) => {}
                (Some(v), None) => said = Some(v),
                _ => {
                    alike = false;
                    break;
                }
            }
        }
        // Bound as the call's reading binds it ([`bind_spec_params_from_provision`]): a
        // ground type holds no variable for the occurs check to find.
        if let (true, Some(value)) = (alike, said) {
            subst.bind_value(kb, vid, value);
        }
    }
}
