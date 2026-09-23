//! Signature elaboration before bodies are checked: rigidifying unwritten sort
//! parameters, self ties, and unwritten fills.

use super::*;

/// WI-392: build a substitution that Skolemizes an operation's own declared type
/// parameters — each `Var::Global(vid)` ↦ a fresh `Var::Rigid`. Applied (via
/// `walk_type_deep_value`) to the op's param types / return / effects before its
/// body is checked, so the body sees its type parameters as rigid
/// (fixed-but-abstract) constants: usable but not solvable. Mirrors the
/// resolver's `forall_impl` skolemisation (`resolve.rs` `step_forall_impl`), the
/// only other site that mints `Var::Rigid`.
/// WI-849: takes each parameter's `Var` directly. The op side (`OpInfoRecord::
/// type_params`) is already `Var`-typed; the SORT side ([`sort_type_params_as_pairs`],
/// still TermId-typed because its consumers unify against the param as a term under
/// `&KnowledgeBase`) is converted by the caller, where its own `Var::Global` filter
/// makes the conversion total.
///
/// The `Var::Global` test below is therefore DEFENSIVE, not a live filter, and the
/// difference is worth stating because the obvious justification for it is FALSE
/// (review): "a sort param may alias a CONCRETE sort (`sort T = Int64`), which is not
/// skolemizable" describes a case that never arrives — `sort_type_params_as_pairs`
/// admits an entry only when it already IS a `Term::Var(Var::Global(_))`, so a concrete
/// alias is dropped BEFORE the concat, and the caller's own conversion `unreachable!`s
/// on anything that is not a `Term::Var`. Both input tables are all-`Global`; nothing
/// reaching here can fail this test today. It is kept as a total match rather than an
/// assertion because a `Rigid`/`DeBruijn` entry would be a caller bug, not user input,
/// and skolemizing one would be worse than leaving it alone.
/// WI-1059/WI-1061 — materialize a declared PARAMETER type's UNWRITTEN sort parameters as
/// `Var::Rigid` skolems, for the duration of the operation's body check. WI-1059 covered a
/// parameter's TOP LEVEL; WI-1061 covers the slots below it — nested inside a binding, inside
/// a callback's RESULT, inside a TUPLE COMPONENT — which is why the walk recurses and why the
/// filler is a parameter ([`UnwrittenFill`]) rather than a constant. The RETURN position is
/// deliberately not here — see the block comment at the caller, and **WI-1063**.
///
/// THREE CHILDREN ARE EXCLUDED, each with its reason at its own site rather than here: an
/// effect-ROW binding and an arrow's effects (a row, not a type), and a callback's own
/// PARAMETER (the quantification faces the other way). Nothing else is: a carrier this walk
/// does not descend into is a slot left silently flexible, which is the defect the whole
/// function exists to prevent, so the `_` arm is the one to distrust when a leak turns up.
///
/// THE THIRD FAMILY. [`rigidify_op_type_params`] skolemizes two: the operation's own `[T]`
/// (WI-392) and its enclosing sort's (WI-942). A parameter of ANOTHER sort left unwritten
/// in a parameter's type — `Stream`'s `E` in `s: Stream[T = Int64]` — is in neither, and
/// there is no variable to skolemize because the slot was never materialized at all: a
/// partial application carries only the bindings it wrote, and a bare `Ref(S)` carries
/// none. So this MINTS the slot and its skolem together.
///
/// The rule it enforces is `docs/kernel-language.md` §"Expansion during unification": an
/// unwritten parameter is a NEW variable per instantiation, so the operation is universally
/// quantified over it and its body may only do what holds for EVERY value of it. Inside the
/// body it is therefore rigid; at a CALL it is flexible again and binds from the argument.
/// Same variable, two positions — and this rewrite is confined to the body, so the call side
/// is untouched (it rebuilds `OpInfo.params` only; the KB's `OperationInfo` fact, which
/// every call site reads, keeps its flexible slots).
///
/// WHICH skolem each position takes is [`UnwrittenFill`]'s, and the two arms are documented
/// there. Either way the fill is rigid by a mechanism already in place, which is why this
/// needs no new rule in the subtype relation: `Stream[T = Int64, E = s.E]` against
/// `Stream[T = Int64, E = {}]` is refused by the WI-400 ζ arm, and a fresh `Var::Rigid` by
/// plain unification. [`refine_self_receiver_body_type`] builds the identical projection for
/// the identical reason (a bare self-receiver return pinned to `l.T`).
///
/// ALL FOUR SPELLINGS OF ONE TYPE ARRIVE HERE ALIKE, which is what makes them agree (the
/// WI-1056 measurement, whose four rows this ticket keeps in lockstep at the new verdict):
/// the explicit `[E]` needs nothing from this function (WI-392 already rigidified it, and
/// the check reaches it once a skolem counts as ground — see [`type_value_is_ground`]);
/// `E = ?` arrives as a written binding whose value is a still-FLEX var and is replaced by
/// the projection; `Stream[T = Int64]` and the bare `Stream` arrive missing the slot, and it
/// is minted. A slot written CONCRETE, or written as the op's own rigid, is left alone.
///
/// SELF AND FOREIGN REFERENCES FILL THE SLOT DIFFERENTLY, and `docs/design/type-parameter-
/// scoping.md` §3 is what decides which: "Within the sort's own definition, a bare self-sort
/// reference participates in that tie — `append(xs: List, ys: List)` declared *inside*
/// `sort List` ties both parameters (and the return) to *this* sort's `T`", whereas two
/// FOREIGN references "do not silently share a variable across a signature". So a self
/// reference's unwritten slot is THIS instance's parameter — the enclosing sort's rigid,
/// which WI-424 already minted — and only a foreign one is fresh-per-occurrence and takes
/// [`UnwrittenFill`]'s answer. MEASURED, and this split is why it is here: filling a self
/// reference with a projection refused `Pair.compare(a: Pair, b: Pair)` at `expected a.A,
/// got b.A`, which is the member tie read as its own negation. The self arm is DEPTH-BLIND on
/// purpose: the tie is the SORT's, so a self reference nested in a binding takes the same
/// rigid a top-level parameter does. DRIVEN, by backing exactly that out (`is_self &&
/// !matches!(fill, Anonymous)`): the stdlib then reports 4 errors, all `expected List[T = ?T],
/// got List[T = ?T] (these render alike but are not the same type)` — `List.insert`,
/// `Stream.iterator` and two `match` rules, each holding one skolem for the enclosing sort's
/// `T` and a second, unrelated one for the same sort named again.
///
/// `None` when nothing was filled — the type is returned unrebuilt, which is what lets the
/// recursion stay exact about whether a nested binding changed rather than re-minting an
/// equal-but-distinct carrier for every signature in the corpus.
///
/// THE DECLARED EFFECTS ARE NOT A FURTHER POSITION, and this is measured rather than deferred
/// on a hunch. Over the whole corpus the declared effect atoms are row variables (`E`,
/// `EffP`), projections (`s.E`), `Modify[v]` value-in-type denotations and concrete labels —
/// no parametric sort application with an unwritten slot. And when one is written on purpose,
/// the effects check is already STRICT in the SAFE direction: `operation weak() -> Int64
/// effects Box = raise_int()` where `raise_int` incurs `Box[T = Int64]` is refused today at
/// `expected declared: [Box], got undeclared effect: Box[T = Int64]` —
/// `views_structurally_equal` does not read a bare atom and a parameterized one as one
/// effect, so the laundering this function exists to stop cannot be built there. That
/// strictness is also why the recursion must not DESCEND into an effect-row binding; the gate
/// for it is at the recursion site.
pub(super) fn rigidify_unwritten_sort_params(
    kb: &mut KnowledgeBase,
    fill: UnwrittenFill,
    ty: &Value,
    position: SlotPosition<'_>,
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
) -> Option<Value> {
    let (base, written) = match extract_type(kb, ty) {
        TypeExtractor::SortRef(s) => (s, Vec::new()),
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        // WI-1061 (review) — A SORT APPLICATION IS NOT THE ONLY THING A PARAMETER TYPE CAN
        // BE, and the first cut of this walk descended only through `Parameterized`
        // bindings, so `f: (x: Int64) -> Stream[T = Int64]` and `p: (s: Stream[T = Int64],
        // n: Int64)` kept their unwritten rows FLEXIBLE. Both are the WI-1059 hole verbatim,
        // one carrier further in, and both were driven: `feed(f: (x: Int64) -> Stream[T =
        // Int64]) = takes_pure(f(1))` with a `{Error}`-returning callback loaded clean, as
        // did the tuple form. They are inside a PARAMETER — the position WI-1063's two
        // readings agree about — so they belong here and not there.
        //
        // The `_` arm below is what let them through, which is why these two are written out
        // rather than folded into it: a carrier this walk does not know is a slot it silently
        // leaves flexible, and the whole function exists to stop silent leaks.
        TypeExtractor::Arrow {
            param,
            result,
            effects,
            arity,
        } => {
            // THE RESULT ONLY. The two other children are each left alone for their own
            // reason, and neither is a hedge:
            //
            // The EFFECTS child, for the reason the written-binding gate below states — a
            // row's labels are compared by structural identity against what a body incurs,
            // and materializing a label's own parameters makes two spellings of one effect
            // unequal.
            //
            // The PARAMETER child because the VARIANCE flips there, and the first cut of this
            // arm got it wrong. An unwritten slot in a callback's own parameter says the
            // callback accepts EVERY instantiation — it is the caller of `f` that chooses, so
            // the body may pass whatever it has. Rigidifying it says the opposite: that `f`
            // accepts one fixed unknown, which the body must then match. DRIVEN — walking it
            // failed 9 tests at `each(l: List[T = Cell], f: (a: Cell) -> Unit)` and
            // `foldCell(xs: List[T = Cell], z: Cell, f: (a: Cell, t: Cell) -> Cell)`, all
            // `expected Cell[V = ?V], got Cell[V = z.V]` or two skolems rendering alike:
            // `f(h)` was refused for handing a perfectly good cell to a callback that had
            // declared it takes any. A RESULT is the position that faces the body the same
            // way a parameter of the operation does — the body CONSUMES what `f` returns —
            // which is why it belongs here and the parameter does not.
            let nr = rigidify_unwritten_sort_params(
                kb,
                UnwrittenFill::Anonymous,
                &result,
                position,
                span,
                owner,
            )?;
            let p = value_to_type_child(kb, &param);
            let r = value_to_type_child(kb, &nr);
            let e = value_to_type_child(kb, &effects);
            // WI-791: the arrow's own ARITY rides across a rebuild — filling a type slot
            // rewrites a parameter's TYPE and never the parameter COUNT. Rebuilt as a
            // `Value::Node` unconditionally, which is the primary arrow form (see
            // [`make_arrow_value`]: the representation note disclaims hash-consing for
            // binders), so a ground arrow stays a Node spine over interned leaves.
            return Some(Value::Node(kb.make_arrow_occ(p, r, e, arity, span, owner)));
        }
        TypeExtractor::NamedTuple(fields) => {
            let mut out: Vec<(Symbol, Value)> = Vec::with_capacity(fields.len());
            let mut any = false;
            for (label, v) in &fields {
                match rigidify_unwritten_sort_params(
                    kb,
                    UnwrittenFill::Anonymous,
                    v,
                    position,
                    span,
                    owner,
                ) {
                    Some(rewritten) => {
                        out.push((*label, rewritten));
                        any = true;
                    }
                    None => out.push((*label, v.clone())),
                }
            }
            if !any {
                return None;
            }
            // Labels and their ORDER are transplanted: a named tuple is an ORDERED PRODUCT
            // whose source order is its identity (WI-788), so the rebuild must not re-slot.
            return Some(named_tuple_value(kb, &out, span, owner));
        }
        _ => return None,
    };
    // Exactly "the parameters an unwritten slot would expand to a fresh var for" — the
    // same table the WI-1056 acceptance arm consults, so the two cannot disagree about
    // which slots a partial application is missing.
    let declared = sort_type_params_as_pairs(kb, base);
    if declared.is_empty() {
        return None;
    }
    let is_self = position
        .self_sort()
        .is_some_and(|p| kb.canonical_sort_sym(p) == kb.canonical_sort_sym(base));
    let key_match = BindingKeyMatch::for_bases(kb, base, base);
    let mut bindings: Vec<(Symbol, Value)> = Vec::with_capacity(declared.len().max(written.len()));
    let mut consumed = vec![false; written.len()];
    let mut changed = false;
    for (param, canonical) in declared.iter() {
        let slot = binding_index_for_param(kb, &written, *param, key_match);
        if let Some(i) = slot {
            consumed[i] = true;
            let (k, v) = &written[i];
            // A slot written `?` is an unwritten one spelled out (kernel-language
            // §"Expansion during unification" — the four ways mean the same thing), and
            // it arrives here as a still-FLEX var. Anything else the author wrote —
            // a concrete type, the op's own `[E]` (already a rigid), the enclosing sort's
            // param — is what they meant, and stands.
            //
            // WI-1063: WHICH written carriers count is the position's, not a constant — at a
            // call the broad flex-var test reads the opposite fact. See
            // [`SlotPosition::written_slot_is_unwritten`], which the corpus decided.
            if !position.written_slot_is_unwritten(kb, v) {
                // WI-1061 — but what the author wrote may itself leave slots unwritten one
                // level DOWN (`l: List[T = Stream]` writes `T` and leaves `Stream`'s own
                // `T`/`E` open), and those are unwritten in exactly the §"Expansion during
                // unification" sense. Recurse. Nothing NAMES a nested slot, so the fill
                // there is [`UnwrittenFill::Anonymous`] whatever this level's was.
                //
                // NOT INTO AN EFFECT-ROW SLOT. `E = Error` in `Stream[T = Solution, E =
                // Error]` looks structurally identical to a nested data type — a `SortRef`
                // whose sort happens to declare a parameter — but it is a ROW, and its
                // labels are compared by structural identity against the effects a body
                // INCURS. Materializing `Error`'s own `T` there makes the two spellings of
                // one label unequal, and the op is refused against its own declaration.
                // DRIVEN, and it is what the recursion cost before this gate: the
                // `anthill-todo` program's `collect_id_set` and `walk_solutions` failed at
                // `expected declared: [Error], got undeclared effect: Error[T = ?T]`,
                // taking 193 tests with them. `sort_param_is_effect_row` keys on the
                // DECLARING sort's kind-anchor (WI-594/WI-320), which is the only thing
                // that separates the two — the values are the same shape.
                let short = short_name_of(kb.local_name_of(*param)).to_owned();
                if sort_param_is_effect_row(kb, base, &short) {
                    bindings.push((*k, v.clone()));
                    continue;
                }
                let inner = rigidify_unwritten_sort_params(
                    kb,
                    UnwrittenFill::Anonymous,
                    v,
                    position,
                    span,
                    owner,
                );
                match inner {
                    Some(rewritten) => {
                        bindings.push((*k, rewritten));
                        changed = true;
                    }
                    None => bindings.push((*k, v.clone())),
                }
                continue;
            }
        }
        // WI-1078 — a slot the author wrote as an UNBOUND NAMED variable takes the one rigid
        // this call opened that VARIABLE to, so every slot the author tied together stays
        // tied. Read before the mint and after the self question, which is the order the two
        // rules already have: a self slot is not existential at all (WI-1063), so it never
        // gets here whatever it was spelled.
        let opened_named = slot.and_then(|i| position.opened_named_var(kb, &written[i].1));
        // WI-1082 — the two halves of [`SlotPosition`]'s 3×2 table, read in the order the
        // rules already have. `None` from either half means THIS POSITION LEAVES THE SLOT, and
        // both reach the same restore below: put back exactly what was there, because the slot
        // is already marked `consumed` and the carry-the-unmatched loop will NOT restore it —
        // skipping outright would DROP an author's `P[A = ?]` on the floor whenever a sibling
        // binding caused a rebuild. That drop is invisible (`A = ?` and an absent `A` mean the
        // same type), which is precisely why it must not be left to be re-derived.
        let filled = if is_self {
            position.fill_self(kb, *canonical)
        } else if let Some(rho) = opened_named {
            Some(rho)
        } else {
            position.fill_foreign(kb, fill, *param)
        };
        let Some(filled) = filled else {
            if let Some(i) = slot {
                bindings.push(written[i].clone());
            }
            continue;
        };
        bindings.push((*param, filled));
        changed = true;
    }
    if !changed {
        return None;
    }
    // A written binding matching no declared parameter is CARRIED, not dropped — it is a
    // malformed or cross-keyed type, and losing it here would silently change what the
    // body is checked against. Whoever owns that diagnosis still sees it.
    for (i, kv) in written.iter().enumerate() {
        if !consumed[i] {
            bindings.push(kv.clone());
        }
    }
    let base_ref = kb.make_sort_ref(base);
    Some(parameterized_value(kb, base_ref, &bindings, span, owner))
}

/// WI-1063 — OPEN one call's existential return: mint a FRESH anonymous rigid for every
/// unwritten sort parameter in the callee's declared return type. The caller's rationale is
/// at the call site in [`check_apply_iter`]; what belongs here is the SCOPE.
///
/// FOREIGN SLOTS ONLY, via [`SlotPosition::CallResult`] — the callee's OWN sort is not
/// existential in its return, it is the §3 parametricity tie, and this call's argument
/// unification is what pins it through the canonical channel. Skipping it is the same
/// decision [`expand_foreign_sort_application`] takes on the parameter side, keyed the same
/// way, and for one reading of one rule.
///
/// FOUR SITES TURN A DECLARED RETURN INTO A RESULT TYPE, and all four must call this. The
/// first cut wired only the first, and each omission was a live hole rather than a tidiness
/// point — the ticket's own exploit ran through both of the ones review found:
///
/// * [`check_apply_iter`]'s Path 1, which every *applied* form reaches — a dotted call
///   (`s.map(f)`), a qualified static (`Stream.splitFirst(s)`) and a bare application all
///   desugar to one `Apply` (WI-752's unified ladder);
/// * [`check_apply_iter`]'s Path 3, the fallback for a functor that has a recorded return but
///   no full `OperationInfo`;
/// * [`check_bare_ref`]'s ZERO-ARG-CALL reading, where a nullary operation named WITHOUT
///   parentheses denotes its return. DRIVEN: `takes_pure(mk())` was refused while
///   `takes_pure(mk)` loaded clean — the exploit surviving a one-character edit — and it is
///   not the eta reading, since `mk() -> Stream[T = String]` is refused at the same site;
/// * [`operation_as_function_value`]'s ETA lift, whose arrow RESULT is that same declared
///   return. DRIVEN: `apply_it(widen, s)` laundered `{Error}` into a slot declaring `E = {}`.
///   That site opens ONCE PER LIFT rather than per application, which is a real limit stated
///   there — an arrow type has nowhere to write `∃`.
///
/// `callee_sort` is the sort that declares the operation whose return this IS, which is not
/// always the one the CALL named: the WI-606 fallback threads a concrete override's
/// declaration, and asking the §3 self question of the spec op would read the override's own
/// carrier as foreign. Its callers pass `impl_parent_sort_of_op` of the right symbol.
/// `callee_op` is that same operation's SYMBOL, and it is what WI-1078 reads the rest of the
/// signature through — see [`unbound_return_var_openings`].
///
/// `None` when nothing was opened, which is the overwhelmingly common case: a fully-written
/// return, a non-parametric one, or a self-sort one. The caller keeps its original value
/// rather than a re-minted equal-but-distinct carrier.
pub(super) fn open_existential_return(
    kb: &mut KnowledgeBase,
    callee_sort: Option<Symbol>,
    callee_op: Symbol,
    ret: &Value,
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
) -> Option<Value> {
    let opened = unbound_return_var_openings(kb, callee_op, ret);
    rigidify_unwritten_sort_params(
        kb,
        UnwrittenFill::Anonymous,
        ret,
        SlotPosition::CallResult {
            callee_sort,
            opened: &opened,
        },
        span,
        owner,
    )
}

/// WI-1082 — WRITE §3's TIE DOWN, once per declaration, before anything reads the signature.
///
/// A member whose declared RETURN names its OWN sort and leaves a parameter slot unwritten is
/// not making an existential claim — `docs/design/type-parameter-scoping.md` §3 bullet 1 says
/// a bare self-sort reference inside the sort's own definition ties the parameters AND THE
/// RETURN to *this* sort's parameter. So `insert(c: List, elem: T) -> List` means `-> List[T =
/// T]`, and this pass writes exactly that: the sort's OWN parameter var, the spelling the
/// sibling parameter `elem: T` already uses and the one `SortedSet.insert(s: SortedSet[T = T,
/// O = O], x: T) -> SortedSet[T = T, O = O]` writes out by hand.
///
/// THE SORT'S PARAMETER, NOT THE RECEIVER'S PROJECTION, and this was measured rather than
/// chosen. `-> List[T = c.T]` is the same type wherever both spellings can answer — in a body
/// `c : List[T = ?T]`, so `c.T` reduces to the sort's rigid — but it reads ONE parameter where
/// the tie pools ALL of them, and it fails wherever that one cannot answer. Driven, both
/// halves from the suite: `put(empty(), "a", 1)` has no stable receiver to project off (the
/// argument is a call, so `param_to_arg_sym` records nothing) and `Map.put`'s result came back
/// as the un-eliminated `Map[K = m.K, V = m.V]`, while the canonical form has `key: K` and
/// `value: V` bind the very same vars; and writing a projection into `put`'s return flips
/// `op_has_projection` on for the whole call, which then failed its own PARAMETERS at
/// `expected m.K, got Int64`. The canonical var perturbs no call path — it is what the
/// signature already rides (`unify_parameterized_with_sort_ref` + the per-call `subst`).
///
/// WHY THE ABSENCE WAS UNSOUND, and why the fix cannot live at the call. An unwritten slot is
/// width-IGNORED by `unify_parameterized_view`: nothing is claimed about it, so nothing refutes
/// a consumer's demand. WI-1063 closed that for FOREIGN sorts by opening the slot to a fresh
/// rigid at each call and left the self case alone, which is WI-1082's five-line exploit:
/// `widen(s: MyStream[T = Int64, E = {Error}]) -> MyStream[T = Int64] = s` loaded, and
/// `takes_pure` (declaring `E = {}`) accepted its result. The laundering has TWO producers —
/// the BODY check width-ignores the same slot, so `widen`'s declaration was never checked
/// against its body either — and a call-side-only filler would make the caller trust a claim
/// nothing had verified. One rewrite of the SIGNATURE closes both, because both read it.
///
/// WHERE THE EXPLOIT NOW FAILS IS THE DECLARATION, NOT THE CONSUMER, and the ticket's
/// acceptance names that as the other admissible verdict. `widen`'s return says "a `MyStream`
/// at THIS instance's `E`"; within a member body the sort's parameters are rigid (WI-424, the
/// §3 tie read as parametricity), so the body must hold for EVERY `E` and `= s` — pinned to
/// `{Error}` by its own parameter — does not. The message points at `widen.return`, which is
/// where the defect was written, instead of at an innocent `takes_pure`. The general rule it
/// states: a member may not pin its own sort's parameter to a constant and still elide it in
/// the return. Writing the return out (`-> MyStream[T = Int64, E = {}]`) is unaffected — a
/// WRITTEN slot is never touched here — so the shape stays expressible, it just has to be said.
/// The corpus contains no such declaration: all four tiers load with zero errors.
///
/// NO SELF PARAMETER, NO TIE. `List.empty() -> List` has no parameter denoting an instance, so
/// [`declares_self_param`] answers `false` and the slot stays unwritten rather than taking a
/// canonical var this call can never bind — a raw canonical var in `resolved_ret` is the
/// dangling-flex hazard the WI-374 note names. Leaving it is also the right answer for
/// `empty`, whose body holds for every `T` and whose caller determines it through WI-270's
/// `expected` seeding. See [`SlotPosition::fill_self`] for what that leaves open (**WI-1083**).
///
/// RUN ONCE, from [`type_check_sorts_collect`], immediately after `build_op_signatures` and the
/// alias/provides indexes it reads.
///
/// WHAT IT REWRITES, AND WHO THEREFORE SEES IT. The target is the CACHED
/// [`crate::kb::op_info::OpSignature`]; the `OperationInfo` FACT is left as the author wrote it, so
/// anything reading the fact directly (persistence's printer, a reflect query over the fact)
/// still sees the declaration. But [`crate::kb::op_info::lookup_operation_info`] answers from the
/// CACHE FIRST, and its own doc names the typer, eval, reflect and codegen as that fast path's
/// callers — so all of them see the elaborated signature. That is intended: the elaboration is
/// what the declaration MEANS, and a backend lowering `-> List` without its element is lowering
/// less than the author said. It is stated here because that cache documents itself as "a pure
/// accelerator, never a correctness change", and this is the exception; the same note is at
/// that function.
///
/// THE TWO TIERS CAN THEREFORE DISAGREE, and the disagreement is bounded to KBs that never
/// type-check. `lookup_operation_info` falls back to scanning the facts when nothing is cached
/// — during load (the const-purity gate, the eq-dispatch-table build) and on a KB built without
/// reflect, where `build_op_signatures` caches nothing at all. Those readers get the
/// un-elaborated declaration. Neither load-time caller asks about a return type's slots, and no
/// typing-time caller can precede this pass; a KB that is loaded and lowered WITHOUT ever
/// type-checking is outside every entry point the CLI and the test harness use.
///
/// RE-RUNNABLE, which `load_all` into a live KB needs: `build_op_signatures` rewrites each cached
/// signature from its `OperationInfo` fact unconditionally, so a second type-check starts from
/// the author's declaration again rather than from this pass's output. Nothing here has to be
/// idempotent against its own result.
pub(super) fn elaborate_self_ties(kb: &mut KnowledgeBase, sort_names: &[Symbol]) {
    // GATED, THEN SORTED, THEN CLONED — in that order, and each step earns its place. Only a
    // member of a PARAMETRIC sort can be rewritten, and `sort_type_params_as_pairs` is memoized,
    // so that test rejects the overwhelming majority under one immutable borrow before any
    // signature is cloned. The survivors are sorted by symbol because `op_records` is a
    // `HashMap` with `RandomState`: nothing here depends on order, but each rewrite interns new
    // `TermId`s, and leaving the numbering to hash order makes two loads of the same sources
    // differ in anything that prints one.
    let mut candidates: Vec<(Symbol, Symbol)> = kb
        .op_records
        .iter()
        .filter(|(_, rec)| rec.signature.is_some())
        .filter_map(|(op_sym, _)| Some((*op_sym, impl_parent_sort_of_op(kb, *op_sym)?)))
        .filter(|(_, sort)| !sort_type_params_as_pairs(kb, *sort).is_empty())
        .collect();
    candidates.sort_by_key(|(op_sym, _)| op_sym.index());
    for (op_sym, sort) in candidates {
        let Some((ret, params)) = kb
            .op_record(op_sym)
            .and_then(|r| r.signature.as_ref())
            .map(|s| (s.return_type.clone(), s.params.clone()))
        else {
            continue;
        };
        if !declares_self_param(kb, &params, sort) {
            continue;
        }
        // The span/owner a rebuild stamps on a `Value::Node` carrier — read ONLY on that
        // branch of [`parameterized_value`], which a Term-carried return never reaches: every
        // value this fill mints is a hash-consed canonical var, so a Term-carried input
        // rebuilds Term-carried. An occurrence-carried return (a `denoted` value-in-type
        // binding) must keep its own node's pair, and the other arm supplies what a diagnostic
        // would want if
        // a future fill ever did carry a node. `functor_span` is EMPTY for almost every
        // operation — it is written by `create_occurrence`, i.e. only for a symbol that heads
        // a stored term — which is why this cannot be a `let … else continue`: demanding a
        // span here skipped all 216 elaborations in the corpus and the pass measured as inert.
        let (span, owner) = declared_span_owner(kb, &ret, op_sym);
        // WI-1078's classification, read here for the SELF answer rather than the foreign one.
        let unbound: Vec<u32> = unbound_return_vars(kb, op_sym, &ret)
            .into_iter()
            .map(|v| v.raw())
            .collect();
        let elaborated_ret = rigidify_unwritten_sort_params(
            kb,
            UnwrittenFill::Anonymous,
            &ret,
            SlotPosition::Declared {
                sort,
                unbound: Some(&unbound),
            },
            span,
            owner,
        );
        // THE PARAMETERS TAKE THE SAME REWRITE, and leaving them out was a hole rather than a
        // smaller scope. §3 bullet 1 ties "both parameters (AND the return)" to this sort's
        // parameter, and only the pair states the tie: with the return alone, a self parameter
        // that elides a slot still writes no binding, so the call's argument never reaches the
        // sort's parameter and the return's copy of it stays a raw flexible var that unifies
        // with anything. DRIVEN — `operation widen(s: MyStream[T = Int64]) -> MyStream`
        // declared inside `sort MyStream`, with NO body, loaded clean and its result satisfied
        // a parameter declaring `E = {}`: §8.1's headline exploit, surviving for exactly the
        // population that has no body check to catch it (spec ops, host-mapped members,
        // declaration-only members). `wi1082_…::a_bodyless_member_cannot_launder_either` holds
        // it, and `the_headline_…`'s first half is the bodied twin the body check catches.
        //
        // NO `unbound` SET HERE, and that is the polarity difference rather than an omission: a
        // named variable in a PARAMETER is bound BY being in a parameter — the caller supplies
        // it — which is the first of WI-1078's three binders. Only the anonymous spelling can
        // be unwritten in this position.
        let mut elaborated_params: Vec<(Symbol, Value)> = Vec::with_capacity(params.len());
        let mut params_changed = false;
        for (pname, pty) in &params {
            // A BARE self parameter is ALREADY tied, by a different mechanism, and writing the
            // tie into it breaks a pattern the stdlib depends on. `unify_parameterized_with_
            // sort_ref` binds the sort's canonical vars whenever ONE SIDE is a bare sort
            // reference, so `reverse(xs: List)` reaches the argument's element without help.
            // Writing `List[T = T]` there instead makes the binding a strict one, and the
            // WI-424 seeding — which pins a SAME-SORT sibling call's canonical params to the
            // enclosing instance's rigids before argument unification — then refuses a sibling
            // called at a DIFFERENT element. DRIVEN: `List.mapElems[Dst]`'s
            // `reverse(mapElemsOnto(xs, f, seed))` fails at `expected List[T = ?T], got List[T
            // = ?Dst]`, and with it every corpus tier.
            //
            // What is left is exactly the gap: a PARTIALLY written self reference, where
            // `unify_parameterized_view` width-ignores the slot the author elided and no
            // canonical binding happens at all.
            if matches!(extract_type(kb, pty), TypeExtractor::SortRef(b)
                if kb.canonical_sort_sym(b) == kb.canonical_sort_sym(sort))
            {
                elaborated_params.push((*pname, pty.clone()));
                continue;
            }
            let (pspan, powner) = declared_span_owner(kb, pty, op_sym);
            match rigidify_unwritten_sort_params(
                kb,
                UnwrittenFill::Anonymous,
                pty,
                SlotPosition::Declared {
                    sort,
                    unbound: Some(&[]),
                },
                pspan,
                powner,
            ) {
                Some(rewritten) => {
                    elaborated_params.push((*pname, rewritten));
                    params_changed = true;
                }
                None => elaborated_params.push((*pname, pty.clone())),
            }
        }
        if elaborated_ret.is_none() && !params_changed {
            continue;
        }
        if let Some(sig) = kb
            .op_records
            .get_mut(&op_sym)
            .and_then(|r| r.signature.as_mut())
        {
            if let Some(r) = elaborated_ret {
                sig.return_type = r;
            }
            if params_changed {
                sig.params = elaborated_params;
            }
        }
    }
    elaborate_self_field_ties(kb, sort_names);
}

/// WI-1082 — the SAME tie at the other declaration position: an ENTITY FIELD whose type names
/// its own sort. `docs/design/type-parameter-scoping.md` §3 states this one literally —
/// "`cons(head: T, tail: List)` ⇒ `tail` is a `List` of *this* sort's `T`" — so this writes
/// `List[T = T]`, the spelling its own sibling field already uses.
///
/// THE RETURN HALF DOES NOT STAND WITHOUT IT. `case cons(x, rest)` binds `rest` at the DECLARED
/// field type, so an untied `tail: List` handed the body a tail with no element; that was
/// invisible only because `append`'s return was erased too. Measured: with the return half
/// alone, the whole corpus raised exactly one error, `cons.type_args` in `List.append`. See
/// [`SlotPosition::fill_self`] for the mechanism and the four stdlib workarounds it retires the
/// reason for.
///
/// THE TWO HALVES HAVE DIFFERENT SCOPES ON PURPOSE, and the reason is which store each writes.
/// The signature half must revisit EVERY operation in the KB, because `build_op_signatures`
/// resets every cached signature from its fact on each type-check, so an op elaborated by a
/// previous `load_all` arrives un-elaborated again. This half writes a registry that is NOT
/// reset, so it only has to reach the sorts THIS call defines (`sort_names` is the caller's
/// `defined_sorts`) — an entity from an earlier load still carries the tie it was given then,
/// which [`the_field_tie_is_a_fixpoint`](wi1082_self_return_tie_test) pins from the other side.
///
/// [`KnowledgeBase::field_constructors_of_sort`] IS THE OWNER of "whose fields are these", and
/// the reason it beats the `SortInfo` constructor list is the case it adds: a free-standing
/// `entity X(next: X)` (§6.3's sugar) emits no `SortInfo` but does carry
/// `entity_field_types(X)`, and reading the index would silently give it no tie — the WI-490
/// hole that helper exists to close. `sort_names` is the set the caller is type-checking.
///
/// NO `unbound` SET, unlike the return half: a field type has no signature whose parameters,
/// `[A]` binders or `requires` chain could bind a variable, so the only spelling that can be
/// "unwritten" here is the anonymous one.
///
/// IN PLACE, AND THEREFORE VISIBLE TO EVERY READER OF THAT REGISTRY — which is more than the
/// typer. `persistence::term_ser`'s `entity_field_type_map` reads `entity_field_types` to pick
/// the ground `TermId` it hands `value_to_term_typed` when reconstructing a persisted fact, and
/// the C++ backend reads it to lower entity fields. After a type-check `cons`'s `tail` is
/// `List[T = <the sort's parameter>]` rather than a bare `Ref(List)`, so those readers see the
/// tie too. Intended, for the reason the return half states: the tie is what the declaration
/// MEANS, and a lowering that drops it lowers less than the author wrote. A KB that never
/// type-checks keeps the raw field types, the same two-tier bound the signature cache has.
///
/// IDEMPOTENT, WHICH THE SIGNATURE HALF DOES NOT HAVE TO BE. Nothing reconstructs this registry
/// from facts the way `build_op_signatures` reconstructs each cached signature, so a second
/// type-check (`load_all` into a live KB) sees this pass's own output. It is a fixpoint: an
/// already-elaborated slot holds the sort's parameter var, which is a `Ref`-carried type
/// reference rather than a flexible variable, so [`SlotPosition::written_slot_is_unwritten`]
/// leaves it. DRIVEN by `wi1082_…::the_field_tie_is_a_fixpoint`, which type-checks one KB twice
/// and compares the field types.
fn elaborate_self_field_ties(kb: &mut KnowledgeBase, sort_names: &[Symbol]) {
    for &sort in sort_names {
        for ctor in kb.field_constructors_of_sort(sort) {
            let Some(fields) = kb.entity_field_types(ctor) else {
                continue;
            };
            let fields: Vec<(Symbol, Value)> = fields.to_vec();
            let mut changed = false;
            let mut out: Vec<(Symbol, Value)> = Vec::with_capacity(fields.len());
            for (fsym, fty) in fields {
                // Same span/owner reasoning as the return half: read only on
                // `parameterized_value`'s Node branch, which a Term-carried field type cannot
                // reach because the fill is a hash-consed canonical var.
                let (span, owner) = declared_span_owner(kb, &fty, ctor);
                match rigidify_unwritten_sort_params(
                    kb,
                    UnwrittenFill::Anonymous,
                    &fty,
                    SlotPosition::Declared {
                        sort,
                        unbound: None,
                    },
                    span,
                    owner,
                ) {
                    Some(elaborated) => {
                        out.push((fsym, elaborated));
                        changed = true;
                    }
                    None => out.push((fsym, fty)),
                }
            }
            if changed {
                kb.register_entity_field_types(ctor, out);
            }
        }
    }
}

/// WI-1082 — the span/owner a rebuild of a DECLARED type stamps on a `Value::Node` carrier,
/// with `fallback` the declaring symbol (the operation, or the entity constructor).
///
/// An occurrence-carried declaration keeps its OWN node's pair, which is the only case where
/// the answer matters to a reader: `parameterized_value` takes its Node branch whenever any
/// binding is Node-carried, and the `Arrow` / `NamedTuple` arms of the walk build occurrences
/// unconditionally. The fallback is the declaration's own span when the loader recorded one —
/// `functor_span` is written by `create_occurrence`, so only a symbol that heads a stored term
/// has one, which is why this cannot refuse to answer — and [`empty_span`] otherwise. A span
/// off `empty_span` renders as the first loaded file's start, so a diagnostic built on one is
/// the WI-745 misattribution class; it is reachable only for a declaration the loader gave no
/// span AND whose rebuild produced an occurrence, and it is preferred here to silently skipping
/// the tie, which would be a soundness gap rather than a bad location.
fn declared_span_owner(
    kb: &KnowledgeBase,
    declared: &Value,
    fallback: Symbol,
) -> (crate::span::SourceSpan, Option<Symbol>) {
    match declared {
        Value::Node(n) => (n.span, n.owner),
        _ => (
            kb.functor_span(fallback)
                .unwrap_or_else(crate::kb::node_occurrence::empty_span),
            Some(fallback),
        ),
    }
}

/// WI-1082 — DOES this operation have a parameter denoting THIS instance of `sort`?
///
/// A GATE, NOT A SOURCE. The fill is the sort's own parameter var and needs no receiver — what
/// this decides is whether the call can ever BIND that var. `List.insert(c: List, elem: T)`
/// can, through `c` (and through `elem` too, which is the pooling a projection off one chosen
/// receiver would have thrown away). `List.empty()` cannot: with no parameter mentioning the
/// sort, writing the canonical var into its return would stamp a raw, unbindable global into
/// `resolved_ret` — the dangling-flex hazard the WI-374 note names, and the reason WI-1063
/// rejected the canonical var as a general filler. So `empty` keeps its unwritten slot and the
/// caller's `expected` seeding determines it (WI-270).
///
/// THE HEAD, not a nested mention. A parameter that merely CONTAINS the sort (`f: (l: List) ->
/// Bool`) denotes no instance of it; the callback's own `List` is a separate value, and nothing
/// at the call binds this sort's parameter through it.
///
/// THE FIRST is enough, and it is not a choice between rivals: §3 bullet 1 declares every
/// self-sort parameter to be at the SAME instance and WI-374 enforces it, so `append(xs: List,
/// ys: List)`'s two parameters cannot disagree at a call that type-checks. This only ever asks
/// whether at least one exists.
///
/// A GUARD THAT COULD NOT BE DRIVEN, said plainly rather than left to look load-bearing.
/// Removing this gate costs ZERO — the whole `anthill-core` suite stays green and all four
/// corpus tiers load clean — and two purpose-built fixtures failed to reach the hazard it
/// names. It is kept on the WI-1063 / WI-374 argument alone: a result type must not carry a
/// global canonical var. `wi1082_self_return_tie_test::no_self_parameter_leaves_the_slot_open`
/// carries the same statement from the test side, including what would retire it.
fn declares_self_param(kb: &KnowledgeBase, params: &[(Symbol, Value)], sort: Symbol) -> bool {
    let want = kb.canonical_sort_sym(sort);
    params.iter().any(|(_, ty)| {
        sort_functor_of_view(kb, ty).is_some_and(|b| kb.canonical_sort_sym(b) == want)
    })
}

/// WI-1078 — THIS CALL'S OPENING OF THE CALLEE'S UNBOUND RETURN VARIABLES: one fresh
/// `Var::Rigid` per unbound variable, keyed by the variable it stands for. Empty (the
/// overwhelmingly common case) when the declared return has no variable the signature leaves
/// unbound, and then nothing below it behaves differently from WI-1063.
///
/// WHAT WI-1063 LEFT OPEN. Its call-side narrowing reads only an ANONYMOUS slot as unwritten
/// ([`value_is_anonymous_wildcard`]), so its own headline exploit survived writing `E = ?E`
/// where the refused program omitted the slot — `-> Stream[T = Int64, E = ?E]` put `{Error}`
/// into a parameter declaring `E = {}`. `docs/kernel-language.md` §"Sort composition" is
/// explicit that BOTH spellings express existential quantification and that a name buys only
/// binding "across the term", so the exemption had no rule behind it.
///
/// BOUND IS A PROPERTY OF THE SIGNATURE, NOT OF THE SPELLING. A variable the declaration also
/// uses somewhere the CALLER supplies or instantiates is an ordinary universally-quantified
/// parameter and must be left flexible — this call's arguments are what pin it. Three such
/// places, each a real population and each with its own back-out measurement:
///
/// * a PARAMETER type — `interleave(a: LogicalStream[T = ?A, E = ?E], …) -> LogicalStream[T =
///   ?A, E = ?E]`. This is the case the rule exists to separate out; dropping it also costs
///   `wi186_free_standing_parametric_test::make_pair_free_standing_parametric_returns_pair`;
/// * the operation's OWN `[A]` binders — `mk3[A]() -> List[T = A]`, whose §5.6 reading is that
///   the CALLER instantiates `A`. `seed_op_type_args` binds these from an explicit `mk3[A =
///   …]`, and opening one would skolemize a parameter out from under its own inference (the
///   `FilteredStream.splitFirst` failure WI-1063 measured for the broad flex test). Dropping
///   it costs 16 tests across WI-204/236/270/427/734 — much the widest of the three;
/// * a `requires` clause. `-> C requires Monoid[C]` is a universal WITH A BOUND, which is
///   precisely the shape WI-1079 records as `PolyType`'s binder-plus-bound; reading its
///   variable as existential would refuse the dispatch that clause exists to drive.
///
/// The DECLARED EFFECTS are deliberately not a fourth. A row the operation INCURS is on the
/// same side of the arrow as the return — `-> Stream[E = ?E] effects ?E` says "the row I hand
/// back is the row I incur", which relates two positive positions to each other and binds
/// neither. Measured: no corpus declaration ties a return variable to its effect row, so this
/// is a reading rather than a cost.
///
/// ONE RIGID PER VARIABLE, NOT PER SLOT, and that is the half of the rule the NAME earns.
/// `?` is fresh at each occurrence and keeps [`UnwrittenFill::Anonymous`]'s per-slot mint;
/// `mkpair() -> Pair[A = ?t, B = ?t]` states that its two components AGREE, so the opening
/// must preserve that agreement — `Pair[A = ρ, B = ρ]`, one ρ. Keying the map on the
/// VARIABLE, not on the slot, is what makes the tie survive the opening; it is also why the
/// consumer's `wantsame(p: Pair[A = Int64, B = Int64])` is now refused, which is the
/// existential reading applied to a tie rather than a new judgement about ties.
///
/// THE CANDIDATES COME FROM THE DECLARATION, NEVER FROM `ret`, and this is the difference
/// between the rule and a regression. By the time Path 1 calls this, `ret` has been through
/// `eliminate_type_projections` and the WI-459 re-key: `takeN(s: Stream, n: Int64) -> List[T =
/// s.T]` arrives as `List[T = ?x]`, where `?x` is the RECEIVER's variable substituted in. That
/// variable is in no parameter type of `takeN`, so reading candidates off `ret` classifies it
/// unbound and skolemizes the caller's own row — DRIVEN, it is
/// `wi714_relation_reference_test::wi714_cross_sort_rule_body_subgoal`, which fails at
/// `expected List[T = Int64], got List[T = ?x]`. Only a variable the AUTHOR WROTE in the
/// declared return can be the existential this ticket is about; `ret` is consulted solely as
/// the cheap gate that keeps a variable-free result off the signature read.
///
/// The map is keyed on `VarId::raw()` — a `VarId` is not `Hash` — and its values are the
/// minted rigids as [`Value`]s, ready to drop into a binding.
fn unbound_return_var_openings(
    kb: &mut KnowledgeBase,
    callee_op: Symbol,
    ret: &Value,
) -> HashMap<u32, Value> {
    let mut opened = HashMap::new();
    for vid in unbound_return_vars(kb, callee_op, ret) {
        let fresh = kb.fresh_var(vid.name());
        let rigid = kb.alloc(Term::Var(Var::Rigid(fresh)));
        opened.insert(vid.raw(), Value::term(rigid));
    }
    opened
}

/// WI-1078's classification WITHOUT the mint — the variables of `callee_op`'s declared return
/// that its signature leaves UNBOUND. [`unbound_return_var_openings`] opens each to a fresh ρ
/// because a FOREIGN slot's unbound variable is existential; WI-1082 reads the same list at the
/// DECLARATION, where a SELF slot's unbound variable is §3's tie instead. One classification,
/// two answers keyed on self/foreign — which is the split [`SlotPosition`] already is.
///
/// SPLITTING IT IS WHAT KEEPS THE SPELLINGS TOGETHER. `-> MyStream[T = Int64]` and `->
/// MyStream[T = Int64, E = ?E]` are one type (`docs/kernel-language.md` §"Sort composition"),
/// and WI-1078 exists because they had drifted apart at the call. Elaborating only the omitted
/// spelling would re-open that gap from the other end: the omitted one would carry the sort's
/// parameter and the named one a flexible var that unifies with anything.
fn unbound_return_vars(kb: &KnowledgeBase, callee_op: Symbol, ret: &Value) -> Vec<VarId> {
    // No variable survives into this call's result, so no slot below can match one. Nearly
    // every call in the corpus stops here, which is what keeps the signature read off the hot
    // path.
    let mut in_result: Vec<VarId> = Vec::new();
    let mut seen = HashSet::new();
    crate::kb::node_occurrence::collect_value_type(kb, ret, &mut in_result, &mut seen);
    if in_result.is_empty() {
        return Vec::new();
    }
    let Some(op) = lookup_operation_info_full(kb, callee_op) else {
        // No readable signature, so no variable can be SHOWN unbound. WI-1063's reading
        // stands for this call; it is the answer that changes nothing, which is the right one
        // when the evidence the rule runs on is absent.
        return Vec::new();
    };
    // ONE WALK ANSWERS BOTH SIDES, and it is the walk the `close`/`open`/σ rewriters already
    // use ([`collect_value_type`], WI-378). The first cut hand-rolled a second one over the
    // `TypeNode` arms and lost two carriers it does not look like it would: a `NamedTuple`'s
    // `fields` ride a `Value::Entity` cons-list, and a `Denoted` payload is an Expr spine. A
    // variable missed in the RETURN merely leaves that slot alone, but one missed in a
    // PARAMETER reads a BOUND variable as existential and skolemizes it — so the two must not
    // be able to disagree, and now they cannot.
    let mut candidates: Vec<VarId> = Vec::new();
    let mut seen = HashSet::new();
    crate::kb::node_occurrence::collect_value_type(kb, &op.return_type, &mut candidates, &mut seen);
    let bound = signature_bound_vars(kb, callee_op, &op.params, &op.requires, &op.type_params);
    let mut unbound = Vec::new();
    for vid in candidates {
        if bound.iter().any(|b| b.raw() == vid.raw()) {
            continue;
        }
        // Only a variable that actually SURVIVES into this call's result can reach a slot, so
        // one that the elimination already substituted away costs no mint. A rigid is interned
        // for the KB's lifetime, and this runs per call.
        if !in_result.iter().any(|r| r.raw() == vid.raw()) {
            continue;
        }
        // An ANONYMOUS carrier keeps its per-SLOT mint below — `?` names nothing and ties
        // nothing, so giving it a per-VARIABLE entry here would be the one case where the
        // sharing this map exists for is wrong. (It would also be invisible on the parser's
        // carrier, where every bare `?` is already its own `VarId`; it is `?_`, a scope-SHARED
        // var the parser and [`value_is_anonymous_wildcard`] both read as anonymous, that the
        // distinction is actually about.) Shared predicate, for the reason stated there.
        if anonymous_var_name(kb, vid.name()) {
            continue;
        }
        unbound.push(vid);
    }
    unbound
}

/// WI-1078's BOUND SET, given its own name by WI-1083 because a second consumer arrived
/// and the two must not be able to disagree: the variables `callee_op`'s SIGNATURE binds
/// — the ones the CALLER supplies or instantiates, as opposed to the existentials
/// [`unbound_return_vars`] opens.
///
/// THE THIRD CONSUMER IS THE BODY (WI-1FKR2), and it is what makes "caller supplies or
/// instantiates" bite on the implementation side: a variable this set names is universally
/// quantified, so [`check_operation_bodies`] SKOLEMIZES it exactly as WI-392 skolemizes an
/// `[A]` binder — the body must hold for every instantiation. Takes the signature as SLICES
/// rather than an [`OperationInfoFull`] only because that consumer holds an
/// `OpInfoRecord`; the fields are the same three.
///
/// THE TWO QUESTIONS ARE ONE QUESTION, AND THAT IS THE POINT. Read negatively it says
/// which return variables are existential (WI-1078). Read positively it says which
/// variables a ∀ over this signature quantifies — the binder list of the [`TypeExtractor
/// ::PolyType`] the eta lift mints. WI-1079's hand-over to WI-1083 asked exactly this
/// ("WHO GENERALIZES, AND WHEN"), and warned that a binder list read as *only* an
/// operation's own `[A]` would classify `mplus(a: LogicalStream[?A], b: LogicalStream[?A])
/// -> LogicalStream[?A]` — whose `type_params` is EMPTY — as unbound and refuse a program
/// that loads today. It does not, because the ∀'s binders ARE this set: generalization
/// happens HERE, at the eta lift that consumes it, and nowhere else.
///
/// FOUR SOURCES, each measured on WI-1078 / WI-1082 and documented in
/// [`unbound_return_vars`]'s own header: a PARAMETER type, a `requires` clause, the
/// operation's own `[A]` binders, and — since WI-1082 elaborates an elided self slot to
/// it — the DECLARING SORT's canonical parameter. The declared EFFECTS are deliberately
/// not a fifth: a row the operation incurs sits on the same side of the arrow as the
/// return and binds nothing.
///
/// A VARIABLE SHARED ACROSS TWO DECLARATIONS costs this function nothing, which is the
/// other half of WI-1079's question. The set is per-operation and its consumers only ever
/// build a substituted COPY (`instantiate_poly_type` maps each binder to a fresh var
/// rather than binding it), so a `VarId` another declaration also mentions is never
/// written through. Measured anyway: the loader mints a distinct `VarId` per declaration
/// even for one spelling — `idp[A]` and `pair2[A, B]` get different ids for the same
/// `Symbol`.
pub(super) fn signature_bound_vars(
    kb: &KnowledgeBase,
    callee_op: Symbol,
    params: &[(Symbol, Value)],
    requires: &[Value],
    type_params: &[(Symbol, Var)],
) -> Vec<VarId> {
    let mut bound: Vec<VarId> = Vec::new();
    let mut seen = HashSet::new();
    for (_, ty) in params {
        crate::kb::node_occurrence::collect_value_type(kb, ty, &mut bound, &mut seen);
    }
    for r in requires {
        crate::kb::node_occurrence::collect_value_type(kb, r, &mut bound, &mut seen);
    }
    // DEDUPED THROUGH THE SAME `seen` the walks above use, which the WI-1078 reading did not
    // need and this one does: `idp[A](x: A) -> A` reaches both sources with ONE variable, and
    // a MEMBERSHIP test cannot tell a doubled entry from a single one while a BINDER LIST can
    // — `∀A, A. …` is not a type. Driven by
    // `wi1083_poly_type_tests::a_type_parameterized_operation_lifts_to_a_forall…`, which
    // asserts the binder count.
    for (_, v) in type_params {
        if let Var::Global(vid) = v {
            if seen.insert(vid.raw()) {
                bound.push(*vid);
            }
        }
    }
    // THE DECLARING SORT'S OWN PARAMETERS ARE A FOURTH ENTRY, and WI-1082 is what put them
    // there. WI-1078 measured this list as unreachable and dropped it, correctly at the time: a
    // sort parameter a HUMAN writes in a type is a `Ref` to its own symbol, never a
    // `Var::Global`, so `to_pair(h: Holder) -> Pair[A = T, B = T]` arrived variable-free. But
    // WI-1082 rewrites an elided self slot to that sort's canonical VAR, so every elaborated
    // member now reaches here with one — and it is bound by construction: it is the §3 tie, the
    // thing this call's arguments pin through the canonical channel, not an existential. Left
    // out, every call to `List.insert` / `Map.put` / a `cons` would mint a `Var::Rigid` — which
    // is interned for the KB's LIFETIME — that `SlotPosition::fill_self` then discards unused,
    // and the cheap `in_result.is_empty()` gate that keeps this whole signature read off the hot
    // path would stop firing for them.
    if let Some(parent) = impl_parent_sort_of_op(kb, callee_op) {
        for (_, canonical) in sort_type_params_as_pairs(kb, parent).iter() {
            if let Term::Var(Var::Global(vid)) = kb.get_term(*canonical) {
                if seen.insert(vid.raw()) {
                    bound.push(*vid);
                }
            }
        }
    }
    bound
}

/// WI-1063 — WHICH POSITION [`rigidify_unwritten_sort_params`] is walking. The walk itself is
/// one rule read at two polarities (a parameter's unwritten slot is universal and rigid in the
/// BODY; a return's is existential and rigid at the CALL), and everything the two positions
/// disagree about is here.
///
/// THE WHOLE POLICY IS ONE 3×2 TABLE — [`Self::fill_self`] × [`Self::fill_foreign`] — and each
/// cell has a corpus measurement behind it rather than a symmetry argument. The cells are
/// documented at their own arms; the table is here so that "which position leaves what" can be
/// read in one place:
///
/// | position | a SELF-sort slot | a FOREIGN-sort slot |
/// |---|---|---|
/// | [`Body`](Self::Body) | the enclosing sort's rigid (WI-424) | [`UnwrittenFill`]'s mint |
/// | [`Declared`](Self::Declared) | the sort's own parameter var — §3's tie, written down (WI-1082) | LEFT — opening once per DECLARATION would share one ρ across every call |
/// | [`CallResult`](Self::CallResult) | LEFT — `Declared` already wrote it, or the callee has no self parameter to bind it | a fresh ρ, the existential opening (WI-1063) |
///
/// WHICH SLOTS EACH CONSIDERS IS *NOT* A DISAGREEMENT, and keeping that so is load-bearing:
/// `Declared` and `CallResult` ask the identical two-part question
/// ([`Self::written_slot_is_unwritten`]) so that `-> S[E = ?E]` and `-> S` stay ONE type. They
/// differ only in the answer.
#[derive(Clone, Copy)]
pub(super) enum SlotPosition<'a> {
    /// The operation's own BODY (WI-1059/WI-1061). `sort` is the enclosing sort and
    /// `rigidify` the WI-424 substitution that skolemized its parameters.
    Body {
        sort: Option<Symbol>,
        rigidify: &'a Substitution,
    },
    /// WI-1082 — a DECLARATION as written by the author: an operation's return type or an
    /// entity's field type, rewritten ONCE by [`elaborate_self_ties`] before any body check or
    /// call site reads it. `sort` is the sort the declaration belongs to.
    ///
    /// `unbound` says which NAMED variables count as unwritten, and its two states are the two
    /// kinds of declaration. `Some(set)` is a SIGNATURE position (a return, a parameter):
    /// [`unbound_return_vars`]' classification, so `-> S[E = ?E]` is the same slot as an
    /// omitted `E` while a variable the signature binds elsewhere is left alone. `None` is an
    /// ENTITY FIELD, which has no signature at all — no parameter list, no `[A]` binders, no
    /// `requires` chain — so nothing can bind a variable written there and EVERY flexible one
    /// is unwritten. Reading a field's `Box[T = ?X]` as bound would split it from `Box` and
    /// `Box[T = ?]`, which are the same type.
    Declared {
        sort: Symbol,
        unbound: Option<&'a [u32]>,
    },
    /// One CALL's result (WI-1063). `callee_sort` is the CALLEE's own sort; `opened` is
    /// WI-1078's per-call opening of the declared return's UNBOUND named variables, built
    /// once by [`unbound_return_var_openings`] and empty whenever the signature binds them
    /// all.
    CallResult {
        callee_sort: Option<Symbol>,
        opened: &'a HashMap<u32, Value>,
    },
}

impl SlotPosition<'_> {
    /// The sort a reference must name to count as SELF here.
    fn self_sort(self) -> Option<Symbol> {
        match self {
            SlotPosition::Body { sort, .. } => sort,
            SlotPosition::Declared { sort, .. } => Some(sort),
            SlotPosition::CallResult { callee_sort, .. } => callee_sort,
        }
    }

    /// What an unwritten slot on a SELF reference takes, or `None` to leave it unwritten.
    /// `canonical` is that sort's own canonical parameter var (the `SortAlias` target) — which
    /// two of the three positions answer with directly, one rigidified and one raw.
    ///
    /// THE BODY knows the instance: the canonical var run through the rigidify substitution,
    /// so the slot holds the same skolem every other mention of that parameter in this body
    /// already resolves to.
    ///
    /// A DECLARATION knows it too, and says so with the sort's OWN parameter (WI-1082).
    /// `docs/design/type-parameter-scoping.md` §3 bullet 1 gives both halves verbatim: a bare
    /// self-sort reference inside the sort's own definition ties the parameters AND THE RETURN
    /// to *this* sort's parameter, and `cons(head: T, tail: List)` ⇒ `tail` is a `List` of
    /// *this* sort's `T`. So `insert(c: List, elem: T) -> List` means `-> List[T = T]` and the
    /// cons cell's tail means `List[T = T]` — the spelling the sibling `head: T` already uses,
    /// and the one `SortedSet.insert(s: SortedSet[T = T, O = O], x: T) -> SortedSet[T = T, O =
    /// O]` writes out by hand. Writing it makes the tie a BINDING instead of an absence, and an
    /// absence is what laundered: a missing binding is width-ignored by
    /// `unify_parameterized_view`, so nothing was ever claimed about the slot and nothing could
    /// refute a consumer's demand.
    ///
    /// NOT THE RECEIVER'S PROJECTION, which was tried first and measured wrong. `-> List[T =
    /// c.T]` is the same type wherever both can answer (in a body `c : List[T = ?T]`, so `c.T`
    /// reduces to the sort's rigid), but it reads ONE parameter where the tie pools ALL of
    /// them: `put(empty(), "a", 1)` has no stable receiver to project off, so `Map.put` came
    /// back as an un-eliminated `Map[K = m.K, V = m.V]` while `key: K` and `value: V` bind the
    /// very same canonical vars the tie wants. Writing a projection there also flipped
    /// `op_has_projection` on for the whole call, which then failed `put`'s own PARAMETERS at
    /// `expected m.K, got Int64`. The canonical var perturbs no call path — it is what the
    /// signature already rides.
    ///
    /// A CALL MUST NOT INVENT ONE, and leaves it — the same decision
    /// [`expand_foreign_sort_application`] takes on the parameter side and for the same
    /// reason: the callee's own sort rides the canonical channel, where THIS call's argument
    /// unification binds it (`type-parameter-scoping.md` §3 bullet 1). Both other answers are
    /// wrong and both are reachable from this arm if it ever grows one — a fresh skolem would
    /// refuse `takes_int(reverse(xs))` for every self-returning member in the stdlib, and the
    /// canonical var itself would stamp a dangling FLEX var into `resolved_ret` for an
    /// argument-less `List.empty()`, the hazard the WI-374 note at the parameter expansion
    /// names.
    ///
    /// WHAT STILL REACHES THAT ARM after WI-1082, and it is the residue that ticket left
    /// open rather than an unmeasured gap: an operation with NO parameter denoting its own
    /// instance — `List.empty() -> List`, `Map.empty() -> Map` — has nothing at the call to
    /// bind the sort's parameter, so its return keeps the unwritten slot and the caller's
    /// `expected` seeding determines it (WI-270's legitimate case). That is the right answer
    /// for `empty`, whose body holds for every `T`, and the WRONG one for a hypothetical
    /// `mk() -> MyStream[T = Int64]` whose body pins a row; the two are indistinguishable
    /// without the universal spelling (`empty[T]() -> List[T = T]`), which is **WI-1083**'s
    /// `PolyType`. See [`declares_self_param`] for why writing the canonical var there anyway
    /// is worse than leaving the slot.
    fn fill_self(self, kb: &mut KnowledgeBase, canonical: TermId) -> Option<Value> {
        match self {
            SlotPosition::Body { rigidify, .. } => {
                Some(Value::term(walk_type_deep(kb, rigidify, canonical)))
            }
            // THE ENTITY-FIELD HALF IS NOT A SECOND RULE, and it is not optional either.
            // `case cons(x, rest)` binds `rest` at the DECLARED field type, so an untied
            // `tail: List` handed the body a tail with NO element. That was invisible while
            // `append`'s return was the erased `-> List` (claiming nothing); the moment the
            // return states the tie, the recursive `append(rest, ys)` comes back at `rest`'s
            // element and the `cons` rebuilding the spine reports the tie as inconsistent —
            // measured, the single error the whole corpus raised. The stdlib had been working
            // around the same loss in four places ("a bare `cons` tail is untyped `List` and
            // would lose `xs.T`" — `foldLeft`, `foldRight`, `nth`, `mapElems`, each recursing
            // via `splitFirst` and each saying why); those keep working unchanged, and `append`
            // keeps its natural `match xs` / `cons` destructure.
            SlotPosition::Declared { .. } => Some(Value::term(canonical)),
            SlotPosition::CallResult { .. } => None,
        }
    }

    /// WI-1082 — [`Self::fill_self`]'s other half: what an unwritten slot on a FOREIGN sort
    /// reference takes, or `None` to leave it unwritten. Two of the three positions answer
    /// with [`UnwrittenFill`]'s mint, which is why this was a bare `fill.mint` call until the
    /// third arrived.
    ///
    /// THE DECLARED RETURN LEAVES IT, and that is a soundness constraint rather than a
    /// deferral. A foreign unwritten slot in a return IS the existential WI-1063 opens, and
    /// its own doc states that "freshness per opening is the soundness, not an implementation
    /// detail — two calls may genuinely return different rows". This position runs ONCE PER
    /// DECLARATION; opening here would mint one ρ and share it across every call of the
    /// operation, relating results that have nothing to do with each other. So the slot stays
    /// as the author left it and [`SlotPosition::CallResult`] opens it per call, exactly as
    /// before this ticket.
    fn fill_foreign(
        self,
        kb: &mut KnowledgeBase,
        fill: UnwrittenFill,
        param: Symbol,
    ) -> Option<Value> {
        match self {
            SlotPosition::Body { .. } | SlotPosition::CallResult { .. } => {
                Some(fill.mint(kb, param))
            }
            SlotPosition::Declared { .. } => None,
        }
    }

    /// Does a slot the author DID write nevertheless count as unwritten here? Both positions
    /// answer yes for the same reason — kernel-language §"Expansion during unification" says
    /// spelling a slot `?` means exactly what omitting it means — and they disagree only about
    /// which carriers can still be an author's `?` by the time the walk sees them.
    ///
    /// IN THE BODY, ANY STILL-FLEXIBLE VARIABLE IS ONE. That is WI-1056's four-spellings
    /// agreement: by then the op's own `[E]` and its enclosing sort's parameters are already
    /// `Var::Rigid` (WI-392/WI-942), so nothing else is left flexible.
    ///
    /// AT A CALL, THE BROAD TEST WOULD READ THE OPPOSITE FACT, so this asks a narrower
    /// question in two parts. The signature a call site sees is the KB's `OperationInfo`,
    /// where NOTHING has been rigidified: the op's `[Elem]`, the enclosing sort's parameters,
    /// and a `s.T` projection already eliminated against the receiver are all still flexible
    /// Globals, and they are precisely the slots this call is about to BIND. MEASURED, and it
    /// is why this is a policy and not a shared constant: with the body's answer here the
    /// stdlib reports `FilteredStream.splitFirst`'s `Pair[A = Elem]` re-minted as an unrelated
    /// `Pair[A = ?A]` — the op's own type parameter skolemized out from under its own
    /// inference.
    ///
    /// The two parts are an ANONYMOUS carrier — `Stream[T = Int64, E = ?]`, which pins nothing
    /// anywhere — and WI-1078's UNBOUND NAMED one: a variable this signature uses ONLY in its
    /// return, which is the existential the polarity rule describes and which WI-1063's
    /// anonymous-only reading let through. A named variable can be TIED across slots
    /// (`Pair[A = ?t, B = ?t]` says "these two agree, whatever they are"), and the tie
    /// survives — [`unbound_return_var_openings`] keys its mint on the VARIABLE, so both slots
    /// take one ρ. What does NOT reach this arm is a variable the signature binds elsewhere
    /// (a parameter, an `[A]` binder, a `requires` bound); that map is empty of it, and
    /// [`merge_annotation_bindings`] replaces only the anonymous spelling for the same reason.
    fn written_slot_is_unwritten(self, kb: &KnowledgeBase, v: &Value) -> bool {
        match self {
            SlotPosition::Body { .. } => value_is_flex_var(kb, v),
            // WI-1082 — the same two-part question [`SlotPosition::CallResult`] asks, and
            // deliberately the same shape: an ANONYMOUS carrier, or a NAMED variable this
            // signature leaves unbound. The two positions differ in the ANSWER (a self slot is
            // the tie here, an existential there), never in which slots they consider — see
            // [`unbound_return_vars`].
            SlotPosition::Declared { unbound, .. } => match unbound {
                Some(set) => {
                    value_is_anonymous_wildcard(kb, v)
                        || value_flex_var_id(kb, v).is_some_and(|vid| set.contains(&vid.raw()))
                }
                // An entity field: nothing here can bind a variable, so every flexible one is
                // unwritten. Same answer the BODY position gives, for the same reason.
                None => value_is_flex_var(kb, v),
            },
            SlotPosition::CallResult { opened, .. } => {
                value_is_anonymous_wildcard(kb, v)
                    || value_flex_var_id(kb, v).is_some_and(|vid| opened.contains_key(&vid.raw()))
            }
        }
    }

    /// WI-1078 — the rigid THIS call opened `v`'s variable to, when `v` is one of the callee's
    /// unbound named return variables. `None` everywhere else, and the fill falls back to
    /// [`UnwrittenFill`]'s per-slot mint — which is what an anonymous `?` and an omitted slot
    /// both want, since neither names anything to share with.
    fn opened_named_var(self, kb: &KnowledgeBase, v: &Value) -> Option<Value> {
        let SlotPosition::CallResult { opened, .. } = self else {
            return None;
        };
        opened.get(&value_flex_var_id(kb, v)?.raw()).cloned()
    }
}

/// WI-1061 — WHERE in a signature an unwritten slot sits, which is the whole of what decides
/// how it is FILLED. One enum rather than a `bool`, because the two arms are not more/less of
/// one thing: one names the slot, the other cannot.
#[derive(Clone, Copy)]
pub(super) enum UnwrittenFill {
    /// The TOP LEVEL of a PARAMETER's declared type, carrying that parameter's name. The
    /// slot takes the projection off the value that carries it — `s: Stream[T = Int64]` is
    /// checked as `s: Stream[T = Int64, E = s.E]`.
    ///
    /// THE PROJECTION, NOT A FRESH VAR, and this is the WI-1059 design. A fresh rigid per
    /// slot is sound but ANONYMOUS: nothing else can name it. The stdlib names these
    /// parameters constantly — `operation collect(s: Stream) -> List[T = s.T]` — and `s.T`
    /// is already a RIGID neutral (WI-400 ζ: "its own rigid type, equal only to an identical
    /// neutral, never to a concrete type"). Minting a fresh var instead desynchronizes the
    /// two: the body's `s` would carry `T = ?T₁` while the declared return still said `s.T`,
    /// and the pair no longer matches. MEASURED — the fresh-var cut cost 27 stdlib load
    /// errors, almost all of the shape `expected List[T = s.T], got List[T = ?T]`, and not
    /// one of them was a wrong program.
    Projection(Symbol),
    /// A slot NESTED inside a written binding. A fresh anonymous `Var::Rigid`, one per slot.
    ///
    /// NOT A CHOICE — nothing can name a nested slot. `l: List[T = Stream]` writes `List`'s
    /// `T` and leaves `Stream`'s own parameters open, and the language does not spell the
    /// inner row: there is no `l.T.E`. So [`Projection`](Self::Projection) is simply
    /// unavailable, and the anonymity that made it the wrong filler at top level is not a
    /// cost that can be avoided here.
    ///
    /// THE DESYNC IT WAS FEARED TO CAUSE CANNOT ARISE, which is what makes this arm safe
    /// where the same anonymity was wrong at top level. At top level the anonymity broke a
    /// signature that had ALREADY NAMED the slot (`-> List[T = s.T]` reading the parameter's
    /// own `T`), so two spellings of one thing stopped matching. A nested slot is named by
    /// nothing anywhere in the signature — there is no second reading to desynchronize FROM —
    /// and a SELF reference, the one nested thing that IS named elsewhere, never reaches this
    /// arm.
    ///
    /// THE COST MEASUREMENT WI-1061 WAS OPENED FOR, and it has two halves that must be read
    /// together. Over stdlib, host bindings (`anthill-stl`), `rustland/anthill-todo/anthill`,
    /// `rustland/anthill-cpp-gen/anthill`, `examples/`, `anthill-todo/` and
    /// `anthill-testcases/`, this arm costs ZERO — every tier loads with the same error count
    /// and the same fact/rule totals as before the change, and the whole workspace suite is
    /// green. But it is also reached ZERO times: counted at the mint, the corpus's only
    /// nested unwritten slot is `MappedStream.splitFirst`'s, a SELF reference that takes the
    /// sort's own rigid instead. So "the corpus loads clean" is evidence that this arm breaks
    /// nothing, and NOT evidence that its filler is cheap — the corpus does not contain the
    /// shape. What drives it is `wi1061_unwritten_slot_positions_test`; that file is the only
    /// coverage this arm has.
    ///
    /// The enum keeps two arms although one call site supplies each, because the RETURN
    /// position (WI-1063) is a third caller of this same walk under this same arm, and it was
    /// built and measured before being held back — see the caller's block comment.
    Anonymous,
}

impl UnwrittenFill {
    /// Mint this position's filler for one unwritten parameter `param`.
    fn mint(self, kb: &mut KnowledgeBase, param: Symbol) -> Value {
        // Both arms name the result after the parameter's SHORT name (`E`, not
        // `Stream.E`) — the projection because that is the member spelling a hand-written
        // `s.E` produces, the rigid because a skolem's identity is its fresh `VarId` and the
        // name is only what the diagnostic prints (`?E` beats `?_`).
        let short = short_name_of(kb.local_name_of(param)).to_owned();
        let member = kb.intern(&short);
        match self {
            // Built byte-identically to the loader's `s.E` — `make_expr_carried(Ref(recv),
            // intern(short))` — and keyed by the carrier's own `<sort>.<P>` symbol, so it is
            // the same neutral a hand-written `s.E` produces and compares to one by path
            // identity.
            //
            // BARE, INCLUDING FOR AN EFFECT-ROW PARAMETER — the single-label row `{s.E}` an
            // effect slot ultimately wants is wrapped where the receiver is CONSUMED
            // ([`bare_spec_arg_self_projection`]), not here. Wrapping it at the fill was
            // tried and reverted: the row makes the slot's value strictly LARGER than the
            // projection it contains, so the author-projection fixpoint in
            // `check_operation_bodies` re-wraps every round (`{s.E}`, `{{s.E}}`, …) and
            // never converges — measured as a stack overflow on a program as small as
            // `operation ok(s: Stream[T = Int64]) -> Int64 = 1`. Keeping the fill bare is
            // also what lets [`is_self_projection_of`] recognize a materialized receiver by
            // shape; a wrapped fill would silently stop matching there and disable the
            // WI-594 effect threading.
            UnwrittenFill::Projection(recv_name) => {
                let recv = kb.alloc(Term::Ref(recv_name));
                Value::term(kb.make_expr_carried(recv, member))
            }
            // The same mint as [`rigidify_op_type_params`], which is the point: a slot the
            // author left unwritten and a slot they declared as the op's own `[E]` are the
            // same universally-quantified variable, so the body must see the same KIND of
            // skolem for both. `wi1059_unwritten_param_rigid_test` pins that agreement from
            // the other side (its `feed[E]` row and its `Stream[T = Int64]` row refuse
            // alike, differing only in what the message prints).
            UnwrittenFill::Anonymous => {
                let fresh = kb.fresh_var(member);
                Value::term(kb.alloc(Term::Var(Var::Rigid(fresh))))
            }
        }
    }
}

/// Is this type value a still-FLEX logical variable — the carrier an explicit `?` in a type
/// binding takes? A `Var::Rigid` answers `false`: it is a skolem the op's own `[E]` or its
/// enclosing sort's parameter already pinned, and re-spelling it as a projection would
/// rename a variable the rest of the signature refers to.
fn value_is_flex_var(kb: &KnowledgeBase, v: &Value) -> bool {
    value_flex_var_id(kb, v).is_some()
}

/// The same question as [`value_is_flex_var`] with the variable's IDENTITY kept, which is what
/// WI-1078 keys its per-call opening on. A name would not do: two distinct `?A`s in two
/// declarations share a name and nothing else, and a rigid's own doc says its identity is its
/// fresh `VarId`.
///
/// Deliberately NOT reading a `TypeExtractor::TypeVar` carrier, which
/// [`value_is_anonymous_wildcard`] does read: that spelling carries a NAME AND NOTHING ELSE,
/// so there is no `VarId` to answer with. A reflect-minted type var therefore keeps WI-1063's
/// behaviour — the anonymous test still sees it, and a named one is left alone.
///
/// ASKED THROUGH [`extract_type`], NOT BY MATCHING CARRIERS (WI-1079). The first cut wrote the
/// two carriers out by hand — `Value::Term{Term::Var(Global)}` and `Value::Var(Global)` — as
/// the sibling [`value_contains_rigid`] used to for the rigid half, and for the same reason:
/// the boundary could not answer. It can now, and the hand-rolled version was not merely a
/// duplicate but NARROWER — it had no `Value::Node` arm, while an occurrence carrying
/// `Expr::Var(Global)` heads as `ViewHead::Var` and so IS a flexible variable. That gap was
/// one-directional and silent: a slot on the Node carrier answered "not a variable", so
/// [`value_is_anonymous_wildcard`] declined it and the WI-1063/WI-1078 opening did not fire
/// for that spelling.
fn value_flex_var_id(kb: &KnowledgeBase, v: &Value) -> Option<VarId> {
    match extract_type(kb, v) {
        TypeExtractor::FlexVar { name, id } => Some(VarId::new(id, name)),
        _ => None,
    }
}

/// WI-1063 — is `v` spelled with the ANONYMOUS variable name (`Stream[T = ?]`), the written
/// slot that pins nothing? The narrow half of [`value_is_flex_var`]: a NAMED variable
/// (`Pair[A = ?t, B = ?t]`, `LogicalStream[?A]`) is excluded, because a name can TIE two slots
/// and replacing it would lose a relation the author wrote.
///
/// TWO CARRIERS SPELL THE SAME `?` AND BOTH ARE READ HERE, which is the whole reason this is
/// a named predicate rather than an inline match. The PARSER mints one as a fresh
/// `Var::Global` whose name symbol is `_` (`convert_variable_node`'s bare-`?` branch); the
/// REFLECT/`type_var` carrier spells it as a [`TypeExtractor::TypeVar`] named `?` or `?_`. A
/// check that read one and not the other would close a hole in one spelling of one type and
/// leave it open in the other, silently — the failure mode WI-1016 names.
///
/// WHAT IT TESTS IS THE NAME, NOT PROVABLE ANONYMITY, and the difference is real enough to
/// write down (WI-1063 owns it; there is no corpus population to measure it against — the
/// seven tiers contain ZERO anonymous wildcard type bindings). The symbol `_` has three
/// producers, and the parser gives two of them the SAME symbol, so no test on this value can
/// separate them:
///
/// * bare `?` — fresh per occurrence, ties nothing. The case this predicate is for.
/// * `?_` — `convert_variable_node` takes its NAMED branch (`text.len() > 1`) and interns the
///   text after the `?`, which is `_`: a scope-SHARED var, so `Pair[A = ?_, B = ?_]` is a tie
///   and opening it would break exactly what the paragraph above says must not break. It is
///   indistinguishable here, and it was already read as anonymous by the annotation-merge
///   site below before this ticket.
/// * `fresh_anon_type_var`, which interns `_` for the DEFINITION of `sort T = ?`. That
///   definition reaches a type slot as the sort's canonical `SortAlias` target, not as this
///   carrier — a written sort parameter arrives resolved, and its tie survives.
pub(super) fn value_is_anonymous_wildcard(kb: &KnowledgeBase, v: &Value) -> bool {
    // BOTH SPELLINGS THROUGH ONE BOUNDARY (WI-1079). The `_` arm used to write the parser's
    // two carriers out by hand and so missed the third — a `Value::Node` occurrence carrying
    // `Expr::Var(Global)`, which heads as `ViewHead::Var` and is a flexible variable like any
    // other. `extract_type` reads all three, which is the point of it.
    let name = match extract_type(kb, v) {
        TypeExtractor::TypeVar(n) => n,
        TypeExtractor::FlexVar { name, .. } => name,
        _ => return false,
    };
    anonymous_var_name(kb, name)
}

/// The NAME half of [`value_is_anonymous_wildcard`], for the one reader that already holds a
/// variable rather than a carrier ([`unbound_return_var_openings`]).
///
/// ONE PREDICATE BECAUSE A DIVERGENCE HERE IS SILENT AND ONE-DIRECTIONAL. WI-1078 keys a
/// per-VARIABLE opening on this test and the slot walk keys a per-SLOT one on the function
/// above; a spelling added to only one of them would give a variable BOTH answers, and the
/// per-variable entry wins ([`SlotPosition::opened_named_var`] is consulted before
/// [`UnwrittenFill::mint`]). Two independent `?`s in one return would then share one ρ — the
/// exact tie the map's own doc says must never be invented.
fn anonymous_var_name(kb: &KnowledgeBase, name: Symbol) -> bool {
    matches!(kb.local_name_of(name), "_" | "?" | "?_")
}

/// WI-1FKR2 — the canonical type-param vars of EVERY sort lexically enclosing `op_sym`, not
/// only its immediate parent. Feeds [`inline_signature_type_params`]' exclusion set, which
/// must never mistake an OUTER instance's parameter for one of this operation's own: the two
/// halves of [`TypingEnv::param_rigids`] mean different things, and an outer parameter placed
/// in the op half would drop out of [`TypingEnv::enclosing_instance_param_rigids`].
///
/// NOT DRIVEN, and the honest reason: the shape needs an outer sort's canonical var to reach
/// a nested member's signature as a `Var::Global`, and nothing produces one. A human writes
/// such a parameter as a `Ref` to its symbol ([`signature_bound_vars`]' own header states
/// this), and WI-1082's elaboration fills only a SELF slot — `SlotPosition::fill_foreign`
/// returns `None` at a declaration, so `grab(o: Outer)` inside `sort Outer.Inner` arrives
/// variable-free. MEASURED by instrumenting the caller: over that fixture the only variable
/// reaching it is the author's own `?` in `grab2(o: Outer[A = ?])`, which the anonymous filter
/// removes for its own reason.
///
/// It is here because the alternative was relying on that: `/code-review` observed that an
/// outer param would ALSO be filtered as anonymous — `sort A = ?` aliases to a `?`-named var —
/// which is a coincidence of an unrelated mint's naming, not a rule. This makes the exclusion
/// structural. The walk is the qualified-name prefix chain, the same decomposition
/// [`impl_parent_of_op`] does one step of.
fn enclosing_sort_param_vars(kb: &KnowledgeBase, op_sym: Symbol) -> Vec<u32> {
    let qn = kb.qualified_name_of(op_sym).to_owned();
    let mut out = Vec::new();
    let mut scope = qn.as_str();
    while let Some((parent, _)) = scope.rsplit_once('.') {
        scope = parent;
        let Some(sym) = kb.try_resolve_symbol(parent) else {
            continue;
        };
        if !kb.has_kind(sym, crate::intern::SymbolKind::Sort) {
            continue;
        }
        for (_, t) in sort_type_params_as_pairs(kb, sym).iter() {
            if let Term::Var(Var::Global(vid)) = kb.get_term(*t) {
                out.push(vid.raw());
            }
        }
    }
    out
}

/// WI-1FKR2 — THE THIRD FAMILY OF TYPE PARAMETERS AN OPERATION BODY IS CHECKED UNDER: the
/// logical variables the author WROTE INLINE in the signature (`operation via(b: Box[?t]) ->
/// Box[?t]`), which no `[A]` bracket and no enclosing sort declares. §5.4 "Which variables the
/// ∀ quantifies" states they are quantified — "an operation that writes no brackets at all
/// still generalizes" — and [`signature_bound_vars`] is that set; this is the part of it the
/// two families the caller already rigidifies (`rec.type_params`, the enclosing sort's) do not
/// cover, returned in the `(name, var)` shape [`rigidify_op_type_params`] takes.
///
/// WITHOUT IT NO GENERIC OPERATION CAN BE IMPLEMENTED IN TERMS OF ANOTHER, and the two ways
/// it failed are one root. An inline variable stayed a FLEXIBLE `Var::Global` in the body,
/// which (a) made [`SlotPosition::written_slot_is_unwritten`]'s body answer —
/// [`value_is_flex_var`], whose whole justification is that by then "nothing else is left
/// flexible" — read the author's own `?t` as an UNWRITTEN slot and overwrite it with
/// [`UnwrittenFill::Projection`]'s `b.T`, so the parameter and the return stopped naming one
/// variable (`expected Box[T = ?t], got Box[T = b.T]`); and (b) left the bare form `-> ?t` as
/// two distinct flex Globals at the top level, where [`types_compatible`] has no variable arm
/// at all and the identical rendering was the whole diagnostic (`expected ?t, got ?t`).
/// Skolemizing restores that justification's premise rather than adding a case to either
/// reader.
///
/// ANONYMOUS VARIABLES ARE EXCLUDED, and that is the same call [`unbound_return_vars`] makes
/// for the same reason: `?` names nothing and ties nothing, so it IS the unwritten slot
/// kernel-language §"Expansion during unification" describes, and it must keep taking the
/// projection fill. Only a NAME can be the tie this function exists to preserve.
///
/// THE `requires` SOURCE IS DELIBERATELY NOT READ, and that is the one place this question
/// and [`signature_bound_vars`]' differ — passed as an EMPTY slice rather than forked into a
/// second walk, so the three sources they DO share cannot drift. §5.4 states why the source
/// is not one thing: an operation's `requires` list holds **two kinds of item**, a TYPE
/// precondition (`requires Ord[T]`, whose variable is a type parameter) and a VALUE
/// precondition (`requires p(x, ?v)`, whose variable is a precondition existential and names
/// no type at all), and `OpInfoRecord::requires` carries both — mixed within one clause, since
/// §5.4's split is per CONJUNCT. Reading the field whole would mint a KB-lifetime `Var::Rigid`
/// for a value-precondition variable and push it into [`TypingEnv::param_rigids`], which
/// [`constrained_param_receiver_type`] reads as its PRECISION gate ("the rigid list holds
/// exactly the parameters in scope") — a wrong answer to a third reader's question, bought for
/// nothing. Found by `/code-review`, which built the case: `f(x: Int64) -> Int64 requires
/// p(x, ?v) = x`.
///
/// NOTHING IS LOST, measured both ways. A type precondition's variable that this op could
/// actually be checked against also appears in a PARAMETER (`cmp(a: ?t, b: ?t) requires
/// Ord[T = ?t]`), so the parameter walk already has it; a variable reaching `requires` and the
/// RETURN alone (`mk() -> ?t requires Ord[T = ?t] = 1`) is refused identically with and
/// without this source — before because [`types_compatible`] refuses every variable pair,
/// after because a rigid equals only itself. Should a driver appear, the repair is the
/// per-conjunct split §5.4 already names (`is_value_precondition_clause`), not the whole field.
///
/// A RETURN-ONLY variable is not here either — [`signature_bound_vars`] never walks the
/// return — which is the WI-1063 polarity split kept intact: that one is the existential
/// [`open_existential_return`] opens per call, and skolemizing it in the body is the wrong
/// quantifier the note on `OpInfo.return_type` records as measured and rejected.
///
/// HOW MUCH THIS REACHES, measured rather than estimated: instrumented over all 194 corpus
/// `.anthill` files, exactly TWO operations come back with a non-empty list — the ticket's own
/// `tv1.via_bare` and `tv2.via`, one variable each, both through a PARAMETER. Every other
/// inline-variable signature in the corpus (`LogicalStream.mplus` / `interleave`, guardians'
/// `bodies_of` / `join_texts` / `prompt_with`) is BODY-LESS, and a body-less operation never
/// reaches this pass at all. That is the whole blast radius, and it agrees with the corpus
/// load diff: two files change, both the ticket's.
pub(super) fn inline_signature_type_params(
    kb: &KnowledgeBase,
    op_sym: Symbol,
    params: &[(Symbol, Value)],
    type_params: &[(Symbol, Var)],
    parent_sort_params: &[(Symbol, TermId)],
) -> Vec<(Symbol, Var)> {
    let mut already: Vec<u32> = type_params
        .iter()
        .filter_map(|(_, v)| match v {
            Var::Global(vid) => Some(vid.raw()),
            _ => None,
        })
        .chain(
            parent_sort_params
                .iter()
                .filter_map(|(_, t)| match kb.get_term(*t) {
                    Term::Var(Var::Global(vid)) => Some(vid.raw()),
                    _ => None,
                }),
        )
        .collect();
    already.extend(enclosing_sort_param_vars(kb, op_sym));
    // `&[]` for `requires` — see the header. Not an oversight and not a fork: the shared
    // walk still answers for the parameters, the `[A]` binders and the enclosing sort.
    signature_bound_vars(kb, op_sym, params, &[], type_params)
        .into_iter()
        .filter(|vid| !already.contains(&vid.raw()))
        .filter(|vid| !anonymous_var_name(kb, vid.name()))
        // The rigid is named after the variable itself (`?t`), which is the only name it has —
        // `rigidify_op_type_params` reads `local_name_of` off this symbol purely to render.
        .map(|vid| (vid.name(), Var::Global(vid)))
        .collect()
}

pub(super) fn rigidify_op_type_params(
    kb: &mut KnowledgeBase,
    type_params: &[(Symbol, Var)],
) -> Substitution {
    let mut rigidify = Substitution::new();
    for (param_sym, var) in type_params {
        if let Var::Global(vid) = var {
            let vid = *vid;
            // Name the rigid after the PARAMETER's short name, not the alias var's name.
            // `sort A = ?` aliases to an ANONYMOUS `?` var, so inheriting `vid.name()`
            // renders every skolemized param as `?_` — a clash then reads the unhelpful
            // `expected F[T = ?_], got F[T = ?_]` (both rigids print identically). The
            // short name makes it `?A` vs `?B`. Purely cosmetic: a rigid's identity is its
            // fresh `VarId`, never its name (unification compares VarIds; `SubjectKey` keys
            // on `v.raw()`), so the rename cannot affect any judgement.
            let name = short_name_of(kb.local_name_of(*param_sym)).to_owned();
            let name_sym = kb.intern(&name);
            let fresh = kb.fresh_var(name_sym);
            let rigid_term = kb.alloc(Term::Var(Var::Rigid(fresh)));
            rigidify.bind_term(kb, vid, rigid_term);
        }
    }
    rigidify
}

/// WI-461: a bare self-receiver IDENTITY body — `operation iterator(l: List) -> … = l` —
/// infers the BARE carrier sort `List` as its body type, leaving the carrier's type params
/// unbound. But the returned VALUE is the receiver `l`, whose members ARE its projections
/// (`l.T`, the WI-374 member tie). Refine the bare body type to `List[T = l.T, …]` — pin
/// each of the carrier's type params to its projection off the receiver — so a declared
/// PROVIDED return that threads the projection (`Stream[T = l.T, E = {}]`) conforms via the
/// `parameterized` cross-sort-provider path (the same machinery the explicit
/// `iterator[Elem](l: List[Elem]) -> Stream[Elem, {}]` form already rides), while a
/// DIFFERENT receiver's projection (`Stream[T = xs.T]`) still fails (`l.T` ≠ `xs.T`, two
/// distinct neutrals) — sound. The caller applies this ONLY as a fallback after the
/// unrefined check fails, so it can never reject a body that conforms today.
///
/// `None` (no refinement) unless ALL hold: the body is a stable single-segment value
/// reference (`l` — not a call/literal/constructor/field path); its inferred type is a BARE
/// `sort_ref` (no bindings); the carrier declares ≥1 type param; and each param resolves to
/// a `<carrier>.<P>` symbol. The projection value is built byte-identical to the loader's
/// `l.T` (`make_expr_carried(Ref(recv), intern(short))`, the SHORT member name), and the
/// binding KEY is the carrier's own `<carrier>.<P>` param symbol so the cross-sort-provider
/// instantiation resolves its canonical var.
pub(super) fn refine_self_receiver_body_type(
    kb: &mut KnowledgeBase,
    body: &Rc<NodeOccurrence>,
    body_ty: &Value,
) -> Option<Value> {
    let segs = stable_receiver_path(kb, body)?;
    let [recv] = segs.as_slice() else { return None };
    let recv = *recv;
    let TypeExtractor::SortRef(carrier) = extract_type(kb, body_ty) else {
        return None;
    };
    let param_names = kb.type_params_of_sort(carrier);
    if param_names.is_empty() {
        return None;
    }
    let carrier_qn = kb.qualified_name_of(carrier).to_owned();
    let recv_term = kb.alloc(Term::Ref(recv));
    let mut bindings: Vec<(Symbol, TermId)> = Vec::with_capacity(param_names.len());
    for short in &param_names {
        let param_sym = kb.try_resolve_symbol(&format!("{carrier_qn}.{short}"))?;
        let member_sym = kb.intern(short);
        let proj = kb.make_expr_carried(recv_term, member_sym);
        bindings.push((param_sym, proj));
    }
    let base = kb.make_sort_ref(carrier);
    Some(Value::term(kb.make_parameterized_type(base, &bindings)))
}

/// WI-20260828-N2FHM — the BACKSTOP on the typer's own output: the first
/// `Expr::DotApply` still standing anywhere in a typed operation body, with the dot's
/// member and span.
///
/// A `DotApply` is a PRE-DISPATCH form. Every one of them is supposed to leave the
/// `TypeBuildFrame::DotApply` arm rewritten — to a method `Apply`, a `field_access`, a
/// relation projection, or a `@[simp]` dot-rule RHS — and that arm ends in
/// `DotDispatchNoMatch` when none of those apply, so one surviving in a STORED body
/// means its refusal was produced and then lost somewhere between the dot and the top.
/// Eval has no arm for it: it raises `Internal("unhandled Expr variant in eval")`, which
/// is not a `Raised` payload, so no handler sees it and the caller cannot catch it. That
/// is a silent load and an un-repairable run-time death for a program the typer had
/// already decided was wrong.
///
/// A BACKSTOP AND NOT THE REPAIR, deliberately — and the repair has since landed. The
/// known producer was `MatchAfterScrutinee`, which dropped the scrutinee's `Err` and put
/// the un-rewritten node back (measured: `match find(rs, lambda r -> r.nosuchfield) …`
/// loaded clean and died at eval). WI-20260829-1SSXM propagates that error, which cost
/// 13 corpus programs their clean load across three unrelated root causes — two genuine
/// under-specifications, repaired, and one untypable fixture body whose signature was the
/// thing under test.
///
/// SO THIS NOW FIRES ON NOTHING, and it stays for exactly that reason. Measured on this
/// tree: with the error push below neutralized, `wi_tests` is 3773/3773 — no program in
/// the corpus reaches it any more, because the frame that produced the refusal now
/// reports it. It is the BOUNDARY and not the repair ("an unresolved dot must not reach
/// the evaluator, by whichever route says so"), it is the only thing standing between a
/// producer we have not found yet and an `Internal` eval death no handler can catch, and
/// a backstop that never fires is what an invariant looks like once it holds. Anything
/// that makes it fire again is a NEW swallow, not a regression of this one.
///
/// ITS COVERAGE IS A UNIT TEST, in `typing/tests.rs`, for exactly that reason: no PROGRAM reaches
/// this any more, so `wi_1ssxm_surviving_dot_backstop_tests` drives the walk over
/// synthetic occurrences instead — the depth find, the receiver it hands back, the
/// SOURCE-ORDER guarantee below, and the dot-free control. Without it this whole
/// function would be live, load-bearing and unexercised (found by /code-review).
///
/// Returns the dot's RECEIVER too, so the refusal can name the sort the member was looked
/// for on. Without it the error carries `receiver_sort: None`, which renders as "the
/// receiver's type is unresolved" — and in this ticket's own witness that is FALSE: the
/// receiver types as `Row`, and what is wrong is that `Row` has no such field. Pointing
/// the author of `find(rs, lambda r -> r.typo)` at an inference problem they do not have,
/// instead of at their typo, is not the loud error the repo asks for (found by
/// /code-review). The receiver's type is on the occurrence because the `DotApply` frame
/// stamped it there (WI-732) before any of this went wrong.
///
/// SOURCE ORDER, so the FIRST unresolved dot is the one reported: children are pushed in
/// reverse and popped, which is pre-order DFS left to right. Pushing them forward reports
/// the LAST one — `and(r.typo1, r.typo2)` would name `typo2`, and the author would fix it,
/// reload, and only then be told about `typo1`.
///
/// An EXPLICIT STACK, not host recursion, for the reason the typer's own tree walk is a
/// worklist: a body's nesting depth is the author's, not this pass's, and a deep one must
/// not decide whether the loader stands up. `as_expr()` is `None` for a Pattern-kind
/// occurrence, which ends that branch — correctly, since a `DotApply` in a pattern slot is
/// not something eval reduces.
pub(super) fn surviving_dot_apply(
    occ: &Rc<NodeOccurrence>,
) -> Option<(Symbol, Option<Span>, Rc<NodeOccurrence>)> {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(occ)];
    while let Some(node) = stack.pop() {
        let Some(expr) = node.as_expr() else { continue };
        if let Expr::DotApply { name, receiver, .. } = expr {
            return Some((*name, Some(node.span.span), Rc::clone(receiver)));
        }
        let mut children: Vec<Rc<NodeOccurrence>> = Vec::new();
        crate::kb::node_occurrence::for_each_child(expr, |child| children.push(Rc::clone(child)));
        stack.extend(children.into_iter().rev());
    }
    None
}

/// WI-20260919-N31XX (proposal 065, "The rule") — the type parameters this body is
/// ALLOWED to read as values: those `B` for which `TypeValue[T = B]` stands among the
/// requirements in scope.
///
/// THE SAME LIST THE LOWERING INDEXES, read through the same decoder
/// ([`type_value_clause_param_at`]). That is not tidiness: [`lower_rigid_read_to_slot`]
/// lowers a read it finds a slot for, and this pass refuses a read that SURVIVED
/// un-lowered — so if the two lists disagreed, a read the chain backs but this misses
/// would be refused although it is well-formed, and a read this admits but the chain
/// lacks would be neither lowered nor refused, silently falling back to the frame
/// channel with no slot behind it. One list, one decoder, no third state.
///
/// BOTH LEVELS COME FOR FREE, because [`op_dict_entries`] IS the sort half followed by
/// the op half — a clause written on the enclosing sort and one written on the operation
/// are found by one walk, at the index each will actually occupy at run time. It also
/// normalizes, which is what makes an op-level clause decodable at all (see
/// [`type_value_clause_param_at`]).
///
/// SO THIS ADMITS MORE THAN THE LOWERING TAKES, on purpose: a SORT-half clause backs a
/// read that `lower_rigid_read_to_slot` declines to lower, and that read is correct —
/// it is served by the frame type-argument channel until WI-20260919-H20YY. What must
/// never happen is the reverse.
/// WI-20260919-N31XX — `anthill.reflect.TypeValue`, or `None` in a KB loaded without
/// the reflect stdlib. One resolution point, so the rule's readers cannot disagree about
/// which sort they are talking about.
// WI-20260919-N31XX's `callee_chain_reads_type_value` STOOD HERE, and
// WI-20260921-159S9 removed it rather than leaving it unread. It gated a narrow
// widening of the chain `build_concrete_dispatch_dict` is given — the whole frame, but
// only for a callee whose chain names `TypeValue`, only out of a free operation, only
// where the sort half was empty. That widening is now unconditional at the same call
// site (a slot declared on the OPERATION is as good as one declared on its SORT), so
// the predicate selected nothing: every call it admitted, and every call it declined,
// takes the whole frame. `wi_r541x_body_read_of_type_param_test`'s five rows are its
// drivers and they pass on the general rule.

fn type_value_spec_sym(kb: &KnowledgeBase) -> Option<Symbol> {
    kb.try_resolve_symbol("anthill.reflect.TypeValue")
}

/// WI-20260919-N31XX (proposal 065) — the type PARAMETER a `TypeValue` requirement
/// clause names, or `None` when the entry is not a `TypeValue` clause over a parameter.
///
/// THE ONE READER for "which rigid does this clause make readable", shared by the
/// lowering (which turns it into a slot index) and by the rule (which refuses a read no
/// clause backs). Written once because the two must never disagree: see
/// [`type_value_backed_params`] for what the third state would be.
///
/// BY THE PARAMETER'S CANONICAL LOGICAL VARIABLE, not by symbol.
/// [`clause_named_type_param`] collapses the two spellings a clause can use — a `Ref` /
/// `Ident` on the op-scoped symbol, and a bare `Var::Global` — onto the one variable, and
/// [`type_param_global_var`] resolves the READ side to that same variable, so the two
/// sides agree by construction. A symbol comparison would admit the first spelling and
/// silently miss the second.
///
/// A CLAUSE OVER A CONCRETE TYPE (`requires TypeValue[T = Int64]`) answers `None`, and
/// needs to: it backs no rigid read, because a concrete sort in value position is not a
/// rigid read at all (065's "What the rule does NOT touch").
///
/// READ OFF THE NORMALIZED CHAIN. Both callers hand entries from [`op_dict_entries`],
/// which runs `normalize_op_requires_entry`, so a clause arrives in `SortView` shape with
/// its positionals already filled into named slots — the one shape
/// `unwrap_spec_view_value` decodes into bindings. A BARE application decodes as "no
/// bindings", which cost this ticket its first cut: an op-level clause was read as
/// binding nothing and `operation ty[T]() -> Type requires TypeValue[T = T]` was refused
/// with its own clause written two columns away.
///
/// `find_map` over the bindings rather than a lookup of the `T` key, because `TypeValue`
/// has exactly ONE type parameter, so there is only ever one binding to test.
/// `tv_canon` IS THE SPEC'S CANONICAL SYMBOL, PASSED IN, because both callers are LOOPS
/// over a whole `DictChain`. Resolving `anthill.reflect.TypeValue` by NAME inside would
/// be a string lookup per ENTRY per read, on a path [`lower_rigid_read_to_slot`] takes
/// for every bare type-value node in every body. Found by `/code-review`.
fn type_value_clause_param_at(
    kb: &KnowledgeBase,
    tv_canon: Symbol,
    entry: &RequiresEntry,
) -> Option<VarId> {
    if kb.canonical_sort_sym(entry.required_sort) != tv_canon {
        return None;
    }
    let (_, bindings) = unwrap_spec_view_value(kb, &entry.spec)?;
    bindings
        .iter()
        .find_map(|(_, v)| clause_named_type_param(kb, *v))
}

/// WI-20260919-N31XX (proposal 065 §1) — the FRAME SLOT that backs a value read of the
/// rigid `param`, as an index into the enclosing operation's composed dictionary chain.
///
/// WHY A DIRECT CHAIN LOOKUP RATHER THAN THE DISPATCH MACHINERY. `type_value()` is
/// NULLARY (WI-20260919-HXGXF's fact 1): no argument and no receiver names the type, so
/// `check_apply_iter`'s ordinary route has nothing to pin `TypeValue.T` with and cannot
/// tell two clauses apart — `twoReq[P, Q] requires TypeValue[T = P], TypeValue[T = Q]`
/// offers two slots and the call site says nothing about which. 065 §8's own spelling
/// `type_value[T = B]()` would say it, but that binds the SORT's parameter through a
/// callee bracket, which is refused today. Here the answer is not inferred at all: the
/// READ names its parameter, so the slot is a lookup, and the ambiguity never arises.
/// Driven by `a_lowered_read_answers_through_its_slot`'s two-parameter row, which a
/// lookup that ignored the parameter would answer `Pair2(A: Int64, B: Int64)`.
///
/// THE SAME LIST THE RUNTIME READS. `start_apply_deferred` resolves a slot through
/// `op_dict_entries(kb, enclosing_op).names(kb)`, which is this chain; indexing anything
/// else would name a different dictionary at run time than the one chosen here.
fn type_value_slot(chain: &DictChain, kb: &KnowledgeBase, param: VarId) -> Option<usize> {
    let canon = kb.canonical_sort_sym(type_value_spec_sym(kb)?);
    chain
        .entries()
        .iter()
        .position(|e| type_value_clause_param_at(kb, canon, e) == Some(param))
}

/// WI-20260919-N31XX (proposal 065 §1) — LOWER a bare value-position read of a rigid to
/// `TypeValue[T = B].type_value()`, dispatched through the frame slot that backs it.
///
/// `None` when the read cannot be lowered, and every `None` is a case the caller leaves
/// as the `Expr::TypeValue` it was: `head` is not a type parameter (a genuine nominal
/// sort — `Cell[V = Int64]` reads no rigid), there is no enclosing operation, no slot
/// backs this parameter, or the slot is in the sort half (below). A read left un-lowered
/// and unbacked is refused after typing by the surviving-read pass, so a `None` is never
/// silent.
///
/// THE ANSWER IS A DICTIONARY WALK, which is why no per-carrier member is needed.
/// `TypeValue.type_value` is body-less and backed by a BUILTIN on the spec op
/// (`BuiltinTag::TypeValueOf`, WI-20260919-HXGXF), and `Dictionary(sub… , impl: S)` names
/// the head in `impl` — so the evidence that selected the call IS the type, GHC's
/// `Typeable`. `start_apply_deferred` reads the slot, `expand_dispatching_dict` builds
/// `__req_self`, `dispatch_resolved_operation` parks it in `builtin_dispatch_dict`, and
/// `type_value_of_self` turns it into the `Type` term. Every one of those already exists;
/// this is the one missing leaf.
///
/// `enclosing_op` IS `Some`, ALWAYS, and it must be: `start_apply_deferred` picks the
/// chain to index by that field — `op_dict_entries(op)` when it is `Some`, the sort-only
/// `provider_dict_entries` otherwise — and the slot is an index into the COMPOSED chain.
///
/// SYNTHESIZED, NOT REWRITTEN IN PLACE, so the original read keeps its span: the node is
/// built `from` the read's occurrence, which puts a later diagnostic on the `B` the
/// author wrote rather than on the operation.
pub(super) fn lower_rigid_read_to_slot(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
    head: Symbol,
) -> Option<Rc<NodeOccurrence>> {
    let param = type_param_global_var(kb, head)?;
    let enclosing_op = env.enclosing_op()?;
    let chain = env.enclosing_frame_chain();
    let slot = type_value_slot(chain, kb, param)?;
    // BOTH HALVES OF THE CHAIN ARE LOWERED, and what made the sort half reachable was
    // one line elsewhere rather than anything here.
    //
    // An OP-HALF slot is an INPUT the caller supplies at every call. A SORT-HALF slot
    // rides the INSTANCE, and the frame carries it only when the operation was entered
    // with its dictionary built — which, for a cross-sort call, is
    // `build_concrete_dispatch_dict`'s job. That builder was being handed the caller's
    // SORT-only chain, so a FREE operation's own `requires TypeValue[T = P]` was
    // invisible to it and the projection failed; `require_complete` then dropped the
    // whole dictionary and the callee ran with an empty frame. See the `serves` note at
    // that call site for the measurement.
    //
    // WHAT IT CLOSED: R541X's two (C) rows — a PROVIDER's and a WITNESS's own parameter
    // on a member entered through a requirement slot — now ANSWER `Box(V: Boom)` and
    // `Crate(W: Boom)` where they were a located fault. That is 065 §4 /
    // WI-20260919-891QP, which the proposal said would flip when the read became a slot
    // dispatch. A `Dictionary` still carries no type BINDINGS; what changed is that the
    // answer no longer needs one, because the evidence that selected the provision IS the
    // type.
    let resolved_spec = chain.entries()[slot].clone();
    let spec_op_sym = kb.try_resolve_symbol("anthill.reflect.TypeValue.type_value")?;
    // Derived, not re-spelled: `kb.intern(short_name_of(&op_qn))` is what every other
    // producer of this field does, and a literal would be a second place the member's
    // name is written.
    let op_qn = kb.qualified_name_of(spec_op_sym).to_owned();
    let op_short_sym = kb.intern(short_name_of(&op_qn));
    let pass = crate::kb::simp_rewrite::simp_pass(kb);
    let node = NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type: None,
            functor: spec_op_sym,
            pos_args: Vec::new(),
            named_args: Vec::new(),
            type_args: Vec::new(),
        },
        Rc::clone(occ),
        pass,
        occ.owner,
    );
    let type_ty = kb.make_sort_ref_by_name("anthill.prelude.Type");
    node.set_inferred_type(Value::term(type_ty));
    classify(
        kb,
        &node,
        CallClass::DeferToRequirement {
            spec_op_sym,
            op_short_sym,
            resolved_spec,
            slot,
            // NO PROJECTION. `proj_path` descends INTO a slot's requirement tree for a
            // requirement reached through another; the slot found here IS the
            // `TypeValue` clause, at the top of its own entry.
            proj_path: SmallVec::new(),
            enclosing_sort: env.enclosing_sort(),
            enclosing_op: Some(enclosing_op),
        },
    );
    Some(node)
}

pub(super) fn type_value_backed_params(kb: &mut KnowledgeBase, op_sym: Symbol) -> HashSet<VarId> {
    let Some(canon) = type_value_spec_sym(kb).map(|tv| kb.canonical_sort_sym(tv)) else {
        return HashSet::new();
    };
    op_dict_entries(kb, op_sym)
        .entries()
        .iter()
        .filter_map(|e| type_value_clause_param_at(kb, canon, e))
        .collect()
}

/// WI-20260919-N31XX — every VALUE-position read of a rigid type in this body, as
/// (the parameter's canonical variable, the symbol as written, span), in SOURCE ORDER.
///
/// THE WALK AND THE ADMISSION TEST ARE SEPARATE, and that split is what keeps the rule
/// off the hot path: almost every operation body in a program reads no rigid at all, and
/// this walk answers empty for it without asking what the operation requires.
/// [`type_value_backed_params`] costs a `lookup_operation_info` and a `direct_requires`
/// chain per call — the same per-operation read `any_requirement_names_spec`' doc
/// measured at ~23 ms over a stdlib load — so it runs only once this has found something
/// to admit.
///
/// THE SHAPE IT LOOKS FOR is proposal 055 §2's classified form: the loader mints a
/// nominal type in value position as an `Expr::TypeValue`, and a BARE one (no type
/// arguments) whose head is a type parameter is exactly "read the rigid `B` as a value".
/// A read nested inside a type expression — `Cell[V = B]` — is the same node one level
/// down, and [`for_each_child`](crate::kb::node_occurrence::for_each_child) yields those
/// arguments, so the plain walk reaches it with no special case. An applied
/// `Expr::TypeValue` is never itself a rigid read: a type parameter takes no arguments.
///
/// WHAT THE WALK DOES NOT REACH, and each is correct rather than tolerated. A CALLEE
/// BRACKET (`tyOf[T = B]()`) is a type position, and `for_each_child`'s `Apply` arm does
/// not yield `type_args` — so it is excluded by construction, not by a test here. A
/// TYPE ANNOTATION is a `NodeKind::Type` occurrence, for which `as_expr()` is `None`.
/// A RULE BODY is not an operation body and this pass never sees one.
///
/// A RAW `Expr::Ref` / `Expr::Ident` NAMING A TYPE PARAMETER IS NOT COUNTED, and that is
/// MEASURED rather than assumed: WI-20260919-BQHGD's census ran this question over the
/// full workspace — stdlib, `anthill-stl`, the examples and every fixture — and found all
/// 157 hits over 19 sites arrived as `Expr::TypeValue`, none as a raw `Ref`. Eval's
/// WI-206 bare-sort arm in `reduce_var` is therefore not reached by a type-parameter read
/// from checked source. Counting the raw form here would mean judging occurrences the
/// loader has not classified as value reads at all.
///
/// SOURCE ORDER, so the FIRST unbacked read is reported: children are pushed in reverse
/// and popped, which is pre-order DFS left to right — the same reason and the same
/// spelling as [`surviving_dot_apply`] above. An author fixing the last read first would
/// reload only to be told about the first.
///
/// AN EXPLICIT STACK, not host recursion, for the reason [`surviving_dot_apply`] gives:
/// a body's nesting depth is the author's, and it must not decide whether the loader
/// stands up.
pub(super) fn rigid_value_reads(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
) -> Vec<(VarId, Symbol, Option<Span>)> {
    let mut out = Vec::new();
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(occ)];
    while let Some(node) = stack.pop() {
        let Some(expr) = node.as_expr() else { continue };
        if let Expr::TypeValue {
            head,
            pos_args,
            named_args,
        } = expr
        {
            if pos_args.is_empty() && named_args.is_empty() {
                // A TYPE PARAMETER and not a sort: `type_param_global_var` answers
                // `Some` only for a symbol `add_type_param` registered, which is the
                // same membership test every other clause reader in the typer uses, and
                // it yields the parameter's CANONICAL variable — the identity
                // `type_value_backed_params` keys its answer on, for the reason stated
                // there. A genuine nominal sort head falls straight through:
                // `Cell[V = Int64]` reads no rigid, which is 065's "concrete sorts"
                // exclusion.
                if let Some(vid) = type_param_global_var(kb, *head) {
                    out.push((vid, *head, Some(node.span.span)));
                }
            }
        }
        let mut children: Vec<Rc<NodeOccurrence>> = Vec::new();
        crate::kb::node_occurrence::for_each_child(expr, |child| children.push(Rc::clone(child)));
        stack.extend(children.into_iter().rev());
    }
    out
}
