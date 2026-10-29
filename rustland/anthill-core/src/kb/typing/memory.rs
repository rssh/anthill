//! Proposal 050.1, stage 1 — the memory half of the typing environment: which parameter's
//! memory, or which pool's, the value a local name holds may lie in, so that a write through
//! the name is charged where the name's scope ends (050.1 §2, §3) instead of being dropped
//! because the binder is a `let` or a pattern.
//!
//! ONE RECORD PER OPERATION BODY ([`MemoryTable`]), shared by every environment cloned from
//! the body's root. A binding is written once: a binder symbol is minted per binding site. A
//! connection a store makes carries the branch it was made in ([`BranchPath`], held by Γ's
//! [`FlowEnv`], which the `if` and each `match` arm fork); it is visible in that branch and
//! after the `if` / `match` it belongs to, never in a sibling arm — what a copy of the record
//! per branch, merged at the join, gives. Shared rather than copied because the typer drops
//! the environment of a call's argument on the way up: a store written as an argument
//! (`g(push(s, c))`) would be lost with it. The path is a persistent list, one node per
//! fork, so a chain of `else if` thousands deep costs one node per level.

use super::*;

/// A memory a value may lie in.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Region {
    /// A parameter's memory: the caller's.
    Param(Symbol),
    /// State outside the process, named by the constant of a pool sort (proposal 037 §2):
    /// `kb_storage`. No effect row can name it.
    Pool(Symbol),
    /// Memory the body allocated: the result of a call whose clauses connect it to nothing.
    Fresh(u32),
    /// A lambda's parameter's memory, which the lambda's caller supplies. A write to it stays
    /// over that parameter (`Modify[z]`), as the lambda's arrow row says it; the application
    /// charges it to the argument (050.1 stage 2, WI-20261014-7EZS6).
    Supplied(Symbol),
}

/// The branch of a body a point lies in: the arm taken at each fork (an `if` or a `match`,
/// numbered per body) above it, innermost first. `None` is the body's root.
pub(crate) type BranchPath = Option<Rc<BranchNode>>;

/// One fork of a [`BranchPath`].
#[derive(Debug)]
pub(crate) struct BranchNode {
    fork: u32,
    arm: u32,
    parent: BranchPath,
}

/// Dropped iteratively: a path an `else if` chain thousands deep built is that many nodes, and
/// the default drop recurses once per node.
impl Drop for BranchNode {
    fn drop(&mut self) {
        let mut parent = self.parent.take();
        while let Some(node) = parent {
            match Rc::try_unwrap(node) {
                Ok(mut node) => parent = node.parent.take(),
                Err(_) => break,
            }
        }
    }
}

impl FlowEnv {
    /// This Γ, in arm `arm` of the fork `fork` ([`TypingEnv::new_fork`]); a `match` arm's
    /// scope began at `mark` ([`TypingEnv::memory_mark`]).
    pub(super) fn in_branch(&self, fork: u32, arm: usize, mark: usize) -> FlowEnv {
        let mut next = self.clone();
        next.scope_mark = mark;
        next.branch = Some(Rc::new(BranchNode {
            fork,
            arm: arm as u32,
            parent: self.branch.clone(),
        }));
        next
    }
}

/// What a local name holds.
#[derive(Clone, Debug)]
pub(crate) enum Binding {
    /// The value at a stable path with this head — `let x = p`, `let x = p.f`, a pattern
    /// binder over `p` or `p.f`. A write through the name is the head's alone (§3). `whole`
    /// when the path is the head itself: only then is the name the head's resource
    /// (`memory_alias`); a field of it lies in its memory and is another resource.
    Alias { head: Symbol, whole: bool },
    /// The regions the value lies in: a construction's parts, a call's connected arguments, a
    /// branch's values, a pattern's scrutinee that is no path.
    Regions(Vec<Region>),
    /// A lambda's parameter, whose value its caller supplies: its memory is
    /// [`Region::Supplied`].
    Supplied,
}

/// A write charged to a pool: no row can declare it, so the operation's boundary refuses it.
pub(crate) struct PoolWrite {
    /// The label as the body incurred it (`Modify[k]`).
    pub(crate) label: Value,
    /// The local name it was written through.
    pub(crate) name: Symbol,
    /// The pool's constant.
    pub(crate) pool: Symbol,
}

/// The memory record of one operation body — see the module doc.
#[derive(Default)]
pub(crate) struct MemoryTable {
    /// Each local name's binding and its position in the order names were bound — a scope's
    /// own names are those bound since it began ([`TypingEnv::memory_mark`]).
    bindings: HashMap<Symbol, (usize, Binding)>,
    /// The name each fresh region was first bound to: the cell `let k = Cell.new(…)` makes is
    /// `k`'s, so a write to it at a scope `k` is outside of is a write through `k`.
    fresh_owner: HashMap<u32, Symbol>,
    unions: Vec<(Region, Region, BranchPath)>,
    pool_writes: Vec<PoolWrite>,
    next_fresh: u32,
    next_fork: u32,
    /// The sorts a `Modify` fires on ([`crate::kb::region::region_sorts`]), read once per
    /// body: what decides whether a value's type can hold memory at all (§1's filter).
    region_sorts: Option<Rc<HashSet<Symbol>>>,
    /// The pairs of parameters the operation requires disconnected (§1.2: an operation whose
    /// facts need one case says so in its `requires`) — hypotheses the record answers from
    /// where the two parameters would otherwise be unknown.
    separations: Vec<(Symbol, Symbol)>,
}

impl MemoryTable {
    fn fresh(&mut self) -> Region {
        self.next_fresh += 1;
        Region::Fresh(self.next_fresh)
    }
}

/// A body's memory record together with the operation whose parameters are its outside
/// regions — what both the typer ([`TypingEnv::memory_scope`]) and Γ's bridge
/// ([`MemoryView`]) read the record through. `op` is `None` outside an operation body.
#[derive(Clone)]
pub(crate) struct MemoryScope {
    table: Rc<std::cell::RefCell<MemoryTable>>,
    op: Option<Symbol>,
}

impl MemoryScope {
    /// What `name` holds, when it is a local name of this body.
    fn binding(&self, name: Symbol) -> Option<Binding> {
        self.table.borrow().bindings.get(&name).map(|(_, b)| b.clone())
    }

    /// Was `name` bound in the scope that began at `mark`? A parameter, or a name bound
    /// before the scope began, is outside it.
    fn bound_since(&self, name: Symbol, mark: usize) -> bool {
        self.table.borrow().bindings.get(&name).is_some_and(|(i, _)| *i >= mark)
    }

    /// Does the operation require `p` and `q` disconnected ([`MemoryTable::separations`])?
    fn required_apart(&self, p: Symbol, q: Symbol) -> bool {
        self.table
            .borrow()
            .separations
            .iter()
            .any(|(a, b)| (*a == p && *b == q) || (*a == q && *b == p))
    }

    /// The name a fresh region was first bound to.
    fn fresh_owner(&self, region: u32) -> Option<Symbol> {
        self.table.borrow().fresh_owner.get(&region).copied()
    }

    fn fresh(&self) -> Region {
        self.table.borrow_mut().fresh()
    }

    /// Is `sym` a data parameter of the operation — a parameter a `Modify` can be charged to?
    /// A callback parameter is not: what it holds is a function.
    fn is_own_param(&self, kb: &KnowledgeBase, sym: Symbol) -> bool {
        self.op.is_some_and(|op| {
            kb.symbols.arg_places(op).contains(&sym) && !kb.symbols.is_callable(sym)
        })
    }
}

impl TypingEnv {
    /// Record what `name` holds ([`Binding`]). A fresh region no name holds yet is `name`'s.
    pub(super) fn bind_memory(&self, name: Symbol, binding: Binding) {
        let mut table = self.memory.borrow_mut();
        if let Binding::Regions(regions) = &binding {
            for r in regions {
                if let Region::Fresh(n) = r {
                    table.fresh_owner.entry(*n).or_insert(name);
                }
            }
        }
        let position = table.bindings.len();
        table.bindings.insert(name, (position, binding));
    }

    /// Where a scope beginning now starts in the order names are bound: the names bound from
    /// here on are its own ([`charge_local_writes`]).
    pub(super) fn memory_mark(&self) -> usize {
        self.memory.borrow().bindings.len()
    }

    /// This body's memory record, read as [`MemoryScope`].
    pub(crate) fn memory_scope(&self) -> MemoryScope {
        MemoryScope {
            table: Rc::clone(&self.memory),
            op: self.enclosing_op(),
        }
    }

    /// A new fork of this body — an `if` or a `match` — for [`FlowEnv::in_branch`].
    pub(super) fn new_fork(&self) -> u32 {
        let mut table = self.memory.borrow_mut();
        table.next_fork += 1;
        table.next_fork
    }

    /// Set the regions of the value a pattern is about to take apart, returning what was set
    /// before — the caller restores it once the pattern is bound, so that nothing typed in the
    /// pattern's scope reads it.
    pub(super) fn set_binding_regions(&mut self, regions: Option<Rc<[Region]>>) -> Option<Rc<[Region]>> {
        std::mem::replace(&mut self.binding_regions, regions)
    }

    /// What a pattern's binder holds: the field path it reads, when the value it takes apart
    /// is one; else the regions that value lies in; else, binding no value of this body (a
    /// lambda's parameter), what its caller supplies.
    /// A path headed by a name that holds no memory — a constructor, a `const`, a nullary
    /// operation's result — is such a value: a write through it is to the body's own memory.
    pub(super) fn pattern_binder_memory(
        &self,
        kb: &KnowledgeBase,
        scrutinee_path: Option<&[Symbol]>,
    ) -> Binding {
        match (scrutinee_path, &self.binding_regions) {
            (Some([head, ..]), _) if names_no_place(kb, *head) => Binding::Regions(Vec::new()),
            (Some(path @ [head, ..]), _) => Binding::Alias {
                head: *head,
                whole: path.len() == 1,
            },
            (_, Some(regions)) => Binding::Regions(regions.to_vec()),
            (_, None) => Binding::Supplied,
        }
    }

    /// Take the operation's own `requires` that two of its parameters are disconnected —
    /// `memory_disconnected(p, q)` or `not memory_maybe_connected(p, q)` — as hypotheses of
    /// the record ([`MemoryTable::separations`]), so that either spelling a callee requires
    /// is answered from them.
    pub(super) fn assume_required_separations(&self, kb: &KnowledgeBase, requires: &[Value]) {
        let pairs: Vec<(Symbol, Symbol)> = requires
            .iter()
            .flat_map(|c| clause_conjuncts(kb, c))
            .filter_map(|conj| required_separation(kb, &conj))
            .collect();
        self.memory.borrow_mut().separations.extend(pairs);
    }

    /// The writes charged to a pool so far, taken out of the record. One per label: only a
    /// final reader records them ([`ScopeEnd::Final`]), over a row already deduplicated.
    pub(crate) fn take_pool_writes(&self) -> Vec<PoolWrite> {
        std::mem::take(&mut self.memory.borrow_mut().pool_writes)
    }
}

/// The regions the value `node` computes lies in (050.1 §2). A value whose type `ty` can hold
/// no memory — no `Modify` fires on it, through a field or a type argument (§1's filter,
/// [`crate::kb::region::type_admits_modify`]) — lies in none, and is not walked. A function
/// value is not filtered by what it returns: it lies in what it captures (§1, §2).
pub(super) fn value_regions(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    node: &Rc<NodeOccurrence>,
    ty: Option<&Value>,
) -> Vec<Region> {
    if let Some(ty) = ty.filter(|ty| arrow_parts(kb, *ty).is_none()) {
        let sorts = {
            let mut table = env.memory.borrow_mut();
            Rc::clone(
                table
                    .region_sorts
                    .get_or_insert_with(|| Rc::new(crate::kb::region::region_sorts(kb))),
            )
        };
        if !crate::kb::region::type_admits_modify(kb, ty, &sorts) {
            return Vec::new();
        }
    }
    let mut out = Vec::new();
    collect_value_regions(kb, &env.memory_scope(), node, &mut out);
    let mut seen = HashSet::new();
    out.retain(|r| seen.insert(*r));
    out
}

fn collect_value_regions(
    kb: &mut KnowledgeBase,
    scope: &MemoryScope,
    node: &Rc<NodeOccurrence>,
    out: &mut Vec<Region>,
) {
    // An explicit stack: a value can be an `else if` chain thousands deep.
    let mut stack: Vec<(Rc<NodeOccurrence>, Walk)> = vec![(Rc::clone(node), Walk::Value)];
    while let Some((node, walk)) = stack.pop() {
        // A name, or a field path off one: the name's memory. A field of a value lies in the
        // value's regions.
        if let Some(sym) = extract_var_ref_sym_node(&node) {
            name_regions(kb, scope, sym, out);
            continue;
        }
        if walk == Walk::Value {
            if let Some(head) = stable_receiver_path(kb, &node).and_then(|p| p.first().copied()) {
                name_regions(kb, scope, head, out);
                continue;
            }
        }
        let Some(expr) = node.as_expr() else { continue };
        let push_children = |stack: &mut Vec<_>, walk: Walk| {
            crate::kb::node_occurrence::for_each_child(expr, |c| stack.push((Rc::clone(c), walk)));
        };
        match (walk, expr) {
            // Every name a lambda's body mentions is a capture, or one of its own parameters,
            // which are [`Binding::Supplied`] and contribute nothing.
            (Walk::Captures, _) => push_children(&mut stack, Walk::Captures),
            (
                Walk::Value,
                Expr::Apply {
                    functor,
                    pos_args,
                    named_args,
                    ..
                },
            ) => call_result_regions(kb, scope, *functor, pos_args, named_args, out),
            // A construction lies in its parts' own regions, and adds none (§2).
            (
                Walk::Value,
                Expr::Constructor { .. } | Expr::TupleLit { .. } | Expr::ListLit(_) | Expr::SetLit(_),
            ) => push_children(&mut stack, Walk::Value),
            (
                Walk::Value,
                Expr::If {
                    then_branch,
                    else_branch,
                    ..
                },
            ) => {
                stack.push((Rc::clone(then_branch), Walk::Value));
                stack.push((Rc::clone(else_branch), Walk::Value));
            }
            (Walk::Value, Expr::Match { branches, .. }) => {
                for b in branches {
                    stack.push((Rc::clone(&b.body), Walk::Value));
                }
            }
            (Walk::Value, Expr::Let { body, .. }) => stack.push((Rc::clone(body), Walk::Value)),
            // A lambda reaches every name it captures (§2).
            (Walk::Value, Expr::Lambda { body, .. }) => {
                stack.push((Rc::clone(body), Walk::Captures))
            }
            // A method call whose dispatch the typer left as a dot: no clause is read through
            // it, so its result is fresh, as a call's with no clause is.
            (Walk::Value, Expr::DotApply { .. }) => out.push(scope.fresh()),
            (Walk::Value, _) => {}
        }
    }
}

/// What [`collect_value_regions`] reads a node as.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Walk {
    /// The value the node computes.
    Value,
    /// The names a lambda's body captures.
    Captures,
}

fn name_regions(kb: &mut KnowledgeBase, scope: &MemoryScope, sym: Symbol, out: &mut Vec<Region>) {
    if scope.is_own_param(kb, sym) {
        out.push(Region::Param(sym));
        return;
    }
    match scope.binding(sym) {
        Some(Binding::Alias { head, .. }) => name_regions(kb, scope, head, out),
        Some(Binding::Regions(regions)) => out.extend(regions),
        Some(Binding::Supplied) => out.push(Region::Supplied(sym)),
        None => {}
    }
}

/// The two memory relations of `anthill.memory`, as a callee's clause names them.
#[derive(Clone, Copy, PartialEq, Eq)]
enum MemoryRelation {
    Alias,
    MaybeConnected,
}

/// `conj` as a memory relation over two operands, each read as the name it is (`result`, a
/// parameter, a constant). An operand that is no name is `None`.
fn memory_relation(
    kb: &KnowledgeBase,
    conj: &Value,
) -> Option<(MemoryRelation, Option<Symbol>, Option<Symbol>)> {
    let ViewHead::Functor {
        functor,
        pos_arity: 2,
        named_arity: 0,
    } = conj.head(kb)
    else {
        return None;
    };
    let relation = match kb.qualified_name_of(functor) {
        "anthill.memory.memory_alias" => MemoryRelation::Alias,
        "anthill.memory.memory_maybe_connected" => MemoryRelation::MaybeConnected,
        _ => return None,
    };
    let operand = |i: usize| conj.pos_arg(kb, i).and_then(|item| operand_name(kb, &item));
    Some((relation, operand(0), operand(1)))
}

/// The name an operand of a clause is: a bare name (`kb_storage`, a parameter), or the
/// `var_ref(name: …)` the loader stores a binder as (`result`).
fn operand_name<V: TermView>(kb: &KnowledgeBase, item: &V) -> Option<Symbol> {
    match item.head(kb) {
        ViewHead::Functor {
            functor,
            pos_arity: 0,
            named_arity: 0,
        } => Some(functor),
        ViewHead::Functor {
            functor,
            pos_arity: 0,
            named_arity: 1,
        } if kb.qualified_name_of(functor) == "anthill.reflect.Expr.var_ref" => {
            let name = item.named_arg(kb, kb.lookup_symbol("name")?)?;
            operand_name(kb, &name)
        }
        _ => None,
    }
}

/// The two places a requirement says are disconnected: `memory_disconnected(a, b)`, or
/// `not(memory_maybe_connected(a, b))` — the clause defining the first.
fn required_separation(kb: &KnowledgeBase, conj: &Value) -> Option<(Symbol, Symbol)> {
    let ViewHead::Functor {
        functor,
        pos_arity,
        named_arity: 0,
    } = conj.head(kb)
    else {
        return None;
    };
    let operands = |goal: &Value| match memory_relation(kb, goal) {
        Some((MemoryRelation::MaybeConnected, Some(a), Some(b))) => Some((a, b)),
        _ => None,
    };
    match (kb.qualified_name_of(functor), pos_arity) {
        ("anthill.memory.memory_disconnected", 2) => {
            let a = operand_name(kb, &conj.pos_arg(kb, 0)?)?;
            let b = operand_name(kb, &conj.pos_arg(kb, 1)?)?;
            Some((a, b))
        }
        ("anthill.kernel.not", 1) => operands(&conj.pos_arg(kb, 0)?.to_value()),
        _ => None,
    }
}

/// Is `conj` one of `anthill.memory`'s relations? Such a clause is read by this module, not
/// assumed into Γ as a fact ([`assume_call_ensures`]).
pub(super) fn is_memory_clause(kb: &KnowledgeBase, conj: &Value) -> bool {
    memory_relation(kb, conj).is_some()
}

/// A callee's memory clauses, with its parameters read as the call's arguments: `operand`
/// gives the argument a callee parameter binds, or `None`.
struct CallMemory {
    clauses: Vec<(MemoryRelation, Option<Symbol>, Option<Symbol>)>,
    result: Option<Symbol>,
    params: Vec<Symbol>,
}

fn call_memory(kb: &mut KnowledgeBase, functor: Symbol) -> Option<CallMemory> {
    let sig = kb.op_record(functor).and_then(|r| r.signature.as_ref())?;
    // The common call: a callee with no `ensures` has no memory clause, and nothing below
    // needs to be read.
    if sig.ensures.is_empty() {
        return Some(CallMemory {
            clauses: Vec::new(),
            result: None,
            params: Vec::new(),
        });
    }
    let params: Vec<Symbol> = sig.params.iter().map(|(s, _)| *s).collect();
    let ensures = sig.ensures.clone();
    let clauses: Vec<_> = ensures
        .iter()
        .flat_map(|clause| clause_conjuncts(kb, clause))
        .filter_map(|conj| memory_relation(kb, &conj))
        .collect();
    let result = crate::kb::region::resolve_op_result_sym(kb, functor);
    Some(CallMemory {
        clauses,
        result,
        params,
    })
}

/// The argument each callee parameter of `params` binds at a call, in the parameters' order
/// (`None` for one the call leaves out).
fn args_by_param(
    kb: &KnowledgeBase,
    params: &[Symbol],
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> Vec<(Symbol, Option<Rc<NodeOccurrence>>)> {
    let mut out: Vec<(Symbol, Option<Rc<NodeOccurrence>>)> =
        params.iter().map(|p| (*p, None)).collect();
    let indices = positional_param_indices(kb, params, pos_args.len(), named_args);
    for (arg, idx) in pos_args.iter().zip(indices.iter()) {
        if let Some(i) = idx {
            out[*i].1 = Some(Rc::clone(arg));
        }
    }
    for (label, arg) in named_args {
        if let Some(i) = params.iter().position(|p| same_label(kb, *p, *label)) {
            out[i].1 = Some(Rc::clone(arg));
        }
    }
    out
}

/// The regions of an operand of a callee's memory clause at a call: an argument's, or a
/// constant's pool. An operand that names nothing this reads — a field path in a clause, or
/// a parameter the call left out — is every argument's: a sound over-approximation.
fn operand_regions(
    kb: &mut KnowledgeBase,
    scope: &MemoryScope,
    operand: Option<Symbol>,
    args: &[(Symbol, Option<Rc<NodeOccurrence>>)],
    out: &mut Vec<Region>,
) {
    let given = |sym: Symbol| args.iter().find(|(p, _)| *p == sym).and_then(|(_, a)| a.clone());
    match operand {
        Some(sym) if given(sym).is_some() => {
            let arg = given(sym).expect("given above");
            collect_value_regions(kb, scope, &arg, out);
        }
        Some(sym) if kb.has_kind(sym, crate::intern::SymbolKind::Entity) => {
            out.push(Region::Pool(sym));
        }
        _ => {
            for arg in args.iter().filter_map(|(_, a)| a.as_ref()) {
                collect_value_regions(kb, scope, arg, out);
            }
        }
    }
}

/// The regions a call's result lies in: what the callee's clauses over `result` connect it
/// to (§4's caller half), else a fresh region of its own (§2, the default for every
/// operation). A construction written as an application lies in its arguments' regions.
fn call_result_regions(
    kb: &mut KnowledgeBase,
    scope: &MemoryScope,
    functor: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    out: &mut Vec<Region>,
) {
    let Some(memory) = call_memory(kb, functor) else {
        if kb.has_kind(functor, crate::intern::SymbolKind::Entity) {
            for arg in pos_args.iter().chain(named_args.iter().map(|(_, a)| a)) {
                collect_value_regions(kb, scope, arg, out);
            }
        } else {
            out.push(scope.fresh());
        }
        return;
    };
    let args = args_by_param(kb, &memory.params, pos_args, named_args);
    let mut connected = false;
    for (_, a, b) in &memory.clauses {
        let other = match memory.result {
            Some(r) if *a == Some(r) => *b,
            Some(r) if *b == Some(r) => *a,
            _ => continue,
        };
        connected = true;
        operand_regions(kb, scope, other, &args, out);
    }
    if !connected {
        out.push(scope.fresh());
    }
}

/// Record the connections a call makes among its arguments: a callee clause relating two of
/// its parameters (or a parameter and a pool) unites their regions, in the branch `branch`
/// (§2, "A call that stores").
pub(super) fn record_call_stores(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    branch: &BranchPath,
    functor: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) {
    let Some(memory) = call_memory(kb, functor) else { return };
    if memory.clauses.is_empty() {
        return;
    }
    let scope = env.memory_scope();
    let scope = &scope;
    let args = args_by_param(kb, &memory.params, pos_args, named_args);
    for (_, a, b) in &memory.clauses {
        if memory.result.is_some() && (*a == memory.result || *b == memory.result) {
            continue;
        }
        let (mut left, mut right) = (Vec::new(), Vec::new());
        operand_regions(kb, scope, *a, &args, &mut left);
        operand_regions(kb, scope, *b, &args, &mut right);
        let mut table = scope.table.borrow_mut();
        for l in &left {
            for r in &right {
                if l != r {
                    table.unions.push((*l, *r, branch.clone()));
                }
            }
        }
    }
}

/// Where a write through a local name is charged.
enum Charge {
    /// Onto a parameter of the operation.
    Param(Symbol),
    /// Onto a pool: refused at the boundary.
    Pool(Symbol),
    /// Onto a name the record cannot see past — a lambda's parameter, or the head of an alias
    /// that is no local name of this body — which the label keeps naming, so that the arrow
    /// row carries it and an undeclared one is refused where it surfaces.
    Kept(Symbol),
}

/// The arm `path` takes at each fork it went through.
fn arms_taken(path: &BranchPath) -> HashMap<u32, u32> {
    let mut arms = HashMap::new();
    let mut node = path.as_deref();
    while let Some(n) = node {
        arms.insert(n.fork, n.arm);
        node = n.parent.as_deref();
    }
    arms
}

/// Is a record made in `made` visible to a reader whose path takes `reader_arms`? Every fork
/// the record's branch went through is one the reader either took the same arm of, or is
/// outside of — after its join.
fn branch_visible(made: &BranchPath, reader_arms: &HashMap<u32, u32>) -> bool {
    let mut node = made.as_deref();
    while let Some(n) = node {
        if reader_arms.get(&n.fork).is_some_and(|arm| *arm != n.arm) {
            return false;
        }
        node = n.parent.as_deref();
    }
    true
}

/// The regions connected to `start` through the unions visible at `reader`.
fn connected_regions(scope: &MemoryScope, start: &[Region], reader: &BranchPath) -> Vec<Region> {
    let table = scope.table.borrow();
    if table.unions.is_empty() {
        return start.to_vec();
    }
    let reader_arms = arms_taken(reader);
    let mut reached: Vec<Region> = start.to_vec();
    let mut i = 0;
    while i < reached.len() {
        let r = reached[i];
        for (a, b, made) in &table.unions {
            let other = if *a == r {
                *b
            } else if *b == r {
                *a
            } else {
                continue;
            };
            if branch_visible(made, &reader_arms) && !reached.contains(&other) {
                reached.push(other);
            }
        }
        i += 1;
    }
    reached
}

/// Where a write through the local name `name` is charged at the end of the scope that began
/// at `mark`, read at `reader` (§3). A name bound outside that scope keeps its label, to be
/// charged where its own scope ends. Of the scope's own names: an alias of a parameter onto
/// that parameter alone, of an outer name onto that name; any other name onto every
/// parameter, and every pool, a region it reaches belongs to, and onto the outer name a fresh
/// region was made for (`k` of `let k = Cell.new(…)`). A fresh region made inside the scope
/// adds nothing — the allocation that made it brings its own `Modify[result]`, which the
/// boundary keeps where the result can carry it (WI-314).
fn charges(
    kb: &KnowledgeBase,
    scope: &MemoryScope,
    name: Symbol,
    reader: &BranchPath,
    mark: usize,
) -> Vec<Charge> {
    if !scope.bound_since(name, mark) {
        return vec![Charge::Kept(name)];
    }
    match scope.binding(name) {
        Some(Binding::Alias { head, .. }) if scope.is_own_param(kb, head) => {
            vec![Charge::Param(head)]
        }
        Some(Binding::Alias { head, .. }) if scope.binding(head).is_some() => {
            charges(kb, scope, head, reader, mark)
        }
        Some(Binding::Alias { head, .. }) => vec![Charge::Kept(head)],
        Some(Binding::Regions(regions)) => connected_regions(scope, &regions, reader)
            .into_iter()
            .filter_map(|r| match r {
                Region::Param(p) => Some(Charge::Param(p)),
                Region::Pool(c) => Some(Charge::Pool(c)),
                Region::Supplied(z) => Some(Charge::Kept(z)),
                Region::Fresh(n) => scope
                    .fresh_owner(n)
                    .filter(|owner| !scope.bound_since(*owner, mark))
                    .map(Charge::Kept),
            })
            .collect(),
        Some(Binding::Supplied) | None => vec![Charge::Kept(name)],
    }
}

/// Which end of a scope [`charge_local_writes`] reads a row at.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum ScopeEnd {
    /// A `match` arm's or a lambda body's end: a write that reaches a pool keeps its label,
    /// so the row still carries it to the reader that refuses it.
    Arm,
    /// The operation's end, or a rule-body call's: a write that reaches a pool is recorded for
    /// the refusal ([`TypingEnv::take_pool_writes`]) and leaves the row.
    Final,
}

/// The effect row a scope ends with, its labels over the body's local names charged where the
/// names' memory lies (§3): onto a parameter (`Modify[x]` ⟹ `Modify[p]`); onto a lambda's
/// parameter the memory is (`let y = z` in the lambda ⟹ `Modify[z]`), which the label keeps
/// naming; a write to fresh memory adds nothing; a write that reaches a pool as `end` says. A
/// label naming no local name is kept as it is — a lambda's row among them: its body's end is
/// charged too, so the row an applied function value brings names none of its body's own
/// names. `reader` is the branch the scope ends in — the root (`None`), at the operation's
/// boundary — and `mark` where it began ([`TypingEnv::memory_mark`]; 0 there).
pub(crate) fn charge_local_writes(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    reader: &BranchPath,
    end: ScopeEnd,
    mark: usize,
    effects: &[Value],
) -> Vec<Value> {
    let scope = env.memory_scope();
    let is_local = |kb: &KnowledgeBase, label: &Value| {
        extract_effect_resource_sym(kb, label).filter(|sym| scope.binding(*sym).is_some())
    };
    let mut out: Vec<Value> = Vec::with_capacity(effects.len());
    let push = crate::kb::region::push_effect_dedup;
    for label in effects {
        let Some(name) = is_local(kb, label) else {
            push(kb, &mut out, label.clone());
            continue;
        };
        for charge in charges(kb, &scope, name, reader, mark) {
            match charge {
                Charge::Param(p) | Charge::Kept(p) => {
                    let rekeyed = crate::kb::region::rekey_resource_value(kb, label, name, p);
                    push(kb, &mut out, rekeyed);
                }
                Charge::Pool(_) if end == ScopeEnd::Arm => push(kb, &mut out, label.clone()),
                Charge::Pool(pool) => scope.table.borrow_mut().pool_writes.push(PoolWrite {
                    label: label.clone(),
                    name,
                    pool,
                }),
            }
        }
    }
    out
}

/// The refusal of a write charged to a pool, at the operation `op_sym`'s declaration.
pub(super) fn pool_write_refusal(
    kb: &KnowledgeBase,
    op_sym: Symbol,
    span: Option<Span>,
    write: &PoolWrite,
) -> TypeError {
    TypeError::Other {
        site: TypeError::here(),
        span,
        context: TypeErrorContext::OperationEffects { op_name: op_sym },
        expected: "a write a row can declare".to_string(),
        actual: format!(
            "the write `{}` through `{}` reaches `{}`, state outside the process that no \
             effect row can name, so the write cannot be declared",
            type_display_name_value(kb, &write.label),
            kb.local_name_of(write.name),
            kb.qualified_name_of(write.pool),
        ),
    }
}

/// The memory half of Γ as the resolver's bridge reads it ([`ResolveConfig::memory`]): the
/// body's record and the branch the question is asked in. It answers `memory_alias` and
/// `memory_maybe_connected` over two places (050.1 §1) — the one source of both relations,
/// which is why a callee's memory clause is not assumed into Γ as a fact.
#[derive(Clone)]
pub(crate) struct MemoryView {
    scope: MemoryScope,
    branch: BranchPath,
}

/// What [`MemoryView::answer`] says of a memory relation over two places.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum MemoryAnswer {
    Holds,
    Fails,
    /// Neither: each place reaches the memory of a different parameter (or a parameter's and
    /// a pool's), and the caller may pass one cell twice (§1.2). Also the answer for an
    /// operand that is no place.
    Unknown,
}

impl FlowEnv {
    /// This Γ, answering the memory relations from `scope` ([`MemoryView`]).
    pub(super) fn with_memory(mut self, scope: MemoryScope) -> FlowEnv {
        self.memory = Some(scope);
        self
    }

    /// The memory half of this Γ, for the resolver's bridge.
    pub(crate) fn memory_view(&self) -> Option<MemoryView> {
        self.memory.as_ref().map(|scope| MemoryView {
            scope: scope.clone(),
            branch: self.branch.clone(),
        })
    }
}

impl MemoryView {
    /// `goal` answered as a memory relation, or `None` when it is not one.
    pub(crate) fn answer(&self, kb: &mut KnowledgeBase, goal: &Value) -> Option<MemoryAnswer> {
        let (relation, a, b) = memory_relation(kb, goal)?;
        let (Some(a), Some(b)) = (a, b) else {
            return Some(MemoryAnswer::Unknown);
        };
        if a == b || (relation == MemoryRelation::Alias && self.alias_root(a) == self.alias_root(b))
        {
            return Some(MemoryAnswer::Holds);
        }
        let (Some(ra), Some(rb)) = (self.place_regions(kb, a), self.place_regions(kb, b)) else {
            return Some(MemoryAnswer::Unknown);
        };
        let ra = connected_regions(&self.scope, &ra, &self.branch);
        let rb = connected_regions(&self.scope, &rb, &self.branch);
        let meet = ra.iter().any(|r| rb.contains(r));
        let outside = |rs: &[Region]| -> Vec<Region> {
            rs.iter().copied().filter(|r| !matches!(r, Region::Fresh(_))).collect()
        };
        let (oa, ob) = (outside(&ra), outside(&rb));
        // Separate: they do not meet, and one reaches no outside region, or both reach
        // only pools, which are distinct state, or every pair of parameters they reach is
        // one the operation requires disconnected (§1, "separate"; §1.2).
        let required = |x: &Region, y: &Region| match (x, y) {
            (Region::Pool(_), Region::Pool(_)) => true,
            (Region::Param(p), Region::Param(q)) => self.scope.required_apart(*p, *q),
            _ => false,
        };
        let separate = !meet
            && (oa.is_empty()
                || ob.is_empty()
                || oa.iter().all(|x| ob.iter().all(|y| required(x, y))));
        Some(match relation {
            MemoryRelation::MaybeConnected if meet => MemoryAnswer::Holds,
            _ if separate => MemoryAnswer::Fails,
            _ => MemoryAnswer::Unknown,
        })
    }

    /// The name `sym`'s value is, through every alias of a whole value — not of a field,
    /// which is another resource in the same memory.
    fn alias_root(&self, mut sym: Symbol) -> Symbol {
        while let Some(Binding::Alias { head, whole: true }) = self.scope.binding(sym) {
            sym = head;
        }
        sym
    }

    /// The regions the place `sym` lies in: a parameter, a local name, a pool's constant.
    /// `None` for a name the record does not know.
    fn place_regions(&self, kb: &mut KnowledgeBase, sym: Symbol) -> Option<Vec<Region>> {
        if self.scope.is_own_param(kb, sym) || self.scope.binding(sym).is_some() {
            let mut out = Vec::new();
            name_regions(kb, &self.scope, sym, &mut out);
            return Some(out);
        }
        kb.has_kind(sym, crate::intern::SymbolKind::Entity)
            .then(|| vec![Region::Pool(sym)])
    }
}

