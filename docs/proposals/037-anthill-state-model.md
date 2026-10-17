# 037: The Modify Effect Framework

## Status: Draft, revised 2026-10-17 under WI-20261017-T34HP. The model below was decided in discussion with the user on 2026-10-17; each decision is recorded on that ticket (decisions 1, 3, 4 and 5, the Branch decision, the rule-body decision and its amendment). This revision replaces the 2026-05 draft, and §9 lists what it withdraws. Nothing here is implemented beyond what §8 says exists today.

## Tracks: WI-20261017-T34HP (this revision, and the proposals it brings into agreement). WI-200 (multi-instance state; its scope follows from §3 and §5). WI-078 (h) (handler scoping, §5.2). WI-070 (Branch, §6.2).

## Relates to: [027](027-effect-handlers-and-standard-effects.md) (effect handlers and the standard effects; for `Modify`, its handler model and its catalog entry are superseded by §4–§6), [027.1](027.1-alloc-effect-and-allocator-revision.md) (allocation is `Modify[result]`), [027.4](027.4-error-effect-reify.md) (the `Error.reify` frame, which §5.2 reuses), [038](038-builtin-sorts.md) (host bindings, the default implementation of §4.2), [045](045-effect-sets-and-expressions.md) and [046](046-region-tracking-and-effect-derive.md) (rows, places, masking), [047](047-effects-as-monads-via-reflection.md) (its reading of `Modify` as State through a requirement slot is not taken, §9), [050.1](050.1-memory-alias-and-maybe-connected.md) (memory relations: freshness and sharing, §3), [054](054-external-effect.md) (state outside the process), 072 (constructor contracts, `requires` and `ensures` on an entity declaration; to be written; §3.3 needs it), `docs/kernel-language.md` §5.5–§5.7.

## The problem

`Modify[x]` is precise statically: it names a place, and the frame condition holds per resource. Nothing at run time matches it.

- **Four write paths, three ways of identifying a resource.** `Cell`'s operations write the interpreter's arena directly, and a cell is its slot. `ModifyRuntime.get`/`set` reach one global handler, which keys anything but a cell by its functor. A store is found through the KB's mirror by its printed value. The KB is written directly.
- **`ModifyRuntime` declares `get` and `set` for every `T`.** It is Cell's protocol offered to every sort, and it accepts a value of a sort that has no operations of its own.
- **The handler registry is global and flat.** It takes a handler out of its slot while the handler runs, so it can be neither scoped nor wrapped.

The 2026-05 draft of this proposal made identity "a property of the handler". The typer cannot rely on that. Its masking, its frame condition and 050.1's alias relations all depend on which places can be one resource, and the handler's choice of one slot per functor made `box(id: 1)` and `box(id: 2)` one place (WI-200; refused at run time since 2026-10-16, F1 of WI-20260908-9WVT7).

## 1. What `Modify` says

`Modify[x]` on an operation says the operation may change the state reachable from the place `x`: a parameter, `result`, a field path, or a zero-argument accessor. Anything that shares no state with a place in the row is unchanged by the call (kernel-language §5.6; with 050.1, "`Modify[x]` modifies everything connected to `x`"). The label is the same for every resource, and reading is silent (Rules 2 and 3).

This section changes nothing. The rest of the proposal says what happens at run time.

## 2. Base and secondary modifiable sorts

- **A base modifiable sort** holds its state outside every anthill value: in the interpreter, in the host, or in the world. Only its own operations change that state.
- **A secondary modifiable sort** is written in anthill over the base resources it holds, in fields or type arguments.
  - Its mutating operations are anthill bodies over base operations: `MutableStack.push` is `Cell.set(s.rep, …)`.
  - It has no identity of its own. Two of its values are one resource exactly when they hold the same base resources.
  - It is modifiable by containment, and an `internal` constructor keeps its invariants (WI-369).
- **A pool sort** is a modifiable sort whose only value names state outside the process, for the typer (§3.2). It has no operations and no implementation. Nothing writes it directly, and at run time nothing is bound to it.
- **Persistent values are not resources.** `Map.put` and `Substitution.compose` return new values.

The typer already draws this line. A base sort is one that a `provides Modifiable[T = …]` names, directly or through a spec it provides (`region::region_sorts`). A secondary sort is admitted through its fields and type arguments (`region::type_admits_modify`). `Modifiable` stays a marker spec, with no dictionary.

| Base sort | How a resource comes to be | How a call finds its implementation | Default implementation |
|---|---|---|---|
| `Cell` | `Cell.new`, fresh | its handle | the interpreter's arena |
| `KB` | `kb()`, the root; or a `loaded(…)` layer | its handle | the interpreter |
| the `Store` family | its value names a root and a convention | the mount of its key | the KB's store mirror |
| the webots devices, guardians' `Mailbox` | declared only | — | — |

## 3. Identity

### 3.1 Identity belongs to the sort

What tells two resources of a sort apart is fixed by the sort, never by an implementation of it. An implementation may change how state is stored, never which resource is which.

### 3.2 Freshness and sharing come from memory postconditions

Whether a write may be dropped from a row, and whether two places may be one resource, is read from 050.1's memory relations, as it is for every other operation. There is no identity kind.

- **An allocating operation declares no memory clause, so its result is fresh,** connected with nothing. `Cell.new` is the case. A write to a cell that never escapes is local, and is dropped from the row (the masking of WI-314).
- **A value that names something outside is connected to a pool**, `ensures memory_maybe_connected(result, pool)`, where `pool` is the constant of a pool sort (§2), an ambient resource standing for that outside state. Such a value is never fresh, and any two values connected to one pool may be one resource. 050.1's decision D is the precedent: `operation kb() -> KB ensures memory_alias(result, kb)`.
- **The pool belongs to what the values name, not to their sort.** `FileStore(root: "x", …)` and `IndexedFileStore(root: "x", …)` name one directory, so the three file backends share one pool. It is declared once, in `anthill.persistence.filesystem`, the module that declares all three:

  ```anthill
  sort FileStorage
    provides Modifiable[T = Self]
    entity file_storage
  end
  ```

  Memory relations are untyped: they connect places of any types, as `box(cell: c)` lies in `c`'s regions. The `Modifiable` claim is there for the row. 050.1 charges a write through a store the body built to the outside region it reaches, so a row may carry `Modify[file_storage]` ("may change the file storage"), and the TR8CF check admits a `Modify` target only over a modifiable type. While 050.1 §1 keeps its filter on which places take part in relations, the claim also lets the pool pass it. A store backed by something else, such as a database, declares its own pool sort (`DatabaseStorage`) in its own module, so it is not connected with the files.

### 3.3 The constructor says so

In an operation body a constructor is a call like any other (kernel-language §5.4), so a keyed sort's constructor declares the connection:

```anthill
entity FileStore(root: String, convention: FileConvention)
  ensures memory_maybe_connected(result, file_storage)
```

An entity declaration cannot carry `ensures` today. Proposal 072 adds it, together with `requires`, as constructor contracts. In a clause a constructor is a term, not a call, and a fact writes nothing, so the `ExtentBinding` facts that name stores are unaffected.

### 3.4 At run time

A value finds its implementation through its handle when an allocating operation made it. When it is plain data, it finds it through the mount of its key (§5.1). A mount key provides total `Eq`, as `Map`'s keys do (`requires Eq[T = K]`), and a value whose type has a `NonEq` witness is refused as one. Identity follows `Eq`, not the canonical printing the store mirror keys by today.

### 3.5 A sort with no operations of its own has no resource

Nothing writes such a sort, whatever it claims. `Box` and `counter` in the m5 fixtures were written only through the generic `ModifyRuntime.set`. Under this proposal that call is a load error, and `default_modify_handler`'s map, which kept one slot per functor for them, goes. WI-200's goal, two boxes kept apart by that handler, has no counterpart. State keyed by data inside the process is a `Map` held in a `Cell`.

A pool sort (§2) also has no operations, and is still modifiable. It names outside state for the typer, and nothing at run time is bound to it.

## 4. Implementations

### 4.1 No generic runtime spec

A base sort's runtime is its own state operations: the mutating ones, the reads and the allocation. No `ModifyRuntime` spec ranges over them. A spec fixes its operations, so one with `get`/`set` forces Cell's protocol on every sort, and one with none says what the base `Modifiable` claim says. The stdlib's `ModifyRuntime` and Cell's `provides ModifyRuntime[T = Self, V = V]` go.

### 4.2 A handler is an implementation of a base modifiable sort

There is one implementation per handler.

- **The default implementation is the sort's host realization:** `provides S language rust { operation_map … }` (proposal 038), held to the sort's `@[host_implemented]` declarations at load (WI-20260922-BRT4Y). It is generalized from one realization per language, chosen at build time, to one per installation, chosen at run time.
- **Other implementations** (time travel, a test fixture, audit) implement the same operations over a different store. They never change identity.
- **An implementation that owns the state answers the reads too.**
- **Allocation is the implementation's.** It mints the identity and stores the initial value, which is `new`'s argument.
- **Lifetime is the implementation's.** A handle is reclaimed by reference count, and a mount lasts until its key is unmounted.

### 4.3 Host code, for now

An implementation is host code. One written in anthill needs a design of its own, later, which provides:
- a form that declares an implementation of a sort;
- a check of its operations against the sort's signatures, as `check_override_refinement` checks a provider against its spec;
- a way to name the implementation it wraps;
- possibly a type for "an implementation of `S`", for code that passes one to an installing operation.

## 5. Binding and installation

### 5.1 Each resource is bound to one implementation

Every call on a resource goes to the implementation the resource is bound to.

- **A resource made by an allocating operation** is bound when it is made, to the implementation that made it, and its handle remembers which. A Cell handle already reads the arena that minted it (WI-20260923-9R5HN).
- **A resource whose value is plain data** is bound when its key is mounted, and is found by its key.

An implementation lives as long as the resources bound to it. A call on a key that is not mounted fails loudly, as `persistence_retrieve`'s "no store registered for key" does today.

### 5.2 Installing chooses the binding

Installing an implementation decides what the resources made or mounted while it is in force are bound to.

**The installation map.** The implementations in force are a persistent map from a base sort, keyed by its canonical symbol, to an implementation.
- **The key is the sort, not a hash of a full type,** because an implementation serves every instantiation of its sort: one Cell implementation for every `V`.
- **The map is read only when a resource is made or mounted,** to choose its binding. A call on an existing resource never reads it (§5.1).
- **Because the map is persistent:**
  - a scope is a new version of the map with one entry changed, and leaving the scope, normally or by a raise, returns to the previous version. There is no enter/pop pair to get wrong, the principle WI-20260823-SPGBP chose for scoped KB layers;
  - an implementation installed over a version can capture the entry it replaces, and pass calls on to it (item 3);
  - a Branch snapshot copies the activation stack, and the current version comes along at no cost;
  - the bridge can hand the current version to a scratch interpreter as one shared reference (§5.4).

1. **Extent.** There is a whole-run default version, chosen by the embedder at startup. Inside the program there are scopes, installed by an ordinary higher-order operation that works as the `Error.reify` frame does (027.4). Its frame sets the new version on entry, and its exit or unwind restores the previous one, so scopes nest.
2. **A scope affects the allocations that run inside it**, not the code written inside it. A closure made inside a scope and called outside it allocates under its caller's implementation.
3. **Wrapping.** An implementation may wrap another and pass calls on to it, which is how audit and logging are expressed. A wrapper sees only the resources bound to it. The registry must allow this: today `EffectRegistry::take_for_invoke` takes a handler out of its slot while it runs, so a handler cannot reach another.
4. **Compiled code** fixes the default implementation at build time. Choosing another at run time is an interpreter feature.

### 5.3 The default is always available

The default is available in a normal run, in a rule body's run, and in load-time evaluation of a `const`.

A local allocation in pure-typed code follows the same rule as any other: the implementation in force where it runs serves it. So an implementation installed for a scope also sees the private cells of pure code (decision 3). That breaks nothing the typer promised, because an installed implementation is host code outside the program's semantics. No channel carries the typer's masking decision to the evaluator. The run-time side of masking is simply that the default is always present.

### 5.4 Rule bodies

A call from a rule body runs in a scratch interpreter, the SLD→eval bridge.
- **A pure call**, one whose row after masking holds no `Modify`, runs with each sort's default, as today. Its private cells are its own.
- **A call that modifies shared state** would inherit the installations of the querying interpreter: the current version of the installation map. Under WI-20260926-7D48J's rule no such call runs in a rule body, so today every bridged call runs with the defaults.

With `Branch` implemented (§6.2), a rule-body call may need no child interpreter at all. That is a future question.

## 6. Composition

### 6.1 With `Error`: a raise keeps the writes made before it

When `Error.reify` catches a raise, the writes made inside its boundary stay. That is the runtime's behaviour today, it is ordinary exception semantics, and it is the only behaviour that state outside the process admits.

Kernel-language §5.7's stack is to read `ExceptT Err (StateT Env …)`. Its current `StateT Env (ExceptT Err …)` says a raise rolls state back.

Rollback, where it is wanted, becomes an explicit construct for later: a transaction scope (047 §7). The bound implementation can provide it by keeping old values while the scope is open.

### 6.2 With `Branch`: an abandoned alternative's writes are undone

Each alternative starts from the state at the branch point. In `pick(c) = branch((let _ = Cell.set(c, 1); Branch.fail()), Cell.get(c))`, the second alternative reads `c`'s old value.

This differs from a raise. A caught raise is a computation that happened and failed; an abandoned alternative never happened, and alternatives must not depend on the order in which they are tried.

- **The undo is done by the implementation each resource is bound to.** It keeps old values while a branch is open, and restores them when an alternative is abandoned: the `register_undo` design of 027 and `docs/design/cell-runtime.md`. Every implementation of a base sort owes this.
- **State outside the process cannot be undone.** So an operation that writes it declares `External`, as 054 defines outside state, and `Branch` together with `External` is refused at load (054). The store operations that reach the disk do not declare it yet: they declare `{Modify[store], Error}`, so today a Branch region calling `Store.flush` would be neither refused nor undoable. Adding `External` to them closes that gap (§8).
- **SLD backtracking needs nothing,** since a rule body writes no shared state (§5.4).

This is the contract WI-070 implements.

### 6.3 With other `Modify` effects

`Modify[s]` covers what is reachable from `s`. A field path coarsens to its head at a call, so `Modify[s.rep]` is covered by `Modify[s]` (WI-506), and under 050.1 a write through a place connected to `s` is `Modify[s]`. A row does not have to list each base resource a secondary value holds.

### 6.4 With time travel

These invariants keep signatures fit for a time-travel implementation, so that one can replace the default without changing a program:

1. `set` means "the next `get` returns the value".
2. `get` returns the current value. History is read under a separate effect.
3. No signature exposes an implementation's internals, such as version ids or snapshots.
4. `set` returns `Unit`, not the prior value.
5. No signature encodes rollback; §6.1 and §6.2 fix it for every operation.

## 7. Rules

1. **Every mutation declares `Modify[x]`.**
2. **`Modify` is uniform across resources.** The place distinguishes them.
3. **Reading is silent.**
4. **An operation's signature does not depend on which implementation answers it.**
5. **One operation per mutation.** Whether a write survives a raise or an abandoned alternative is fixed by §6, never by the operation or by an implementation. There are no `set_local`-style variants.
6. **Identity is the sort's** (§3), stated through memory postconditions. An implementation never changes it.
7. **Signatures stay fit for time travel** (§6.4).
8. **`Modify` applies only where the place's type admits it.** This is enforced since WI-20260823-TR8CF: a base sort admits it through its `Modifiable` claim, a secondary sort through containment. A base sort has a default implementation, which WI-20260922-BRT4Y holds to its declarations.

## 8. Today, and what changes

`docs/design/037-implementation.md` will give the plan. In summary:

**What exists:**
- the Cell arena, with slot identity (WI-205);
- masking (WI-314);
- the `Modifiable` check (TR8CF);
- the `Error.reify` frame (027.4);
- the host-binding check (BRT4Y);
- a flat registry that interprets `Pure` and `Throw` (WI-389).

**What changes:**
- `ModifyRuntime` and the functor map are retired, and the m5 `Box` and `counter` fixtures become load errors;
- every base operation goes to the implementation its resource is bound to, `Cell.*` included (the user's direction, WI-20260908-9WVT7 note F10). Stores keep finding theirs by mounted key;
- the flat registry is replaced by the installation map (§5.2), which lets an implementation wrap another, and the scoped installing operation is added (WI-078 (h));
- every implementation gets mark and undo, for `Branch` (WI-070);
- the store operations that write outside the process declare `External`, and so do their callers, anthill-todo's commit path among them. 054's refusal then covers them under `Branch`;
- in the spec, §5.6 adopts 050.1 §6's text on resources and memory, and §5.7 takes the stack of §6.1, each written only after its wording is agreed;
- proposal 072 adds a constructor's `ensures`.

## 9. What this revision withdraws

From the 2026-05 draft, and from 027, 036 and 047 where they say the same:

- identity as "a property of the handler", `ModifyHandler[Resource, IdentityKey]`, and the menu of schemes a handler picked from (functor-only, by key, opaque handle);
- `Modify[T]` read over a type. A target is a place (WI-20260823-39AD2);
- `Cell.new` as allocation free of effects. It declares `Modify[result]` (027.1);
- per-resource branch contracts (branch-local snapshot, frozen, sticky-by-physics), replaced by §6.2's single rule and 054's refusal;
- the handler stack, where a call went to whichever handler was on top at that moment. §5 replaces it: a call goes to the implementation its resource is bound to, and the installation map is read only when a resource is made or mounted.

Considered and not taken in the 2026-10-17 discussion:

- dispatching a call by what is installed at the call, which splits a resource's state between implementations;
- interceptors that see every call, whatever it is bound to, since they need a definition the type system cannot express yet;
- `Modify` as State through a requirement slot (047), and `Modifiable` as a slot that carries a dictionary;
- an identity kind per sort (allocated or keyed), whether declared or derived;
- rolling state back on a raise.

## 10. Open questions

- Implementations written in anthill (§4.3), and interceptors.
- The name and signature of the scoped installing operation.
- A transaction scope that rolls back on a raise (§6.1).
- A rule-body call with no child interpreter, once `Branch` exists (§5.4).

## Acceptance

1. §1–§7 are agreed with the user as binding for the Modify framework.
2. 027, 027.1, 036, 047 and 050.1 point here where they touch these questions, or mark what they say as superseded (the second step of WI-20261017-T34HP).
3. The spec changes of §8 are written, after their wording is agreed.
4. `docs/design/037-implementation.md` is written.
