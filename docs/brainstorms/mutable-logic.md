# Mutable logic

 I see, people and agents often by defaut, when start describing some domain rules start produce something like 
    ~rssh/packages/alexzhyshko/prose-v-progressive-formalization/anthill/shop.anthill 
   i.e. thibk that knowledge base and state are the same and keep state in the knowledge base.

   But state is mutable.
    So, what we do 

    variants
      - linear logic.  
          I'm not very happy with :- as --*  - maybe we should have something like mutable predicates and special clause for it
      - metalogic operations (assert/retract)
          but I'm not sure that it is possible to do 
      - explicit dependency from time.
      - something else?

    Can you do deep research anout existing approaches and give me an overview, than we can brainstorm

## Overview of choice and backtracking

Suppose two rules can consume the only occurrence of `B`. One produces `D1`, the other `D2`. The engine tries the `D1` path, then a later goal needs `D2`. Can the engine recover `B` and try the other path?

| System | Can a later failure retry the choice? | How the choice works |
|---|---|---|
| **Lolli** | Yes, during proof search. | A failed continuation can return to the choice point. The alternative proof can use the original linear assumption `B`. [Hodas & Miller, *Logic Programming in a Fragment of Intuitionistic Linear Logic*](https://www.lix.polytechnique.fr/Labo/Dale.Miller/papers/ic94.pdf) |
| **LolliMon** | Yes in backward proof search. No after a forward step fires. | Each successful atomic forward step discards the choice points used to select and prove that step. [López et al., *Monadic Concurrent Linear Logic Programming*, §3.4](https://www.cs.cmu.edu/~kw/pubs/ppdp05.pdf#page=7) |
| **Simmons & Pfenning's Linear Logical Algorithms** | No after a linear rule fires. | An execution follows one enabled transition. In the tournament example, the chosen winner advances and subsequent results cannot reopen that match. [*Linear Logical Algorithms*, §2, Figure 2](https://www.cs.cmu.edu/~fp/papers/icalp08.pdf#page=4) |
| **Ceptre** | No within the same execution trace. | The engine described in the paper chooses an applicable rule at random by default. An interactive stage lets the player choose. If the resulting stage has no enabled rule, it reaches quiescence. [Martens, *Ceptre*, “Interactive Rulesets” and “Stages and Quiescence”](https://www.cs.cmu.edu/~cmartens/ceptre.pdf#page=3) |

For Anthill, the placement of an acceptance check determines the behavior. A guard checked before firing can rule out `D1` while `B` is still available. A goal checked after a committed `KBChange` sees the resulting facts. LolliMon provides a precedent for combining backtracking proof search with a committed forward step.

## The question raised by the shop and Guardians

The shop author wrote this fact and a rule that uses it:

```anthill
fact Stock(2, 200, 54)

rule available(?p, ?a) :-
    Stock(product: ?p, onHand: ?h, reserved: ?r), ?a <=> ?h - ?r
```

To the author, this says that product 2 has 200 units on hand, 54 of them reserved. They ask `available(2, ?a)` and expect 146. The first Guardians model did the same with `fact InMailbox(...)` and `fact KnownContact(...)`. Neither author wrote a state variable. The explicit shop was a later experiment. **Can these facts themselves serve as the application's data, even when that data changes?** [Original shop facts](https://github.com/alexzhyshko/prose-v-progressive-formalization/blob/d1a57975eebd1e7b2233ff7592466bd86c8f2b42/anthill/tests/ok/basic.anthill#L3-L9) · [Shop rule](https://github.com/alexzhyshko/prose-v-progressive-formalization/blob/d1a57975eebd1e7b2233ff7592466bd86c8f2b42/anthill/shop.anthill#L25-L34) · [Initial Guardians fixture](https://github.com/rssh/anthill/blob/266245d78e354b4fb1b478111207bc7c0e6bf85e/examples/guardians/fixtures/mailbox.anthill#L20-L30)

My candidate answer is the deductive-database reading. `Stock` is a stored relation. `available` is a rule over its rows. A fixture can supply the stock facts literally. A running shop could supply the same facts from its inventory store. When that store replaces the product's row with `Stock(2, 200, 55)`, the next query of `available(2, ?a)` should answer 145. The shop author can write exactly the two declarations above even if another system makes every inventory change. [Anthill extent sources](../proposals/057-extent-seam.md)

Guardians gives a test of this reading using only an addition. Its rule for `sender_not_in_contacts` looks up a message and checks whether its sender is absent from `KnownContact`. Add that address to the address book and the next query should stop reporting that message as coming from an unknown sender. The rule already expresses everything the author needs to know about that change. [Original Guardians rule](https://github.com/rssh/anthill/blob/266245d78e354b4fb1b478111207bc7c0e6bf85e/examples/guardians/lib/classify.anthill#L46-L53)

### A linear-logic interpretation of the shop

In a single rule firing, `consume` removes the matched occurrences of stored facts and `produce` adds the facts specified by the rule. [Simmons & Pfenning, *Linear Logical Algorithms* (2008), §2, Figure 2](https://www.cs.cmu.edu/~fp/papers/icalp08.pdf#page=4)

#### Implemented languages with these operations

**Ceptre** has a particularly small example in its game code:

```text
train : turn * stamina * $alive -o skill.
```

The rule consumes one `turn` and one `stamina`, requires and keeps `alive`, and produces one `skill`. The `$` on a premise preserves that occurrence when the rule fires. This gives an author three distinct ways to mention a fact in a single rule: read it, consume it, or produce it. [Executable example](https://github.com/chrisamaphone/interactive-lp/blob/master/examples/rpg-tiny.cep) · [Chris Martens, *Ceptre: A Language for Modeling Generative Interactive Systems* (2015)](https://www.cs.cmu.edu/~cmartens/ceptre.pdf)

Operationally, this is **multiset rewriting**, the idea behind chemical programming in Gamma. Facts play the role of molecules. One reaction replaces its matched molecules with its products and carries the rest of the solution forward. Berry and Boudol's Chemical Abstract Machine takes up Gamma's model and adds membranes for local reactions. Ceptre gives resource consumption a linear-logic reading. [Banâtre & Le Métayer, *The Gamma Model and Its Discipline of Programming*](https://www.sciencedirect.com/science/article/pii/016764239090044E) · [Berry & Boudol, *The Chemical Abstract Machine*](https://www-sop.inria.fr/members/Gerard.Boudol/tcs96.html) · [Martens, *Ceptre*, operational semantics](https://www.cs.cmu.edu/~cmartens/ceptre.pdf#page=3)

For Anthill, this raises a choice about **what triggers a firing**. A reaction engine could fire `Request(cart, p, q) ⊗ Stock(p, h, r) ⊸ …` when matching facts are present and its guard holds. With a `KBChange` operation, calling `reserve(cart, p, q)` supplies the request and attempts one firing. Both readings consume the same stock occurrence. Only the former needs a policy for choosing the next enabled reaction.

With one occurrence of `A` and two rules `A ⊸ B` and `A ⊸ C`, there are two possible next configurations, `{B}` and `{C}`. Committing either consumes the only `A`. The logic gives both possibilities equal standing and assigns them no probabilities. In the engine described in the Ceptre paper, automatic stages choose randomly among applicable rules, and an interactive stage lets an external participant choose. For the proposed Anthill design, a caller could choose between two named operations. If both clauses implement the same operation and both guards hold, selecting the operation still leaves a choice between clauses. An abstract interpreter answering “what can happen?” must cover both outcomes. [Ceptre, *Interactive Rulesets*](https://www.cs.cmu.edu/~cmartens/ceptre.pdf#page=3)

| Language | What it contributes to the Anthill design |
|---|---|
| **Linear Meld (LM)** | A forward-chaining logic language with persistent facts and linear facts. Its rule-application semantics explicitly identifies consumed linear facts, produced linear facts, and produced persistent facts. This is a model for giving `KBChange` a formal meaning. [Cruz et al., *A Linear Logic Programming Language for Concurrent Programming over Graph Structures* (2014), Table 2 and Figure 5](https://www.cs.cmu.edu/~fp/papers/iclp14.pdf) |
| **Constraint Handling Rules (CHR)** | SWI-Prolog implements the guarded form `Kept \ Removed <=> Guard \| Body`. It finds matching constraints, tests the guard, keeps the first group, removes the second, and runs the body, which can introduce new constraints. This directly addresses how a guard selects occurrences to consume. [SWI-Prolog, *CHR Syntax and Semantics*](https://www.swi-prolog.org/pldoc/man?section=chr-syntaxandsemantics) |
| **Linda** | A precedent for separate operation calls. `in(pattern)` withdraws one matching tuple, `out(tuple)` deposits one, and `read(pattern)` observes one. A sequence of `in` and `out` calls has intermediate steps. Anthill would have to supply a commit boundary if the sequence represents one logical change. [David Gelernter, *Generative Communication in Linda* (1985)](https://cseweb.ucsd.edu/groups/csag/html/teaching/cse291s03/Readings/p80-gelernter.pdf#page=3) |

#### A stock operation

An ordinary rule `H :- B` means that if `B` holds, then `H` holds. Asking for `H` lets the resolver try to prove `B`. The facts used by that proof remain available. For a reservation, the author also needs to change stored facts. One place to express that is the body of an ordinary operation on a KB. In this sketch `rewrite db`, `consume`, `when` and `produce` form a proposed expression, and `Reservation` is an illustrative stored record.

```anthill
operation reserve(db: KB, cart: Int64, product: Int64, qty: Int64) -> Bool
  effects {KBChange[db], Error}
  = rewrite db {
      consume Stock(product: product, onHand: ?h, reserved: ?r)
      when qty > 0, qty <= ?h - ?r
      produce Stock(product: product, onHand: ?h, reserved: ?r + qty)
      produce Reservation(cart: cart, product: product, quantity: qty)
    }
```

With the fixture's `Stock(2, 200, 54)` in a writable `shopDb`, calling `reserve(shopDb, 17, 2, 1)` replaces that stock row and creates one reservation for cart 17. A fresh query of `available(2, ?a)` gives 145. The proposed expression returns true when all edits commit together, false when there is no eligible stock row, and raises an error on a storage failure. This example assumes the shop's one-row-per-product invariant and treats the stock row and reservations as resident facts. `KBChange[db]` is a proposed effect. The existing `KB.assert` takes a KB parameter and declares `Modify` on it. Providing a writable handle to the caller is a separate design question, since the kernel refuses a write through the ambient `kb()`. [KB declaration](../../stdlib/anthill/reflect/reflect.anthill) · [Kernel §5.6](../kernel-language.md)

The call supplies the request to act. To see the linear reading, represent that request as a one-use premise:

```text
Stock(p, h, r) ⊗ Request(cart, p, q)
    ⊸ Stock(p, h, r + q) ⊗ Reservation(cart, p, q)
    when 0 < q and q ≤ h - r
```

Here `⊗` means the facts are available together. Firing `⊸` consumes one occurrence of each fact on the left and produces the facts on the right in one step. The rule itself remains available. Start with `Stock(2, 1, 0)` and one request each from carts A and B for product 2. Either request can succeed. If A's fires, B's request is still present, but the stock fact is now `Stock(2, 1, 1)`, so B's guard fails. That follows from the rule and the available facts. There is no state parameter or clock in the clause.

**What should an ordinary Anthill rule mean alongside this?** I would keep `available` as a read-only query. Asking it twice inspects the same stock occurrence twice. Asking whether A's request *could* succeed also leaves it available for B. Only firing a named action consumes facts. A proof of `available(2, 1)` depends on the occurrence `Stock(2, 1, 0)`. Once that occurrence has been consumed, its proof cannot justify the same answer about current inventory. In particular, a derived answer must never be promoted to a permanent fact merely because the clause deriving it is reusable. LolliMon is a precedent for combining backward proof search with a distinct form of forward, committed computation. [Monadic Concurrent Linear Logic Programming](https://www.cs.cmu.edu/~kw/pubs/ppdp05.pdf)

For this combination to be sound, the resolver would need to give each query one consistent collection of facts for all its premises, including later answers and negated subgoals. For Guardians, concluding that a sender is absent requires a definitive membership answer for that address in the same address book the query observes. An incomplete search or an unavailable address book cannot establish absence. A proof reused across queries needs its dependencies checked, including absences it relied on. Anthill's extent-source draft already discusses observation scope, negative answers, and cached proofs. [Extent-source design](../proposals/future/extent-sources.md)

Linearity supplies a specific guarantee: the same occurrence cannot fund two committed reservations. The shop's separate invariant of one stock row per product still matters. Two initial stock rows would be two resources, and a badly written action could produce two successors. The invariant must hold initially and each admitted action must preserve it, by proof or by checking its complete result. A concurrent implementation must also prevent two commits from consuming the same occurrence. These are concrete obligations against which to judge a proposed Anthill facility.

The first facility I would explore is a special clause for consuming and producing stored facts, alongside ordinary `fact` and `:-`. A declaration of which predicates may be consumed could be made once per predicate. Proposal 053 already answers whether a store permits removal. The additional question for the language is whether a clause can name the resources it consumes and what it produces as a single logical step. [Per-functor fact monotonicity](../proposals/053-fact-mutability.md)

### Analyzing calls to KB.consume and KB.produce

One design is to make `KBChange[db]` an effect with two primitive operations. `KB.consume(db, ref)` takes one stored fact occurrence identified by its reference. `KB.produce(db, fact)` adds one occurrence and returns a reference to it. The pattern in the reservation clause selects the stock row and binds its fields. On the successful path, its edits amount to the following proposed calls:

```text
KB.consume(db, matchedStock)
KB.produce(db, replacementStock)
KB.produce(db, reservation)
```

The signature tells a caller which KB the operation may change. The checker would treat `KBChange[db]` as a write to `db` wherever the current effect system checks which resources an operation can modify. Anthill combines effect rows by set union, so all three calls contribute a single label. To analyze the edits, keep their order, operands and multiplicity from the body. Inside the rewrite, later calls see earlier staged edits. The successful path commits the three edits together. [Kernel §§5.5–5.6](../kernel-language.md)

For example, two successive `KB.consume(db, matchedStock)` calls on the same path demand the same occurrence twice. The checker can show that this path cannot succeed. One consume in each of the two arms of an `if` is valid with respect to that reference because only one arm executes. At a helper call the checker needs the helper's body or a summary of its possible edits. A helper exposing only `KBChange[db]` tells the checker that its edits are unknown. The runtime must check identities or conflicts that depend on actual rows or concurrent callers. The signature, the static analysis of possible executions, and the runtime commit each answer a different question. [Gordon, *Polymorphic Iterable Sequential Effect Systems*](https://www.cs.drexel.edu/~csgordon/assets/pdf/papers/toplas21.pdf)

### A change described in the operation signature

The author's sketch puts the patterns themselves in the effect declaration. Here `?` renders the omitted `onHand` field in the consume pattern. The produced fact is left open as in the sketch.

```text
operation changeStock(i: Int64)
  requires Stock(i, ?onHand, ?reserved)
  effects KBChange {
    consume Stock(i, ?, ?reserved)
    produce ...
  }
```

If this declares the exact edits promised on successful return, a caller can use it to analyze a call to `changeStock` without opening its body. A mere permission to make those edits would give a weaker contract. Whether the declaration can also execute the rewrite is open.

#### Guard or explicit search?

For the stock part of reserving one unit, a **guard** could both find a stored row and test its fields. This sketch assumes the shop has at most one stock row per product.

```text
effects KBChange {
  guard stored Stock(i, ?onHand, ?reserved) as ?row, ?reserved < ?onHand
  consume ?row
  produce Stock(i, ?onHand, ?reserved + 1)
}
```

The guard binds the field values and a reference to the matching occurrence. If it has no match, the change is inapplicable and consumes nothing. If it succeeds, `consume ?row` removes exactly that occurrence. A derived predicate can help test eligibility, but a proof of `Stock(...)` alone supplies no stored row reference. An ordinary `requires` remains a precondition on the call. [Kernel §8.5](../kernel-language.md)

With an **explicit search operation**, the caller searches for stored `Stock` rows satisfying the same condition, chooses one result, and hands its reference to the change. This is useful when several rows qualify and the caller has a reason to choose one, such as the warehouse it plans to ship from. The change must verify that the selected occurrence and the fields used by its guard are still current when committing. The library already has a related operation, `KB.stored_facts_of`, which pairs stored values with references. The pattern search and guard syntax above are design options. [Stored row enumeration](../../stdlib/anthill/reflect/reflect.anthill)

Both forms could share the same stored-row search. The difference visible to the author is who chooses the occurrence. A unique-key update can let the guard choose it within the change. An explicit search gives that choice to the caller.

### Can a rule give us a next-state relation?

Yes. A linear implication `L ⊸ R` can describe a reusable rule whose individual firings consume the matched occurrences in `L` and produce `R`. Here is the stock part of reserving one unit, written as a possible `KBChange` declaration. The guard inspects the values bound by the match. The spelling is illustrative. A literal `--*` currently starts a line comment in Anthill. [Kernel §2.2](../kernel-language.md#22-comments)

```text
effects KBChange {
  Stock(i, ?h, ?r) ⊸ Stock(i, ?h, ?r + 1)   when ?r < ?h
}
```

The declaration supplies a **labelled, one-step relation**. Let `F` be the multiset of all other stored fact occurrences, and `⊎` multiset union. For each enabled match in a valid configuration whose result satisfies the invariants, the successful atomic firing gives:

```text
next(reserveOne(i), F ⊎ {Stock(i, h, r)}, F ⊎ {Stock(i, h, r+1)})
    when r < h
```

Only the semantics mentions `F`. All other stored rows carry forward. Derived answers such as `available` can change because their premises changed. The one-step meaning comes from counting **one firing of a named rule**. Given rules `A ⊸ B` and `B ⊸ C`, their composition proves `A ⊸ C`, but getting from `A` to `C` takes two firings unless a separate atomic rule specifies that step. [Simmons & Pfenning, *Linear Logical Algorithms*, §§2–3](https://www.cs.cmu.edu/~fp/papers/icalp08.pdf)

**What can abstract interpretation derive?** Give `KB.consume` and `KB.produce` transfer rules and compose them along each successful commit path. If the analyzer keeps the same symbolic `r` from the consumed row to the produced one, it can infer the relation `r < h ∧ h′ = h ∧ r′ = r + 1` for this example, or check a declared linear rule against the body. If it tracks only separate ranges, starting with `h = 200` and `r ∈ [54,55]` yields `r′ ∈ [55,56]`. Those two ranges alone also admit the pair `54 → 56`, which the rule cannot execute. A sound abstract relation covers every concrete step. Its additional possibilities cannot authorize a concrete write. This would extend Anthill's design for propagating facts through effectful operation bodies with knowledge of which row was consumed and which fields its successor inherits. [Anthill abstract-interpreter design, §6](../design/abstract-interpreter-and-rules.md) · [Cousot & Cousot, *Basic Concepts of Abstract Interpretation*](https://www.di.ens.fr/~cousot/COUSOTpapers/publications.www/Top4-Abst-Int-1-PC-RC.pdf)

#### Backtracking over proofs and choosing a successor

Assume the stored facts are `{B, C}`, one occurrence each. With `A :- B` and `A :- C`, asking for `A` has two proofs. Both inspect the same facts. Backtracking from one proof to the other leaves the store at `{B, C}`.

Suppose an operation explicitly chooses a witness for `A` and then fires **one** rewrite on the chosen occurrence. Its possible outcomes are:

| Chosen witness | Eligible rewrites on that witness | Possible committed stores |
|---|---|---|
| `B` | `B ⊸ D1`, `B ⊸ D2` | `{D1, C}` or `{D2, C}` |
| `C` | `C ⊸ E1`, `C ⊸ E2` | `{B, E1}` or `{B, E2}` |

The connection between proof and rewrite belongs to the operation. A plain `requires A` only establishes that `A` holds. If the operation needs to consume the witness, it must retain the selected stored occurrence. A hypothetical search can explore all four successors starting from the same input each time. A committed call realizes one successor. Under a different policy that keeps firing enabled reactions, the surviving `C` could still fire after a `B` step, or vice versa.

### What does Anthill have to decide?

Writing a second `fact Stock(2, 200, 55)` alongside the first asserts a second fact. The two declarations alone say nothing about one superseding the other. The author could equally well be describing two observations. The design choice is where the meaning of *replacement* comes from when a domain needs it.

| Choice | What the author writes |
|---|---|
| Put the policy on the predicate | Write ordinary facts. Designate `Stock` as replaceable once. To replace by product ID, also identify that field as its key. |
| Let the source supply the policy | Write ordinary facts in fixtures and ordinary rules in the library. The deployment binds `Stock` to inventory or `InMailbox` to a mail service. The source supplies the current rows and their identities. |
| Name the old fact in an update | Write ordinary facts. If an Anthill operation itself makes a reservation, its update can match the stored stock row and explicitly replace it. This can use a reference to the matched row. |

These choices can coexist. Anthill already gives each stored predicate a write policy. The default permits additions, and `non_monotone` permits replacement and removal. Its store API can update a row by reference. That gives us a starting point for supporting the observed style. The open language question is how much of this the domain author should have to spell out when they first need a write. [Per-functor fact monotonicity](../proposals/053-fact-mutability.md) · [Store operations](../../stdlib/anthill/persistence/store.anthill)

## Approaches to change

If a specification goes on to describe an action or to ask about history, the following approaches give it different expressive powers. Transaction Logic earns its place when an author wants to reason about a sequence of actions. Querying current inventory or a mailbox already makes sense with stored facts and ordinary rules.

| Approach | What an author could say about the shop | What adopting it would mean |
|---|---|---|
| **1. Implicit state in operation contracts** | In `registerCustomer`, the new customer and their cart exist on return. In `checkout`, every cart line present on entry supplies an order line with the same quantity and captured unit price on return. | Ordinary goals in `requires` use the entry state and those in `ensures` use the return state. An explicit qualifier is needed only to refer across that boundary. A contract can remain partial while the implementation is still `todo()`. Alloy 6 offers a close precedent for the notation: mutable relations have an implicit current value and an expression can select its next value. [Alloy 6](https://alloytools.org/alloy6.html) |
| **2. Declarative updates over stored facts** | A registration clause proposes inserting a specific customer and cart. Both edits are computed against the same starting shop. | U-Datalog collects inserts and deletes while solving a goal and applies consistent updates in a second phase. An Anthill variant could restrict edit-producing clauses to operations and validate the complete candidate shop. Rows outside the edits carry forward automatically. A design choice is whether multiple answers describe alternative edits or one bulk update. [Montesi, Bertino & Martelli, *Transactions and Updates in Deductive Databases*, §4](https://www.doc.ic.ac.uk/research/technicalreports/1995/DTR95-2.pdf) |
| **3. Linear facts or multiset rewriting** | A reservation step consumes the old stock row and produces its replacement together with the cart reservation. The product lookup is reusable. | A dedicated transition clause can distinguish rows to consume, rows to produce, and ordinary premises. This fits transfers of scarce goods. The semantics must identify a consumable occurrence: two proofs of `available` may witness the very same stock row. The existing `:-` can keep its deductive reading throughout. [Four approaches to choice and backtracking](#overview-of-choice-and-backtracking) |
| **4. Transaction Logic** | First restore the cart's reservations, then perform checkout in the resulting shop. Ask whether there is a successful execution of that composite action. | A formula can hold over a path of database states. Serial conjunction composes paths and gives the second step access to the result of the first. This earns its place when intermediate observations, hypothetical execution, or search over alternative action sequences are domain requirements. Wrapping two inserts in an atomic commit alone supplies no reason to adopt the path logic. [Bonner & Kifer, *A Logic for Programming Database Transactions*](https://www.cs.toronto.edu/pub/bonner/papers/transaction.logic/chapter98.pdf) |
| **5. Effectful operations with assert, update and retract** | The body of `registerCustomer` inserts both rows inside a transaction. Existing rules and contracts query the resulting facts. | This is a direct executable implementation. It needs a transaction boundary, a specified view for reads and a policy for concurrent writes. SWI-Prolog's logical update view stabilizes an individual predicate call. Its separate transaction facility makes a group of edits atomically visible, and its manual gives an example requiring an additional commit constraint. [SWI-Prolog transactions](https://www.swi-prolog.org/pldoc/man?section=transactions) |
| **6. Events and time-indexed facts** | Record when a reservation was granted or released. Derive whether it held when a payment arrived. Ordinary queries can use an implicit observation time. | Events and persistence rules earn their cost when the domain asks historical questions. The shop's `now` for checking expiry already has a business meaning. Two registrations can share that timestamp and still be distinct transitions. Choosing which competing reservation to accept remains a separate decision. [Kowalski & Sergot, *A Logic-based Calculus of Events*](https://www.cs.brandeis.edu/~cs112/cs112-2004/newReadings/Kowalski-Sergot.pdf) |
