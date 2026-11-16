## Attributes

- id: WI-20261116-JWCNN-a-tuple-provides-partialeq-and
- created: 2026-11-16T17:19:45Z

- status: Open
- status_agent: claude
- status_at: 2026-11-16T17:19:45Z

- acceptance: cargo-test

- tags: proposal-073

## Description

A TUPLE PROVIDES PartialEq, AND Eq, THROUGH A GENERATED MEMBER THAT IS A DICTIONARY. Decided with the user 2026-11-16 (their proposal, reading confirmed; recorded on WI-20261105-CBRD2): a tuple whose component types each provide PartialEq provides it, through a generated eq that compares the components through their own members, and provides Eq when each component provides Eq; positional and named tuples alike, () always both. The instance is a dictionary like any other. PROGRAM: sort Pt { entity pt(x: Int64, y: Int64)  provides PartialEq[T = Pt]  provides Eq[T = Pt]  operation eq(a: Pt, b: Pt) -> Bool = match a case pt(ax, ay) -> match b case pt(bx, by) -> PartialEq.eq(ax, bx) } (Pt's eq compares x alone). (1) (pt(1, 2), 3) = (pt(1, 9), 3), in a rule body, an operation body and a query, is true through Pt's member, the call pinned to the tuple's member entered with its dictionary — today the typer returns early for = at a tuple (typing/apply.rs, equality_at_a_tuple, the call left unclassified) and the resolver and interpreter compare the components with no member (resolve.rs tuple_components_sem_eq, builtins.rs semantic_equal), each component through the equality index. (2) operation same[A](a: A, b: A) -> Bool requires PartialEq[T = A] = a = b called as same((pt(1, 2), 3), (pt(1, 9), 3)) is handed the tuple's dictionary and answers true. (3) List[T = (String, String)] and Map[K = (Int64, Bool)] get their equality through it (today a tuple as a type argument derives nothing, kernel-language §8.3; the Map key's Eq is a special case in typing/coherence.rs, unlawful_eq_part, which reads a tuple by its components). (4) (Int64, Float) provides PartialEq and not Eq; a tuple with a component providing no PartialEq has none, and = at it is refused at load as today (tuple_component_without_equality). WHERE: the typer builds a tuple's dictionary wherever a requirement at a tuple type is asked (dictionary_at_in_scope and its kin), from the components' dictionaries (a component at a type parameter forwards the caller's); a dictionary is Dictionary(sub0 … subn, impl: S) with S a provider sort (eval/dictionary.rs), so the tuple needs a provider of its own or a shape for it; the resolver's and the interpreter's equality enter the member through it; lawfulness (Eq's law at the tuple, dictionary_is_lawful, eq_call_law) reads it. kernel-language §8.3's 'A tuple has no eq member: its equality is its components'' and 'a tuple as a type argument derives nothing' replaced. WHY NOW: WI-20261105-CBRD2 makes an untyped equality at a carrier with its own eq a run-time error proposing === (decided 2026-11-16); a typed tuple equality carries no class today, so it cannot be told from an untyped one, and its components would start erroring. ACCEPTANCE: (1)–(4) driven to their answers; no component of a typed tuple equality read through the equality index (a trace or counter at its readers, resolve::eq_index_reads_by_this_thread); full workspace green via rustland/scripts/test.sh; families green on both carriers.

