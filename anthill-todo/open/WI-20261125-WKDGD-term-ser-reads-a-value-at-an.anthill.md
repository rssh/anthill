## Attributes

- id: WI-20261125-WKDGD-term-ser-reads-a-value-at-an
- created: 2026-11-25T23:53:57Z

- status: Open
- status_agent: user
- status_at: 2026-11-25T23:53:57Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261125-SCPW9-term-ser-has-no-spelling-for-a

## Description

term_ser reads a value at an abstract library sort (Stream, FiniteStream) with its providers' parameters unbound, so a list at Stream[T = Int64] is refused at its first element, naming a binding the type writes
WHO NEEDS IT. A caller of decode_value / encode_value (anthill-traces) whose spec's state, parameters or results are typed at an abstract sort a GENERIC provider provides: Stream[T = Int64, E = {}] and FiniteStream[...], which List provides (`provides Stream[T, {}]`, list.anthill:154). WI-20261125-SCPW9 gave a value at a sort with abstract values a spelling (the provider's value, tagged among the providers' constructors, read as the Instance pair), and stopped at providers with parameters (proposal 021, "Not in this proposal").
WHAT HAPPENS. MEASURED 2026-11-25 on the SCPW9 working tree (atop 2eed52a9e) with a scratch binary: at Stream[T = Int64, E = {}] DeclaredType::shape's constructors are MappedStream.mapped, FilteredStream.filtered, List.nil, List.cons; `[1, 2]` is refused "found an array of 2 elements"; `{"cons": {"head": 1, "tail": [2]}}` is refused "$.cons.head: expected T, type parameter `T` is bound neither by the type nor by a default"; encoding the fact's list [1, 2], and the value `operation st() -> Stream[T = Int64, E = {}] = [1, 2]` returns (Instance(Dictionary(impl: List), cons(1, cons(2, nil)))), is refused the same way. FiniteStream[T = Int64, E = {}] likewise (constructors List.nil, List.cons). Read: shape types each provider's constructors in the provider's own parameters at their defaults (term_ser.rs, sort_env(kb, provider, &ty, &[])); the abstract sort's bindings never reach them, though the provision says how (List.T is Stream.T).
WHY IT MATTERS. Stream and FiniteStream are the standard library's sequence interfaces, so a spec typed through them can be neither checked nor generated; and the refusal misdirects, saying T is unbound where T = Int64 is written.
WHAT IS ASKED. (1) A provider's parameters bound from the abstract sort's application through the provider's provision: where it binds a spec parameter to one of the provider's (List provides Stream[T = T]), that parameter is the declared binding; one the provision does not reach takes its default, and one with neither is refused naming the provision and the parameter, not as unbound in the declared type. A provision binding through a composite (provides Sp[T = List[T = A]]) is bound by matching or refused by name, which is for anthill to say. (2) The spelling of a List provider's value at Stream: tagged as now ({"cons": ...}, its tail an array), or the list's own array; anthill to decide, with the reason. (3) The lazy providers (MappedStream, FilteredStream, whose fields hold functions) refused by name at their tag, rather than listed as tags no value reads.
DONE WHEN. Rows driving decode_value / encode_value: a list at Stream[T = Int64, E = {}] and at FiniteStream[T = Int64, E = {}] round-trips, read as the pair an operation body builds (st()'s value, by hash-consed identity) and run (a Stream operation on it answers); a provider binding through a composite, bound or refused by name; a lazy provider's tag refused by name; each with its back-out measured at its site.

