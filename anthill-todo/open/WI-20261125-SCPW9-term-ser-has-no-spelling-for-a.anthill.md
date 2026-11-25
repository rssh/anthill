## Attributes

- id: WI-20261125-SCPW9-term-ser-has-no-spelling-for-a
- created: 2026-11-25T09:08:47Z

- status: Open
- status_agent: user
- status_at: 2026-11-25T09:08:47Z

- acceptance: cargo-test

## Description

term_ser has no spelling for a Set, a Map, or a value at a spec type that its providers' constructors make
WHO NEEDS IT. A caller that reads and writes values at declared types through decode_value / encode_value. anthill-traces (private) checks recorded traces of a spec's operations, and generates them, through that pair. Today a spec whose state or parameters hold a Set, a Map, or a value at a spec type can be neither checked nor generated, because every such value is refused. An example of the last is a field xs: List[T = Sp] whose elements are values of Sp's providers, the case kernel-language.md:6142 writes as total([car(n: 1), van(n: 2)]).
WHAT HAPPENS. MEASURED 2026-11-25 on 8ed4765f3 through anthill-traces' test binary (decode_value with its options): Set[T = Int64] from [1, 2], Map[K = Int64, V = Int64] from [[1, 2]], and a spec sort with no constructors from {} are each refused "the type has no data spelling" (ValueProblem::NoDataSpelling, persistence/term_ser.rs:711, :250). Read: proposal 021 refuses them by design. A sort with no constructors (Set, Map, Stream) is refused at both ends (021, the paragraph at line 219), and encoding Set, Map and other host-carried values, "Set as an array, Map as an array of pairs", is left to a later proposal (line 472). A Set's values are its insert / empty chains (set.anthill); a Map's is a host handle that TermView shows as opaque (021).
WHY IT MATTERS. Sets and maps are the natural spelling of a state's collections, and a spec typed through a spec is how providers are meant to be used. Neither can cross the codec, so any tool built on it stops at them.
WHAT IS ASKED. Spellings, with their decode and encode, for: (1) a Set, as an array of its elements, decoded to the Set value the language builds, and encoded the same way every time for the same value; (2) a Map, as an array of [key, value] pairs, likewise; (3) a value at a spec type, tagged by its constructor as a value of a sort of several constructors is, the tag read among the constructors of the spec's data-sort providers, and an ambiguous or unknown tag refused by name. The choices left to anthill: an element written twice in a Set's array, a key twice in a Map's, the order encode writes, the Map spelling when its keys are strings, and whether a host-handle Map needs the interpreter to encode (021 line 472 says so).
DONE WHEN. Rows that drive each through decode_value and encode_value: Set[T = Int64] from [2, 1] is a set equal by = to the one insert(insert(empty(), 2), 1) builds, and writes the same text each time; a Set of entities likewise; a Map[K = String, V = Int64] round trip; a value at a spec Sp with providers car and van read from {"car": {"n": 1}} and written back; and each refusal, named: an unknown tag, a tag two providers share, and whatever the choices above refuse.

