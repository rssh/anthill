## Attributes

- id: WI-20261116-411A7-proposal-004-extension-stage-2
- created: 2026-11-16T20:30:12Z

- status: Open
- status_agent: claude
- status_at: 2026-11-16T20:30:12Z

- acceptance: cargo-test

- depends_on: WI-20261116-JWCNN-a-tuple-provides-partialeq-and

- tags: proposal-004

## Description

PROPOSAL 004 EXTENSION, STAGE 2: A TUPLE PROVIDES TypeValue. docs/proposals/004-tuple-sorts.md, 'Extension (2026-11-16): a tuple is a NamedTuple', rule 2: a tuple provides TypeValue when each component's type does, a derived provision as a sort's TypeValue is (proposal 065 §2; §7 step 2 deferred the formers: 'a named tuple or arrow has no sort to carry a provision'). Stage 1, WI-20261116-JWCNN, makes the tuple type the sort NamedTuple and gives it its derived PartialEq and Eq and the dictionary shape Dictionary(d1 … dn, impl: NamedTuple); this stage adds TypeValue on the same carrier. PROGRAMS (measured on 371a78ad): (T4) operation t4() -> Type = TypeValue.type_value[T = (a: Int64, b: String)]() is refused at load ('its carrier is (a: Int64, b: String), a tuple or an arrow, and no provision …'); under the rule it answers the type (a: Int64, b: String), and PartialEq.eq(type_value[T = (a: Int64, b: String)](), (a: Int64, b: String)) holds. A generic reader, operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = type_value[T = B](), called as tyOf((1, "s")), answers (Int64, String) (065 §'open question 3' measured it panicking before the refusal at the call). A component at a type parameter takes the caller's dictionary: operation pairOf[E](x: E) -> Type requires TypeValue[T = E] = type_value[T = (E, Int64)]() at E = Bool answers (Bool, Int64). A tuple with a component providing no TypeValue has none (refused at the call, as a requirement at a former is today). WHERE: the derived TypeValue provision (065 §2's derivation, HXGXF, sorts only today), the tuple's TypeValue dictionary built from its components', and type_value's answer read off it. kernel-language: §5.4's type_value sentence ('the derived instances are a sort's and a tuple or an arrow carries none') narrowed to arrows. ACCEPTANCE: the programs above driven to their answers; an arrow still refused (WI-20261021-VF8GT owns it); full workspace green via rustland/scripts/test.sh; families green on both carriers.

