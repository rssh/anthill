## Attributes

- id: WI-20261116-411A7-proposal-004-extension-stage-2
- created: 2026-11-16T20:30:12Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-17T06:54:07Z

- acceptance: cargo-test

- depends_on: WI-20261116-JWCNN-a-tuple-provides-partialeq-and

- tags: proposal-004

## Description

PROPOSAL 004 EXTENSION, STAGE 2: A TUPLE PROVIDES TypeValue. docs/proposals/004-tuple-sorts.md, 'Extension (2026-11-16): a tuple is a NamedTuple', rule 2: a tuple provides TypeValue when each component's type does, a derived provision as a sort's TypeValue is (proposal 065 §2; §7 step 2 deferred the formers: 'a named tuple or arrow has no sort to carry a provision'). Stage 1, WI-20261116-JWCNN, makes the tuple type the sort NamedTuple and gives it its derived PartialEq and Eq and the dictionary shape Dictionary(d1 … dn, impl: NamedTuple); this stage adds TypeValue on the same carrier. PROGRAMS (measured on 371a78ad): (T4) operation t4() -> Type = TypeValue.type_value[T = (a: Int64, b: String)]() is refused at load ('its carrier is (a: Int64, b: String), a tuple or an arrow, and no provision …'); under the rule it answers the type (a: Int64, b: String), and PartialEq.eq(type_value[T = (a: Int64, b: String)](), (a: Int64, b: String)) holds. A generic reader, operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = type_value[T = B](), called as tyOf((1, "s")), answers (Int64, String) (065 §'open question 3' measured it panicking before the refusal at the call). A component at a type parameter takes the caller's dictionary: operation pairOf[E](x: E) -> Type requires TypeValue[T = E] = type_value[T = (E, Int64)]() at E = Bool answers (Bool, Int64). A tuple with a component providing no TypeValue has none (refused at the call, as a requirement at a former is today). WHERE: the derived TypeValue provision (065 §2's derivation, HXGXF, sorts only today), the tuple's TypeValue dictionary built from its components', and type_value's answer read off it. kernel-language: §5.4's type_value sentence ('the derived instances are a sort's and a tuple or an arrow carries none') narrowed to arrows. ACCEPTANCE: the programs above driven to their answers; an arrow still refused (WI-20261021-VF8GT owns it); full workspace green via rustland/scripts/test.sh; families green on both carriers.

## Changes

### 2026-11-17T06:54:05Z — feedback — claude

DELIVERED (2026-11-17, f73002f9 code, 28c2a6bc spec): a tuple provides TypeValue where each component does, through NamedTuple's instance Dictionary(d1 … dn, impl: NamedTuple, labels: (l1, …, ln)) — the labels a field of the dictionary, as decided with the user — on all three carriers; type_value reads it back as the tuple. Driven (wi_411a7_tuple_type_value_test, 7 rows): T4 answers (a: Int64, b: String); tyOf((1, "s")) is (Int64, String); pairOf(true) is (Bool, Int64); named order kept, nested, inside a sort, two generic levels, Cell[V = B]; a component with no TypeValue is refused naming the component; an arrow is still refused (VF8GT). Not driven as written: PartialEq.eq(type_value[T = (a: Int64, b: String)](), (a: Int64, b: String)) is refused at load, a tuple written as a value being a tuple of Type values (VF8GT's tuple type as a value); the equality is asked between two answers. Decided with the user 2026-11-17: TypePattern at a tuple stays refused until HWD8A (a pattern whose type is or holds a tuple is refused at load), so Error.raise((1, 2)) loads and a reify over a tuple payload is refused. Also fixed: tyOf((x, 1)) in g[E] with no requires loaded and panicked when run, now refused asking for requires TypeValue[T = E]. Found, not fixed (older than this stage): f != f and (1, f) != (1, f) with f an arrow load, where = is refused. kernel-language §4.5, §5.4 and the structural-former paragraph updated. Gate 12233 / 0 / 17; families green on both carriers; scaland testFull 804 / 0.

