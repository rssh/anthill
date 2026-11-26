## Attributes

- id: WI-20261126-VKDX4-a-dotted-sort-member-in-a
- created: 2026-11-26T06:16:19Z

- status: Open
- status_agent: user
- status_at: 2026-11-26T06:16:19Z

- acceptance: cargo-test, scaland-sbt-test

## Description

a dotted sort member in a reflect `Term` field of a `@[simp]` replacement is not the term it spells where the rule fires: `Q(pattern: K.seven)` (a const) is refused at load with the internal-defect message, and `Q(pattern: K.one)` (a nullary operation) loads and is fired as `Q(pattern: 1)`, missing the fact that holds it; the one-segment `seven` / `one` find it
WHO NEEDS IT. A program whose rewrite builds a value holding a quoted pattern, a field declared anthill.reflect.Term (§4.2), and names a sort member there by its path, as §5.3 says a qualified name is. WI-20261106-BYJ0X made a paren-less dotted name in a replacement run where the rule fires, and left a quoted field alone (`in_quoted_term`): there the name is the term its author wrote, and reading it as the operation-body walk does made the fired field miss its fact, with nothing refused (measured).
WHAT HAPPENS. MEASURED 2026-11-26 on d87be1ccc with the anthill CLI, over `sort K { const seven: Int64 = 7 }`, `entity Q(pattern: Term)`, `operation f(a: Int64) -> Q`, `rule r: f(?a) <=> Q(pattern: K.seven) @[simp]`, `fact held(q: Q(pattern: K.seven))` and `rule hit(1) :- ?q <=> f(1), held(q: ?q)`. (1) The load is refused at the replacement (9:32): "type mismatch in tkq.K.reference: expected a type value recorded where the sort is written (proposal 055 §1), got a plain reference to the sort — a defect in the walk that built this occurrence, not an error in the program". With `operation g() -> Q = f(1)` as the consumer instead, the same, plus "type mismatch in seven.name: expected resolved name, got unresolved". (2) Over `sort K { operation one() -> Int64 = 1 }` with `K.one` in the replacement and the fact, the load is clean, `rule what(?q) :- ?q <=> f(1)` binds `Q(pattern: 1)` (the call run inside the quoted field), and hit has NO answer: a silent miss. The same on the binary before BYJ0X (pre-existing). The twins: with the imported one-segment `seven`, and with `one`, in the replacement and the fact, the load is clean and hit answers 1; written directly in the rule, `?q <=> Q(pattern: K.seven), held(q: ?q)` answers 1; spliced into g, `seven` gives `Q(pattern: 7)`, as an operation body's own `Q(pattern: K.seven)` does.
WHY IT MATTERS. The const's message blames the loader, not the program; the operation's is a wrong answer with no diagnostic, against §8.3's "an operation's name in a field of type Term, written alone or dotted, [is] not a computation and stays the term it spells". The only way round either is the one-segment spelling, an import per member.
WHAT IS ASKED. A dotted name in a Term field of a replacement read as the same text is where the rule fires. Fired by the resolver in a rule body, it is the term a fact holding the same text holds, so hit answers 1 for K.seven, K.one and a nested sort's K.In.eight. Spliced into an operation body, it is what that body's own construction of the same text gives (`Q(pattern: 7)` for K.seven today); if anthill decides instead that a replacement's quoted field is the written chain wherever it lands, it says so with the reason.
DONE WHEN. Rows driving it: hit answers 1 for K.seven, K.one and K.In.eight in the replacement and the fact, read against the one-segment twins; g() spliced is what the body's own construction gives; a name with no reading in such a field keeps the treatment it has today (measured first); each row's back-out measured at its site.

