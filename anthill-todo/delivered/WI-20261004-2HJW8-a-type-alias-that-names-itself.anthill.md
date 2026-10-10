## Attributes

- id: WI-20261004-2HJW8-a-type-alias-that-names-itself
- created: 2026-10-04T21:51:50Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-09T14:49:25Z

- acceptance: cargo-test, scaland-sbt-test

- tags: declarations, loader

## Description

A TYPE ALIAS THAT NAMES ITSELF IS REFUSED AT ITS DECLARATION — today a cyclic alias (`sort A = B`, `sort B = A`) and a self-naming one (`sort Loop = List[T = Loop]`) load with no diagnostic and are then an opaque type nothing inhabits. Filed on the user's word (2026-10-04), found while probing WI-20261001-80ZV8's stage (e).

THE PROGRAMS.

  sort A1 = B1                          -- a bare cycle: stands for no type at all
  sort B1 = A1
  operation f(x: A1) -> Int64 = 1

  sort Loop = List[T = Loop]            -- names itself inside its own definition
  operation g(x: Loop) -> Int64 = 1
  operation h(x: List[T = Loop]) -> Int64 = g(x)

TODAY (measured 2026-10-04, on `1612b482` and on the stage (e) tree alike). Every declaration above LOADS. Used as a type, each alias is a name of its own that nothing conforms to: `f(5)` is refused `expected A1, got Int64`; `g(nil)` is refused `expected Loop, got List`; and `h` is refused at `g(x)`, `expected Loop, got List[T = Loop]` — the alias is not even read as the type its own declaration says it is. Nothing hangs or overflows. ONE reader already says it out loud: a spec clause naming a bare cycle (`provides A1`) is refused, "its chain comes back to itself (A1 = B1 = A1), so it stands for no type" (WI-20260924-F8PYZ; kernel-language.md §5.1, "a chain that comes back to itself"). Every other alias reader stops at the cycle in its own way and says nothing: `alias_expansion` answers `Cycle`, `resolve_alias_shape` / `dealias_type` leave the name as written ("a cyclic or non-well-founded alias, which has no finite expansion"), and the carrier rule's alias walk (stage (e)) reads a self-naming alias once. So a typo in an alias is a silent uninhabited type, found only at the first value that fails to conform — the silent skip the project rules ask to make loud.

WHAT IT IS, AND IS NOT (the user asked, 2026-10-04: "is it F-bounded polymorphism? If yes — do we want to support it?"). It is NOT F-bounded polymorphism. F-bounded polymorphism is a type whose BOUND mentions it — `T <: Ord[T]` — and in anthill that is a DECLARATION providing or requiring a spec at itself: `sort Car … provides Ord[T = Self]`, `operation max[T](a: T, b: T) -> T requires Ord[T = T]`. No alias is involved, it loads and runs today, and this ticket does not touch it. A self-naming ALIAS is an EQUI-RECURSIVE TYPE: an alias is transparent, so `Loop` would be the infinite type `List[T = List[T = List[…]]]`; the bare cycle is its degenerate case, a name for nothing.

THE CHOICE, with a recommendation. (a) REFUSE at the alias declaration — recommended. Types here are finite terms: unification has an occurs check, and a recursive type is written NOMINALLY, through a sort with a constructor (`sort Loop  entity loop(items: List[T = Self])  end`), which is what gives the recursion a value to stand on. Scala and Rust both refuse a cyclic type alias for the same reason. (b) SUPPORT equi-recursive aliases — regular infinite types in the unifier (cyclic terms or a μ binder, equality by bisimulation), touching the hash-consed store, the occurs check, every alias reader and the printer. No program in the stdlib, the examples or anthill-todo asks for it. Not recommended; it would be a proposal of its own.

ACCEPTANCE (for (a)). Each of these is a load error AT THE DECLARATION, naming the chain, on rustland and on scaland: `sort S = S`; `sort A = B` with `sort B = A`; `sort Loop = List[T = Loop]`; and a cycle through two applied links (`sort A = List[T = B]`, `sort B = Option[T = A]`). CONTROLS, which load and are driven: a chain that ends (`sort Top = Mid`, `sort Mid = List[T = Int64]` — a value of `List[T = Int64]` is a `Top`); recursion through a constructor, which is nominal and finite (`sort Tree  entity node(kids: Kids)  end` with `sort Kids = List[T = Tree]` — a `node` holding a list of nodes runs); and F-bounded use (`Car provides Ord[T = Self]`) unchanged. The spec clause's own refusal of a cycle keeps its message or defers to the declaration's. kernel-language.md's alias section says the rule in one sentence. Each row says which rows fail when the check is backed out.

## Changes

### 2026-10-04T22:08:36Z — feedback — claude

DECIDED by the user, 2026-10-04: option (a) — REJECT. In their words: "difference that in F-bound polymorphism we have <:, while in self-naming: = . Agree, should be rejected." That is the whole distinction: an F-bound is a SUBTYPE constraint on a type (`T <: Ord[T]` — in anthill a carrier providing, or a parameter requiring, a spec at itself), which has many solutions and is supported; a self-naming alias is an EQUATION (`Loop = List[T = Loop]`), whose only solution is an infinite type. So: a type alias whose definition reaches its own name — directly, through a chain of aliases, or inside an applied link — is a load error at the declaration, naming the chain. Option (b) (equi-recursive aliases) is not pursued.

### 2026-10-09T14:49:23Z — feedback — user

DELIVERED 2026-10-09, on rustland and scaland. A type alias whose definition reaches its own name is a load error where it is declared, naming the chain: `sort S = S` (S -> S); `sort A = B` with `sort B = A` (A -> B -> A at A, B -> A -> B at B); `sort Loop = List[T = Loop]` (Loop -> Loop); and a cycle through two applied links (`sort A = List[T = B]`, `sort B = Option[T = A]`). An alias that only names one on a chain (`sort D = List[T = A]`) is not refused itself. Rustland: `declare_type_aliases` gains a round that notes which pending aliases each pending alias names, and the last round refuses each alias on a chain (`AliasDeclarePass::refuse_alias_reaching_itself`, `chain_back_to`); an alias that names itself is now never ready, where before it was recorded in the first round. Scaland: `reportRecursiveAliases` after pass 2 of `scanDefinitions`. CONTROLS that load and run: a chain that ends, an alias naming one declared below it, recursion through a constructor (`Tree` / `Kids`), `Car provides Ord2[T = Self]`, an alias sharing its short name with the sort it stands for. The spec clause's own refusal of a cycle KEEPS its message beside the declarations': `provides CA` over `sort CA = CB`, `sort CB = CA` reports three refusals (wi_f8pyz's reports-once rows count them). kernel-language.md §5.2 states the rule. Back-outs are at the head of wi_2hjw8_recursive_alias_test.rs; scaland rows in RecursiveAliasTest.scala.

