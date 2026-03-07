/-!
# Anthill → Lean 4 Mapping: Overview

This module describes the strategy for compiling/realizing anthill kernel
constructs as Lean 4 code.

## Strategy

The anthill kernel has four core constructs (`namespace`, `sort`, `rule`,
`operation`).  Each maps to a natural Lean 4 counterpart:

- **Namespaces** → Lean `namespace`
- **Sorts** → `inductive`, `structure`, `abbrev`, or `variable` depending on form
- **Rules** → `theorem`, `@[simp] theorem`, or `instance`
- **Operations** → `def` or `class` method

## Key Principles

1. **Specs become types**: pre/post-conditions become proof arguments and
   subtype returns.
2. **Effects become monads**: effect declarations map to monad transformer stacks.
3. **Visibility maps naturally**: `internal` → `private`, `export` → default,
   `public` → public.
4. **Type parameters become `variable`s**: abstract sorts become type variables,
   often with class constraints from `requires` clauses.
-/

-- This file is documentation only; no definitions.
