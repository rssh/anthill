## Attributes

- id: WI-20260825-N2865-a-spec-s-cross-namespace
- created: 2026-08-25T19:18:29Z

- status: Open
- status_agent: claude
- status_at: 2026-08-25T19:18:29Z

- acceptance: cargo-test

## Description

a spec's cross-namespace `provides` leaks the provided sort's enclosing chain, so the providing spec's own NAME goes ambiguous at every consumer that `requires` it

## Changes

### 2026-08-25T19:18:58Z — feedback — claude

MEASURED AND MINIMIZED, on the tree that delivers WI-20260825-1WBZT. Two files, no stdlib edit:

  namespace probe.alg
    sort Base
      sort T = ?
      provides anthill.prelude.Additive[T = T]     -- the one line that decides it
      operation b(x: T) -> T
    end
    sort User
      sort V = ?
      requires Base[V]
      operation f(x: V) -> V
      rule f_def: f(?x) <=> Base.b(?x)
    end
  end
  -- second file
  sort Base
    sort T = ?
    operation g(a: T) -> T
  end

WITH the `provides` line: two load errors, `ambiguous symbol 'Base' in scope 'probe.alg.User': candidates ["probe.alg.Base", "Base"]` at the `requires` and at `Base.b`. WITHOUT it: loads clean, 2746 facts. Nothing else differs, so the `provides` clause IS the cause.

CROSS-NAMESPACE IS THE CONDITION, and this is the row that makes it a rule rather than one unlucky program. The same `Base`/`User` pair with `provides Cat[T = T]` where `Cat` is declared BESIDE `Base` in `probe.alg` loads clean. So does every same-namespace provision the stdlib already ships: a global `sort Eq` beside `Eq provides PartialEq` + `WeakOrd requires Eq` loads clean, and so do a global `sort Numeric` and a global `sort EuclideanDomain`. All three are `anthill.prelude` providing `anthill.prelude`.

THE MECHANISM, read off `intern.rs`. `load_requires_decl` and `link_provides_parent` both add `ScopeInclusion { is_enclosing: false }`, and `resolve_in_scope_recursive_with_mode`'s parent loop follows a reached scope's ENCLOSING parents afterwards — only an IMPORT edge stops that (`EnclosingLinks::StoppedByImport`, WI-1089: "below an import edge, the ENCLOSING chain is not re-entered — `import a.b.C` opens `C`, not the `a.b` around it"). So a `provides` across namespaces opens a path `User -> requires Base -> provides anthill.prelude.Additive -> anthill.prelude -> <global>`, and every global name is suddenly a rival at `User`. WI-1089's own sentence is the argument for the fix: a `requires A[T]` opens `A`, not the namespace around it.

WHAT IT COSTS TODAY, exactly one site. `anthill.prelude.algebra.Ring provides anthill.prelude.Additive` is the tree's only cross-namespace provision, and `VectorSpace requires Ring[F]` is its only consumer — so `anthill-testcases/ring-polynom/ring.anthill`'s top-level `sort Ring` turned SEVEN references in `algebra.anthill` into load errors (`ring_polynom_test` x4 and `algebra_spec_test::ring_spec_loads_and_resolves`). Unblocked in 1WBZT by ONE line — `import anthill.prelude.algebra.{Ring}` inside `VectorSpace`, importing its own SIBLING — which is why the comment at that import says what it is; when this lands, that import should go and the ring-polynom rows are the control.

NOT FIXED INLINE, and the reason is blast radius rather than difficulty. The candidate repair is one predicate — stop the enclosing chain below a `requires`/`provides` edge the way WI-1089 stops it below an import — and 64,445 `requires` links across the stdlib, `anthill-stl` and every fixture walk it (the count is `load.rs`'s own, measured under WI-993). Narrowing a shared resolver set serves one reader and breaks another (WI-1090, WI-1098, WI-1095), so this needs its own census per EDGE KIND before the predicate moves.

