/-!
# Namespace Mapping

How anthill namespace, visibility, and import declarations map to Lean 4.

| Anthill                    | Lean 4                              |
|----------------------------|-------------------------------------|
| `namespace N { ... }`     | `namespace N ... end N`             |
| `internal`                | `private`                           |
| `export`                  | (default visibility)                |
| `public`                  | (public — no modifier)              |
| `import N.*`              | `open N`                            |
| `import N.{A, B}`         | `open N (A B)` or selective import  |
| `requires Eq{T}`          | `variable [Eq T]`                   |
-/

namespace Anthill.Mapping.Namespaces

-- Example: namespace with visibility
-- anthill:
-- ```
-- namespace Geometry {
--   export entity Point(x: Int, y: Int)
--   internal operation helper() -> Int
-- }
-- ```
namespace Geometry
  structure Point where
    x : Int
    y : Int
    deriving Repr

  private def helper : Int := 42
end Geometry

-- Example: import mapping
-- anthill: `import Geometry.*`
-- Lean:
open Geometry in
#check Point

-- Example: requires as type class constraint
-- anthill: `sort Container { sort T = ?; requires Eq{T} }`
class Container (T : Type) [BEq T] where
  empty : List T
  insert : T → List T → List T

end Anthill.Mapping.Namespaces
