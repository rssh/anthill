# Webots → anthill binding conversion checklist

How to add a new webots device sort to this project, given the C++ header at `$WEBOTS_HOME/include/controller/cpp/webots/<Device>.hpp`.

## Per-device recipe

1. **Create one file per device**: `<device_name>.anthill` (lowercase, snake_case).
2. **Top-of-file comment**: paste the relevant subset of the C++ class's public surface so the reader sees the source-of-truth alongside the anthill model.
3. **Sort declaration**: `sort anthill.examples.lf1.webots.<DeviceName> ... end`.
4. **Imports**: `Int`, `Float`, `Unit`, `Bool`, `String` from `anthill.prelude` as needed; `Vec3` from `anthill.examples.lf1.webots.types` for fixed-size double-array returns.
5. **Exports**: list the sort name and every operation, one or more `export` clauses.
6. **Operations**:
   - **Public C++ method → `operation`** with `self: <DeviceName>` as the first argument.
   - **`const` method** → no `effects` clause.
   - **Non-`const` method** → `effects Modify[self]`. Multiple effects: `effects {Modify[self], Error}`. Bracket form for the target binding is required; `Modify(self)` (paren) is the term-level form, `Modify[self]` is the type-level form, effects are types.
   - **Return types**:
     - `void` → `Unit`
     - `int` returning -1/0/1 codes → `Bool` if it fits, otherwise `Int`
     - `double` → `Float`
     - `const double *` returning a fixed 3-vector → `Vec3`
     - `std::string` → `String`
     - Pointer-to-class (e.g. `webots::GPS*`) → the sort name; carrier-bound to the pointer in `realization.anthill`
   - **`enum` nested in the class** (e.g. `GPS::CoordinateSystem`) → its own sort with one `entity` per enum constant, at namespace level (i.e. as a sibling sort, not nested).
7. **Add a fact in `realization.anthill`**:
   ```anthill
   fact Implementation(
     target:      "anthill.examples.lf1.webots.<DeviceName>",
     artifact:    "webots/<DeviceName>.hpp",
     language:    "cpp",
     profile:     some("cpp20-stl"),
     description: some("webots::<DeviceName> — <one-liner>"),
     carrier:     [CarrierBinding(sort_name: "<DeviceName>",
                                  host_type: "webots::<DeviceName> *")],
     namespace_map: []
   )
   ```

## Patterns

| C++ shape | anthill encoding |
|---|---|
| `void enable(int)` / `void disable()` | `operation enable(self, p: Int) -> Unit \n  effects (Modify self)` |
| `int getSamplingPeriod() const` | `operation get_sampling_period(self) -> Int` |
| `const double *getValues() const` (3-vec) | `operation get_values(self) -> Vec3` |
| `const double *getValues() const` (n-vec) | hand-define a fixed-size value type (`Vec4`, etc.) — anthill `List[T = Float]` is variable-size |
| nested `enum X { A, B }` in class | `sort X { entity A; entity B; }` at the same namespace |
| static method `static T foo(...)` | namespace-level operation in a sort with no `self`, e.g. `operation foo(args) -> T` (same sort declaration, no `self`) |
| reference param `Foo &out` (output) | return type, not a parameter — anthill operations have one return value |
| pointer param `Foo *opt` (optional) | `Option[T = Foo]` |

## Conventions specific to lf1

- **Vec3** lives in `anthill.examples.lf1.webots.types`. When WI-081 (math library) lands, lift to a shared location.
- **Profile** is `cpp20-stl` for every binding; the project uses `-std=c++20`.
- **Channel sentinel** (`CHANNEL_BROADCAST = -1`): for now, callers pass `-1` directly. A term-level constant once anthill grows that.
- **Payload bytes**: `send`/`get_data` model the payload as `String`. Replace with a proper byte-array sort once anthill has one.

## What lives in lf1 vs. what to lift later

- These bindings are **project-local**. If a second consumer of webots appears, lift `examples/webots-modelling/lf1/webots/` into a shared location (sibling crate or `bindings/webots/`). Do not lift preemptively.
- The same applies to abstract sensor/channel interfaces: if blefusku lands as a second messaging consumer, introduce abstract `Channel[T]` etc. and have both webots's `Emitter` and blefusku's analog `provides` it.
