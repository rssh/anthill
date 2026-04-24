# 028: `anthill run` CLI and the `Main` entry-point sort

## Status: Draft

## Depends on: 013 (effects as sorts + facts), 026 (expression evaluator), 026.1 (value-integrated KB queries), 027 (effect handlers)

## Relates to: WI-051 (M6 `anthill run`), WI-009 (port todo-app), WI-049 (Console stdlib), 025 (`requires` / `provides`)

## Motivation

The evaluator milestones (WI-042…WI-050) gave us an interpreter callable from Rust. To actually run anthill programs from the shell we need a CLI command that answers three questions:

1. **Which files make up the program?**
2. **Which operation is the entry point?**
3. **What effects are available at top level?**

Questions 1 and 3 are routine (positional paths + a fixed default handler set). Question 2 needs a design decision: anthill has no reserved name `main`, no `public static void main`, no manifest. We need a declarative way for a loaded KB to say "I am a program, start here." The answer here uses the same spec-satisfaction pattern the rest of the language already uses: a stdlib sort `anthill.cli.Main` whose satisfaction fact marks a program entry.

Non-goals for v1: package manager, dependency resolution, watch mode, REPL, incremental recompile, multi-target builds, `anthill.toml` / project manifest.

## The `Main` sort

```anthill
namespace anthill.cli
  import anthill.prelude.{Int, String, List}
  import anthill.prelude.Console.{ConsoleOutput, ConsoleInput}
  import anthill.prelude.{Error}
  export Main, main

  -- A program that can be invoked from the shell.
  -- Plain sort: no type parameter, no carrier. Hosts one abstract operation.
  sort Main
    operation main(args: List[T = String]) -> Int
      effects ConsoleOutput, ConsoleInput, Error
  end
end
```

`Main` is a plain sort, not a typeclass. It has no `sort T = ?`, no satisfaction fact, no carrier. Its only job is to host the signature contract for `main` — we need a sort because operations live in sorts. Nothing more.

A user program *refines* Main via the `requires` / `provides` relation from proposal 025:

```anthill
namespace my.app
  import anthill.cli.Main
  import anthill.prelude.Console.{console, println}
  export MyApp

  sort MyApp
    provides anthill.cli.Main

    operation main(args: List[T = String]) -> Int
      effects ConsoleOutput
    = let c = console in
      println(c, "hello, world");
      0
  end
end
```

The body is an expression (per proposal 018's operation-body form), not a rule: `main` is a functional operation with a single `Int` return, not a relational definition.

### Why `requires` / `provides`, not a typeclass

- We do need a *sort*, because every operation in anthill is declared inside a sort. `anthill.cli.Main` is that sort — a signature container.
- We do not need *parametric abstraction* (`sort T = ?` + satisfaction facts). `Main` has exactly one operation; there is no cluster to reason about generically; no value of type `Main` is ever passed around. The typeclass pattern earns its keep when multiple operations cluster under an abstraction and dispatch varies by carrier type (`Eq.eq` across Int/String/…); `Main` meets neither condition.
- `provides` is proposal 025's standard refinement-and-delivery mechanism: `MyApp provides Main` means `MyApp` is a subtype of `Main` and must supply Main's operations. This is the right modeling tool here. The CLI discovers entry points by querying the KB for this `provides` relation — the discovery story does not need a separate fact shape.
- User-side cost shrinks from three constructs (`entity` + `fact Main[…]` + `operation main(prog: T, …)`) to two (`sort MyApp` + `operation main(…)`), and `main` drops the ceremonial `prog: T` parameter.

### Signature contract

- **Return type `Int`**: process exit code. `0` = success, non-zero = failure.
- **`args: List[String]`**: CLI positional arguments passed after `--` (see below).
- **Effect row**: `ConsoleOutput, ConsoleInput, Error` by default. Additional effects (`Modify[store]`, `Branch`, …) are allowed but must have handlers registered — see §Handlers.

Operations that want a `Unit` return or a different signature are free to exist; they simply are not `Main` implementations and must be invoked by other means (library call from a Rust host, or a different entry sort introduced later).

## Entry-point discovery

After `parse + load_all` completes, the CLI queries the KB for all sorts that provide `anthill.cli.Main`. Concretely: the `requires` / `provides` relation is stored as a fact per proposal 025; the CLI reads those facts filtered by `Main`.

Let `N` be the number of refining sorts.

| N | Behavior |
|---|---|
| 0 | Error: `no program entry found (expected sort … provides anthill.cli.Main)`. Exit code 2. |
| 1 | Unique — invoke that sort's `main` operation. |
| ≥ 2 | Error listing all candidate entries (see below); require `--entry <qualified.Sort>` to pick one. |

When `N ≥ 2` and `--entry` is not given, the CLI prints the full list of providing sorts in qualified form, one per line, so the user can copy-paste:

```
error: ambiguous program entry — 3 sorts provide anthill.cli.Main
candidates:
  my.app.MyApp
  my.app.MyAppDebug
  my.tools.Scratch
pass --entry <sort> to select one
```

Exit code **2**. The list is sorted by qualified name so runs are deterministic.

### Disambiguation: `--entry`

```bash
anthill run --entry my.app.MyApp src/
```

The argument is the **qualified name of the sort that provides `Main`**. It must resolve to one of the sorts returned by the discovery query; otherwise it is an error.

If `--entry` is passed when only one program exists, it is accepted if it matches, rejected if it disagrees.

### Why sort-name not operation-name

- Every refining sort declares an operation *named* `main` (forced by the `Main` signature). The disambiguating information is *which sort's* `main` — so naming the sort is the direct way.
- Qualifying by operation (`my.app.main`) requires the user to know the operation lives under a sort and spell the compound path; naming the sort is what the `provides` relation already records in the KB.

## CLI surface

```
anthill run [--entry <Carrier>] [--] <path>... [-- <arg>...]
```

- `<path>...` — one or more `.anthill` files or directories. Directories are walked recursively for `*.anthill`.
- `--entry <Carrier>` — disambiguation (required when >1 program; optional/redundant otherwise).
- `--` — separates anthill-facing arguments (paths + flags) from arguments passed into the program. Everything after `--` becomes the `args: List[String]` given to `main`.

### Source loading

- Stdlib is always loaded first via `load_stdlib` (the existing pipeline used by tests and `anthill-todo`). No opt-out in v1.
- User paths are loaded after stdlib via the existing `load_incremental` path. No special "classpath" is introduced: the CLI is *not* responsible for finding files by namespace name. The user names the files they want loaded; namespace identity is orthogonal.
- No `ANTHILL_PATH` / no `anthill.toml` in v1. The explicit-paths model mirrors `go run` more than `mvn` — matches the current scale of programs.

This is a deliberate minimal choice. When `anthill run` graduates to multi-file / multi-project use, a package manifest can extend it backwards-compatibly: paths stay, manifest discovery of entry + deps layers on top.

## Default handlers

`anthill run` wires the following into the `Interpreter` before calling `main`:

| Effect | Handler |
|---|---|
| `ConsoleOutput` | Real stdio: `print` / `println` write to `stdout`; `stdout` flushed on `println`. |
| `ConsoleInput` | Real stdio: `read_line` reads from `stdin`, returns line without trailing `\n`. On EOF returns empty string (v1; revisit in 027 follow-up). |
| `Error` | Propagation: raised payload surfaces as a CLI-level error, printed in a fixed format on stderr, exit code 1. |
| `Modify[store]` | Default in-memory store handler from WI-050 (lives but empty per run — not persisted). |
| `Branch` | **Not enabled at the `main` boundary** in v1 — raising `branch` / `fail` inside `main` is a runtime error (`UnhandledEffect`). Programs that want non-determinism must install a local handler via `with_handler` (per proposal 027 phase B). |
| `Suspension` | Same as `Branch`: unhandled at top level in v1. |

Programs are free to register additional handlers via proposal-027 `with_handler`; the CLI does not filter what effects a program may declare, only what it provides defaults for.

## Exit code and output

- Process exit code = `main`'s return value. Values outside `0..=255` are clamped (shell convention).
- `main`'s return value is **not** printed. Programs that want to produce output do so via Console effects. This differs from the `[--arg '<term>']` sketch in proposal 026 §CLI, which targeted a library-style "invoke + print result" flow. `anthill run` serves programs; library-style invocation stays a Rust-host concern.
- On `EvalError`: format on stderr as `error: <msg>\n  at <span>`, exit code 1.
- On load error / typecheck error: format on stderr, exit code 2. (Distinct code so shells can tell "program failed" from "program didn't compile".)

## Promotion of the result

`main` returns `Int` — a `Value::Int(i64)`. No `Value → TermId` promotion is needed at the exit boundary; the i64 goes straight to `std::process::exit`. (The promotion path from proposal 026 §CLI was designed for arbitrary return types; it is retained as library API but not exercised by the CLI.)

## Error reporting

Three error classes, three exit codes, three stderr formats:

```
error: <parse/load/typecheck message>
  at <file>:<line>:<col>
```
Exit code **2** — compilation failed.

```
error: no program entry found (expected `fact anthill.cli.Main[T = …]`)
```
Exit code **2** — compilation succeeded but no `Main`.

```
error: <EvalError message>
  at <occurrence-span>
```
Exit code **1** — runtime error.

## Testing

Acceptance test is `anthill-cli/tests/run_cmd_test.rs`:

1. **hello.anthill** — single-file program with `sort Hello { provides Main; operation main(_) -> Int = println(console, "hello"); 0 }`. Assert `stdout == "hello\n"`, exit code 0.
2. **no-main.anthill** — well-typed program with no sort providing `Main`. Assert stderr matches the "no program entry" message, exit code 2.
3. **two-mains.anthill** — two sorts providing `Main`. Assert (a) without `--entry`: exit 2, stderr contains the "ambiguous entry" message *and* both qualified sort names in the candidate list; (b) with `--entry my.Two`: the right one runs.
4. **args.anthill** — program echoes `args` one per line. Invoke `anthill run … -- a b c`; assert stdout matches.
5. **exit-code.anthill** — `main` returns `7`. Assert process exit code 7.

## Open design decisions

1. **Should `Main` be in `anthill.prelude` or `anthill.cli`?** Draft puts it in `anthill.cli` — the sort is CLI-shaped (return is `Int`, effect row is Console + Error), so it does not belong in the pure prelude. Non-CLI embeddings (library, WASM, server) should define their own entry-point sort (e.g. `anthill.wasm.Wasm`, `anthill.embed.Op`).
2. **`println` flushing policy.** v1 flushes on every `println`. Revisit only if a benchmark motivates buffering.
3. **`read_line` on EOF.** v1 returns empty string. Cleaner would be an `Option[String]`, but the current Console op signature is `String`. Revisit alongside any future Console-signature change; do not special-case here.
4. **Should `--entry` accept the operation name as an alias?** Draft says no. One name, one convention.

## Migration plan

Land as WI-051 in one change:

1. Add `stdlib/anthill/cli/main.anthill` with the `Main` sort as shown.
2. Add `Command::Run(RunArgs { paths, entry, args })` to `anthill-cli/src/main.rs`.
3. Wire `load_stdlib` + `load_incremental(paths)` into the run path.
4. Query the KB for sorts providing `anthill.cli.Main`; resolve via `--entry` if >1.
5. Construct `Interpreter`, call `register_standard_builtins`, register the stdio `Console` handler.
6. Invoke `interp.call(<Sort>.main, &[Value::Term(args_list)])`, coerce return to exit code.
7. Acceptance tests as in §Testing.

Unblocks WI-009 (port todo-app to anthill).
