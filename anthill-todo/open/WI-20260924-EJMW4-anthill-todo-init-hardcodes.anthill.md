## Attributes

- id: WI-20260924-EJMW4-anthill-todo-init-hardcodes
- created: 2026-09-24T09:04:37Z

- status: Open
- status_agent: user
- status_at: 2026-09-24T09:04:37Z

- acceptance: cargo-test, scaland-sbt-test

## Description

anthill-todo: `init` HARDCODES `language: "rust"`, `build: "cargo"`, `tools: ["cargo-test"]` into project.anthill, with NO WAY TO SET THEM -- every non-Rust project starts misdescribed.

MEASURED 2026-09-24 on dotty-cps-async (a Scala/sbt project): `anthill-todo -d <dir> init` wrote the Rust triple; `init --help` offers only `<name>` / `--name`. Repaired by hand-editing project.anthill to `language: "scala", build: "sbt", tools: ["sbt-test"]` -- `status` and `fsck` accept it, but nothing says which `tools` names are meaningful, so `sbt-test` was a guess by analogy with `cargo-test`.

Source: the `format!` literal in `rustland/anthill-todo/src/main.rs` (~line 4422, the `-- Project configuration` scaffold).

Directions, not decided:
  (a) `init --language L --build B --tools T,...` flags;
  (b) detect from marker files in the project root (Cargo.toml -> rust/cargo, build.sbt -> scala/sbt, package.json, pyproject.toml, ...), flags overriding;
  (c) document the `tools` vocabulary -- where a name like `cargo-test` is resolved (ToolPasses acceptance) and what an unknown name does.

