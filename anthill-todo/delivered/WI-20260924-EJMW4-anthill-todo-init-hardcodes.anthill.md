## Attributes

- id: WI-20260924-EJMW4-anthill-todo-init-hardcodes
- created: 2026-09-24T09:04:37Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-24T14:48:38Z

- acceptance: cargo-test, scaland-sbt-test

## Description

anthill-todo: `init` HARDCODES `language: "rust"`, `build: "cargo"`, `tools: ["cargo-test"]` into project.anthill, with NO WAY TO SET THEM -- every non-Rust project starts misdescribed.

MEASURED 2026-09-24 on dotty-cps-async (a Scala/sbt project): `anthill-todo -d <dir> init` wrote the Rust triple; `init --help` offers only `<name>` / `--name`. Repaired by hand-editing project.anthill to `language: "scala", build: "sbt", tools: ["sbt-test"]` -- `status` and `fsck` accept it, but nothing says which `tools` names are meaningful, so `sbt-test` was a guess by analogy with `cargo-test`.

Source: the `format!` literal in `rustland/anthill-todo/src/main.rs` (~line 4422, the `-- Project configuration` scaffold).

Directions, not decided:
  (a) `init --language L --build B --tools T,...` flags;
  (b) detect from marker files in the project root (Cargo.toml -> rust/cargo, build.sbt -> scala/sbt, package.json, pyproject.toml, ...), flags overriding;
  (c) document the `tools` vocabulary -- where a name like `cargo-test` is resolved (ToolPasses acceptance) and what an unknown name does.

## Changes

### 2026-09-24T14:48:21Z — feedback — user

Delivered (2026-09-24, efcd5a3b). All three directions, composed: (b) init reads language/build/tool off the ONE build file in the project dir -- Cargo.toml rust/cargo/cargo-test, build.sbt scala/sbt/sbt-test, go.mod go/go/go-test; only files that PIN the triple are listed (package.json, pyproject.toml say it with flags). (a) --language / --build / --tool (repeatable; '--x v' and '--x=v') override field by field; a build file is read only while it is the build in effect (--build sbt beside Cargo.toml does NOT default to cargo-test -- found by the 2nd review). No default anywhere: no build file and no --tool, or two build files with a field left open, is refused (exit 1) naming the flags; with nothing to read, language/build are OMITTED from the fact (status loads clean, measured). (c) help text, the scaffolded project.anthill comment and the skill say a tool name is a free-form LABEL anthill-todo neither resolves nor runs (verified: ToolPasses is only constructed; ToolDef has no consumer in anthill-todo); add without --acceptance embeds each as ToolPasses(<tool>). Also: --name=--help no longer scaffolds a project called --help; duplicate/empty values and ',' in a tool refused; given values escaped via print::write_anthill_string. Tests: wiejmw4_init_project_config_test (9) drives each case through add and reads back the acceptance; all 9 fail against the old main.rs (measured). Bare-init tests plant a Cargo.toml (common::plant_cargo_toml). anthill-todo 300/300. scaland NOT run: no scaland file changed. NOT done, reported: init's host-side argv parser grew, against WI-1124 gap (2) (init runs before any KB, so the bundle's OperationSpec reporter can't serve it); embedded SKILL_MD and skills/anthill-todo/SKILL.md had already drifted (the embedded copy lacks 'What a project looks like on disk').

