## Attributes

- id: WI-20261122-EFRBA-anthill-core-does-not-build-as
- created: 2026-11-22T13:05:17Z

- status: Open
- status_agent: claude
- status_at: 2026-11-22T13:05:17Z

- acceptance: cargo-test, scaland-sbt-test

## Description

anthill-core does not build as a cargo git dependency: the generated tree-sitter parser is not in the repository

WHO NEEDS IT. anthill-traces (a tool outside this repository, not yet published) depends on anthill-core and anthill-stl as cargo git dependencies, `{ git = "https://github.com/rssh/anthill.git", rev = ... }`. Any crate outside this repository that uses anthill as a library has to do the same, since nothing is on crates.io.

WHAT HAPPENS TODAY (measured 2026-11-22 at rev 60ff38d3; .gitignore and tree-sitter-anthill/build.rs are unchanged at d1b3d716b). `cargo build` of such a crate fails in the build script of tree-sitter-anthill (anthill-core's path dependency):
- .gitignore ignores `tree-sitter-anthill/src/` (parser.c and the headers `tree-sitter generate` writes) and `tree-sitter-anthill/bindings/`, so cargo's checkout of the repository has neither.
- build.rs therefore runs `npx tree-sitter generate` in that checkout, and fails: `npm error could not determine executable to run`, then `tree-sitter generate failed`. It fails the same way with tree-sitter-cli on PATH: npx resolves against the checkout's own package.json (tree-sitter-cli is a devDependency there) and the checkout has no node_modules. The only way through is to run `npm install` inside cargo's checkout under ~/.cargo/git, which a dependent crate cannot do.
- Building inside this repository works only because a developer's tree has a generated parser.c and an npm-installed tree-sitter-cli. So the repository's own build also depends on files that are not in it.
- The `bindings/rust/lib.rs` that build.rs creates with `npx tree-sitter init` is missing for the same reason.
anthill-traces builds today only against a local checkout, by a `[patch."https://github.com/rssh/anthill.git"]` in an untracked .cargo/config.toml.

WHAT IS ASKED. A clean checkout of the repository at any commit builds with cargo alone: no node, npm or tree-sitter-cli. The usual way for a tree-sitter grammar is to commit the generated `src/` (parser.c, tree_sitter/*.h, grammar.json, node-types.json) and `bindings/rust/`, and to regenerate only when grammar.js changes. One trap: build.rs decides staleness by comparing the mtimes of grammar.js and parser.c, and a fresh git checkout sets every mtime to the checkout time, so it can still decide to regenerate (and fail) on a clean clone. Staleness should not depend on mtimes (e.g. compare a hash of grammar.js recorded beside the generated files), or build.rs should never regenerate on its own and leave that to an explicit step (`npm run generate`). Then a committed parser that does not match grammar.js has to be caught: a check in scripts/test.sh (or a test) that regenerates and compares, so the two cannot drift.

WHAT IS NOT ASKED: publishing the crates to crates.io.

DONE WHEN: a crate outside this repository that names anthill-core and anthill-stl as git dependencies at the item's commit builds with `cargo build` on a machine where `npx tree-sitter` is not available (measured: e.g. with PATH stripped of node, or in a container without it). Editing grammar.js in this repository and not regenerating makes the gate fail, naming the stale parser.

