# Building Anthill

## Prerequisites

- Rust toolchain with Cargo
- Node.js and npm (the tree-sitter CLI is a locked development dependency)
- A C/C++ build toolchain for the generated tree-sitter parser and Node binding
- Scala 3 / sbt only when building `scaland`

## First checkout

The Rust workspace builds `tree-sitter-anthill`. A fresh checkout has no
generated `tree-sitter-anthill/src/parser.c`, so install the locked JavaScript
dependencies without running the Node binding's install hook, generate the
parser, and then optionally build that binding:

```bash
cd tree-sitter-anthill
npm ci --ignore-scripts
npm run generate
npm rebuild                 # optional: required for the Node binding, not Rust
```

Running plain `npm ci` before `npm run generate` is not sufficient on a clean
checkout: the package install hook invokes `node-gyp`, which expects the
generated `src/parser.c` and fails when it is absent.

After `node_modules` and `src/parser.c` exist, the Rust build re-runs
`tree-sitter generate` automatically only when `grammar.js` is newer than the
generated parser.

## Rust

Run from the repository root:

```bash
cd rustland
cargo build
scripts/test.sh
```

Always use `rustland/scripts/test.sh` for tests. It provides live progress and
writes the complete output to `rustland/target/test-run-latest.log`. See
`rustland/CLAUDE.md` for filters, crate-specific commands, architecture, and
test-placement conventions.

## Tree-sitter grammar

After the first-checkout setup:

```bash
cd tree-sitter-anthill
npm run generate
npm test
```

Regenerate and commit the generated parser/bindings according to the grammar
package's tracked-file policy whenever `grammar.js` changes.

## Scala

```bash
cd scaland
sbt test
sbt compile
```
