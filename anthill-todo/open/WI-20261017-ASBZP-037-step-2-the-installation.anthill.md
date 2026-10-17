## Attributes

- id: WI-20261017-ASBZP-037-step-2-the-installation
- created: 2026-10-17T12:35:47Z

- status: Open
- status_agent: claude
- status_at: 2026-10-17T12:35:47Z

- acceptance: cargo-test

- tags: proposal-037

## Description

037 STEP 2: THE INSTALLATION MAP, AND Cell BOUND THROUGH IT. Plan: docs/design/037-implementation.md §2.2 and §2.3; acceptance §4, step 2. Proposal 037 §5: each resource is bound to one implementation of its sort, and every call on it goes there. The implementations in force are a persistent map from a base sort to an implementation, read only when a resource is made or mounted. WHAT IS MISSING: a cell already reaches one store, since its handle carries the arena that minted it, but nothing chooses that store at Cell.new, and the arena is a concrete type, so no second implementation can exist. THE CHANGE: (1) a module eval/installation.rs with Installations, a persistent map from a base sort's canonical symbol to an Implementation (one variant per family of base sorts; Cell is the only one now), held in one field on Interpreter. (2) A trait CellImplementation (alloc, read, write, retain, release), which the arena implements as the default. (3) CellHandle { raw, implementation: Rc<dyn CellImplementation> }; its identity is the implementation's allocation and the slot. (4) alloc_cell takes the installed entry, else the interpreter's arena. Cell.get and Cell.set go through the handle as they do today. The bridge's scratch interpreter starts with no installation, which means the defaults, so 037 §5.4's pure-call rule holds unchanged. NOT IN THIS STEP: installing for a scope, and wrapping (WI-078 (h), which comes after this); undo (WI-070).

