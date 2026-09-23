## Attributes

- id: WI-20260922-BRT4Y-declare-host-backing-on-the
- created: 2026-09-22T14:52:44Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-23T11:16:44Z

- acceptance: cargo-test

- tags: typing

## Description

DECLARE HOST BACKING ON THE OPERATION, SO "IS THIS BODY-LESS BY DESIGN?" IS ANSWERABLE IN THE LANGUAGE. Proposed by the user during WI-20260921-EE0EP, after a review argument there rested on grepping `builtins.rs` — and got the answer wrong.

WHAT EXISTS. A binding block declares host backing PER CARRIER, PER LANGUAGE:

  rustland/anthill-stl/anthill/int64.anthill:  operation_map { compare: "ordered_compare", ... }   -- language rust
  rustland/anthill-cpp-gen/anthill/…:          the same for cpp

read by `is_host_mapped_op` (any language — the LOAD check's question) and `is_interpreter_mapped_op` (`lang == "rust"` — eval's). WI-886 split those two because a cpp-only mapping made a merged index promise eval an implementation it did not have. `stdlib/` itself holds ZERO `operation_map` blocks, which is right: the mapping names a host FUNCTION, so it belongs in the host's layer and the stdlib stays portable.

THE GAP. The ~33 `register_if_present` entries in `eval/builtins.rs` — `PartialEq.eq`/`neq`, `anthill.reflect.TypeValue.*`, `anthill.realization.runtime.OpRef.*`, `Console.*`, `Map.*` — are Rust host backings with NO `operation_map` anywhere. They are the one group that escaped the layering, and they are invisible to both predicates.

WHAT THE MARKER BUYS THAT `operation_map` CANNOT. The two say different things. `operation_map` answers "in rust, WHICH function", and only once a particular host's layer is loaded. `@[host_implemented]` would answer "is this operation body-less BY DESIGN" — a property of the DECLARATION, true whether or not any host is loaded:

  sort Int64
    @[host_implemented]
    operation compare(a: Int64, b: Int64) -> Int64
  end

Today a body-less operation is three things wearing one face: a spec member awaiting dispatch, a host-backed operation, and an unfinished mistake. The loader tells them apart by whether some binding block happened to map it — which is why `stdlib/` alone LOADS CLEAN and then dies `OperationBodyMissing` at eval, and why `collect_stdlib_and_rust_bindings`' own doc records three fixtures "loading half the library and measuring half the language".

NO NEW MACHINERY FOR THE MARKER ITSELF: operations already carry attributes (`OpInfoRecord.meta`, WI-087, read by `meta_has_flag`), the same channel `@[simp]`, `@[internal]` and `@[Profile: "cpp20-stl"]` ride.

AND THE MARKER IS ABOUT BODY-LESSNESS, NOT ABOUT DICTIONARIES — measured, because the obvious extension is to declare a builtin's `requires` beside its arity (`HostFn { arity, f }`) and check the two agree. EXACTLY ONE builtin reads a dispatching dictionary: `type_value_of_self`, backing `anthill.reflect.TypeValue.type_value`, and it is the pure case — nullary, so the dictionary is not extra evidence but its ONLY evidence ("`type_value()` is nullary and the dictionary is its only evidence"). Every other host function answers from its arguments. A declaration channel for a population of one is machinery nothing drives, and that single case already fails loudly and specifically when the dictionary is absent, which is what the check would have bought. So this ticket stays about "is this operation body-less BY DESIGN"; revisit only if a second dictionary-reading builtin appears.

WHAT TO DECIDE AT PICKUP.
 (a) THE LOAD CHECK, which is the point of the marker: declared host-implemented AND no binding in the loaded closure supplies it ⟹ a LOAD error naming the missing layer, not an eval death. And its converse — mapped but not declared — is the drift check.
 (b) ONE SOURCE OF TRUTH. The marker is the CLAIM, the binding layer is the EVIDENCE, and (a) is where they must agree. Two readers that can disagree is the failure this codebase keeps writing comments about; do not let `@[host_implemented]` become a second `is_host_mapped_op`.
 (c) MIGRATE THE 33. `register_if_present` should become `operation_map` blocks in `rustland/anthill-stl/anthill/`, so the spec members stop being invisible. This is the bulk of the work and the part that makes "which spec members are host-backed?" a grep of the binding layer.
 (d) NOT A NEW EVAL GATE. `spec_instance_for_sibling_call`'s builtin skip must keep asking `self.builtins`, the map step 2 itself dispatches from: a declaration says host-implemented SOMEWHERE, and a gate keyed to anything but the deciding map can drift from it.

ACCEPTANCE: the marker parses and reaches `OpInfoRecord.meta`, DRIVEN; a declared-but-unsupplied operation is a LOAD error naming it, with its control — the same program with the binding layer loaded runs; a mapped-but-undeclared one is reported too, or (b) is re-justified; the 33 migrate and `is_interpreter_mapped_op` covers them, measured by a count before and after; full workspace green via rustland/scripts/test.sh.

REFERENCE: `KnowledgeBase::is_host_mapped_op` / `is_interpreter_mapped_op` (kb/mod.rs, WI-876/WI-886), `eval::builtins::register_standard_builtins` and `register_operation_mappings` (WI-880), `OpInfoRecord.meta` (WI-087), `common::collect_stdlib_and_rust_bindings`, proposal 038.

## Changes

### 2026-09-23T11:16:39Z — feedback — user

Delivered (2026-09-23). Decisions: STRICT check chosen by the user — the stdlib alone no longer loads; every harness loads stdlib + rustland/anthill-stl/anthill; the WI-1117 'declaration without binding' split is reversed (anthill-core fixtures load coordination_rust.anthill + forge_* test stand-ins). Drift check kept as an error; a mapping over a BODIED op is its own refusal. Attribute refused off operations and with a value (converter). Measured: 137 -> 183 rust-mapped ops, 46 -> 0 registered builtins invisible to is_interpreter_mapped_op. Visibility consequences pinned: Map.size(...) = 1 now DECIDES at a rule-body operand (it suspended), FiniteCollection.size(m) runs Map's host size; reducing Map calls across bridge interpreters exposed a latent arena bug (handle read against another interpreter's slot table: panic, or a silent read of another map) — map/cell bodies are now read through the handle's own arena. KNOWN GAP: anthill-stl's reflect set (register_reflect_builtins, closures over ReflectSyms) still registers by qualified name; its operations are unmarked and invisible. The Substitution arena keeps the receiver-arena read shape.

