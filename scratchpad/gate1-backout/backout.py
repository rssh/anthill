#!/usr/bin/env python3
"""Back out ONE axis of WI-20260909-S8CBV gate (1) and ASSERT the patch applied.

    python3 scratchpad/gate1-backout/backout.py {rung|anchor|delta}
    rustland/scripts/test.sh -p anthill-core --test wi_tests -- s8cbv
    git checkout rustland/anthill-core/src/kb/          # restore between axes

A back-out that silently no-ops reports "no failures", which is indistinguishable
from a control that measures nothing.  Every replacement asserts its pattern
matched exactly once.  `.filter(|_| false)` keeps the call site compiling and its
callee live, so only the ROUTE is removed.

The measured row counts are in the header of
`rustland/anthill-core/tests/include/wi_s8cbv_projection_requirement_test.rs`.
"""
import sys, pathlib

ROOT = pathlib.Path("rustland/anthill-core/src/kb")

AXES = {
    # 1. THE LOADER RUNG — the drop rule never learns the third kind, so `p.E` is
    #    reported as a name that spells no sort (WI-20260909-51W18's message).
    "rung": ("load.rs",
             "if let Some(occ) = self.try_require_spec_projection(parse_id) {",
             "if let Some(occ) = self.try_require_spec_projection(parse_id).filter(|_| false) {"),
    # 2. THE ANCHOR ROUTE — `anchor_grounding` falls back to the `provides` scan,
    #    which asks whether the ROOT'S BOUND provides the spec.
    "anchor": ("typing.rs",
               "carrier_param.and_then(|p| written_projection_anchor(kb, spec_arg, p));",
               "carrier_param.and_then(|p| written_projection_anchor(kb, spec_arg, p)).filter(|_| false);"),
    # 4. THE STATIC MEMBER CHECK — a member the root's data-sort bound cannot declare
    #    goes back to loading clean and residualizing.
    "member": ("typing.rs",
               "        if let Some((_, member)) = projection_anchor {\n            if kb.sort_has_constructors(bound_head) {",
               "        if let Some((_, member)) = projection_anchor {\n            if false && kb.sort_has_constructors(bound_head) {"),
    # 5. THE SUSPEND ARM — a carrier that does not bind the member decides the guard
    #    FALSE instead of delaying (WI-067's silent drop).
    "suspend": ("typing.rs",
                "        None => Err(FindDictOutcome::Suspend),\n    }\n}",
                "        None => Err(FindDictOutcome::DontFire),\n    }\n}"),
    # 3. THE RUNTIME δ — the member never reaches the guard/fetch, so the carrier
    #    type read is `Box[E = …]` itself rather than its `E`.
    "delta": ("resolve.rs",
              "let project = super::typing::requirement_projection_member(self, &spec_arg_val);",
              "let project = super::typing::requirement_projection_member(self, &spec_arg_val)\n            .filter(|_| false);"),
}

axis = sys.argv[1]
fname, old, new = AXES[axis]
p = ROOT / fname
s = p.read_text()
n = s.count(old)
assert n == 1, f"{axis}/{fname}: pattern matched {n} times, expected exactly 1"
p.write_text(s.replace(old, new, 1))
print(f"APPLIED {axis} -> {fname}")
