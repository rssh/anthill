## Attributes

- id: WI-20260821-W9SD3-a-relative-qualified-rule-head
- created: 2026-08-21T19:01:49Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T19:01:49Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A RELATIVE QUALIFIED RULE HEAD THAT NAMES NOTHING LOADS CLEAN, and its clause is stored
under the WI-476 bare intern where nothing can cite it. The absolute spelling is refused
and a body goal is refused; only this one is silent.

MEASURED (rustland, current tree) -- the extension-point shape a plugin would naturally
write:
  file A  namespace app.workflow        { fact stage("draft") }     -- no `allowed` here
  file B  namespace app.plugins.review  { rule app.workflow.allowed("draft", "review") }
  file C  namespace app.plugins.ship    { rule app.workflow.allowed("review", "shipped") }
  -> LOADS CLEAN, no diagnostic. `app.workflow.allowed` DOES NOT RESOLVE, and both plugin
     clauses are stored under the bare intern.
CONTROL, the same program with one unqualified head in `app.workflow` to introduce the
name: `app.workflow.allowed` = 3 clauses and every goal answers.

THE INCONSISTENCY IS THE POINT. Three shapes ask the same question and get three answers:
  * a rule BODY goal naming nothing            -> REFUSED, "rule-body goal `x` names
                                                  nothing: no rule, fact, operation,
                                                  entity, const or builtin is declared
                                                  under that name" (WI-1034)
  * an ABSOLUTE head naming nothing (`..a.b`)  -> REFUSED (`refuse_unresolvable_absolute_
                                                  head`, WI-1075)
  * a RELATIVE qualified head naming nothing   -> SILENT
and the silent one is the spelling a contributing file would actually use.

MECHANISM, confirmed at the site. `Loader::refuse_unresolvable_absolute_head`
(kb/load.rs) opens with
    if absolute_path_target(name).is_none()
        || self.resolve_dotted(name, DottedVisibility::Any).denotes() { return; }
The first clause narrows the check to the `..`-MARKED spelling. A relative dotted head
takes the early return, and `remap_name_str`'s bare `intern(name)` then files the clause
under one global name -- WI-894's defect class, reached from a direction WI-894 did not
cover, since §WI-896 makes a qualified head a REFERENCE that never introduces.

NOT WI-20260821-RDGQC. That ticket is about which head SHAPES the scan collects at all
(facts, multi-head rules, `provides`-block heads, paren-less nullary heads). This head IS
collected; the defect is that it references a target that does not exist and nothing says
so.

WATCH FOR: the refusal must not fire where the target is introduced LATER in the same
scan -- a qualified head may legitimately precede the unqualified one that introduces the
name (measured: `rule qd.p(2)` in one file and `rule p(1)` in another load to one
predicate in BOTH file orders). So the check belongs after the whole program is loaded,
where WI-980's own hole check sits, not at the head's own load.

RELATED, and the reason this was found: proposal 061 (WI-20260821-FQC85) needs a
declaration precisely so a library can own a predicate whose clauses all arrive from other
files. Until it exists, the qualified-head spelling is how such a program would be
written, and this defect makes the broken version indistinguishable from the working one.

ACCEPTANCE: the three-file program above is a located load error naming the head and the
name it fails to reach. CONTROLS: the same program with an introducing head still loads
and answers; a qualified head written BEFORE the file that introduces the name still loads
in both file orders. Say at the site which rows fail on a back-out. cargo-test green via
rustland/scripts/test.sh.

