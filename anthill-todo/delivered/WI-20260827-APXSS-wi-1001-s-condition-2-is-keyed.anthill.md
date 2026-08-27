## Attributes

- id: WI-20260827-APXSS-wi-1001-s-condition-2-is-keyed
- created: 2026-08-27T14:10:30Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-27T19:09:06Z

- acceptance: cargo-test, scaland-sbt-test

## Description

WI-1001's CONDITION (2) IS KEYED ON THE "INTRODUCES" SITE SET, WHICH BY CONSTRUCTION EXCLUDES THREE SPELLINGS THAT STILL LAND CLAUSES ON THE SAME PREDICATE. Each admits a main-entry clause beside the secondary entry's rule -- 059's worked harm, arriving through the exact route R3 exists to close. Found by /code-review on the WI-20260827-P1TPE diff; the reviewer drove all three.

WHY IT IS NEW: before WI-1001 (commit b09aa9f1) the entry's rule was banned outright, so none of these could compose.

THREE ROWS, EACH LOADING CLEAN AND EACH LEAVING THE PREDICATE WITH TWO CLAUSES FROM TWO ENTRIES. Reported by the reviewer as measured on that tree; RE-DRIVE THEM FIRST -- they are quoted here, not re-run by the filer.

  (1) A DOTTED `fact` HEAD -- `fact_head_functor_name` (rustland/anthill-core/src/kb/load.rs:8370)
      returns None when the local name contains a `.`, so the head never enters `fact_heads`.

        namespace probe.dotted
          sort Rec  entity rec(n: Int64)  fact Rec.freshp(2)  end
          namespace Rec  rule freshp(1) :- true  end
        end

      loads clean; `probe.dotted.Rec.freshp` holds 2 clauses; `freshp(2)` answers 1.
      CONTROL: the UNDOTTED `fact freshp(2)` is correctly refused ("assembled from more
      than one entry").

  (2) A DOTTED RULE HEAD IN THE MAIN ENTRY -- `rule_introduced_functor_name`
      (load.rs:8512) returns None for a qualified head, so it is never a `RuleHeadSite`
      and `in_main_entry` stays false.

        namespace probe.drule
          sort Rec  entity rec(n: Int64)  rule Rec.freshp(2) :- true  end
          namespace Rec  rule freshp(1) :- true  end
        end

      loads clean; 2 clauses; `freshp(2)` answers 1. NOTE THE ASYMMETRY: the SAME
      qualified spelling inside the SECONDARY entry IS refused
      (`a_desugared_or_qualified_head_introduces_nothing`), so only the main-entry side
      leaks.

  (3) A FACT IN A SCOPE NESTED INSIDE THE MAIN ENTRY -- the census filters `f.scope ==
      scope` (load.rs:8538). The doc argues only ENCLOSING scopes fall away; a DESCENDANT
      scope resolves UP the chain to the entry's predicate and is missed.

        namespace probe.nested
          sort Rec  entity rec(n: Int64)
            sort Inner  entity inn(n: Int64)  fact freshp(2)  end
          end
          namespace Rec  rule freshp(1) :- true  end
        end

      loads clean; 2 clauses; `freshp(2)` answers 1.

ONE TICKET BECAUSE IT IS ONE CAUSE: condition (2) censuses the sites that INTRODUCE a name, and what it needs is a census of where a clause LANDS. A dotted head introduces nothing and still lands; a nested-scope fact resolves up and still lands. Fixing any one of them by adding a spelling to the "introduces" set leaves the others.

AND THE SPEC CLAIM IS CURRENTLY FALSE: kernel-language.md's new sentence -- "every clause of that name at that scope being written in this same entry" -- is not what the code enforces. It must become true or be narrowed.

ACCEPTANCE: the three programs above driven as tests, each REFUSED at load with the same "assembled from more than one entry" diagnostic the undotted control already gets (or, if any of the three is deliberately legal, the reason written at the predicate and the spec sentence narrowed to match); the undotted control and the secondary-entry qualified-head refusal both still green; `a_desugared_or_qualified_head_introduces_nothing` unmoved; the census keyed on where the clause LANDS rather than on the introduces-site set, said at the site; kernel-language.md's sentence true of the code; full workspace green via rustland/scripts/test.sh.

REFERENCE: `fact_head_functor_name` / `rule_introduced_functor_name` / the fact census's scope filter and `judge_secondary_entry_rules` (rustland/anthill-core/src/kb/load.rs ~8370, ~8512, ~8538), proposal 059, WI-1001 (delivered in b09aa9f1).

