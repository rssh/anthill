```anthill
fact WorkItem(id: "WI-20260818-K63ZV-anthill-todo-backend-the-head", created: "2026-08-18T15:32:43Z", context: none, acceptance: [ToolPasses(tool: "cargo-test", params: none), ToolPasses(tool: "scaland-sbt-test", params: none)], depends_on: some(value: ["WI-1120"]), generates: none, requires_capability: none, status: Open)

fact Tag(workitem: "WI-20260818-K63ZV-anthill-todo-backend-the-head", name: "wi437")

fact Feedback(workitem: "WI-20260818-K63ZV-anthill-todo-backend-the-head", author: "claude", at: "2026-08-18T15:37:52Z")

fact Feedback(workitem: "WI-20260818-K63ZV-anthill-todo-backend-the-head", author: "claude", at: "2026-08-18T15:47:13Z")

fact Feedback(workitem: "WI-20260818-K63ZV-anthill-todo-backend-the-head", author: "claude", at: "2026-08-19T07:42:14Z")

fact Feedback(workitem: "WI-20260818-K63ZV-anthill-todo-backend-the-head", author: "claude", at: "2026-08-19T09:40:41Z")
```

## description

anthill-todo backend: DEFINE THE ITEM DOCUMENT FORMAT AND MIGRATE THE TREE ONTO IT. The format is settled and written -- `rustland/anthill-todo/docs/design/DRAFT-document-mapping.md`, which replaces design §5.3 and §5.4 -- with seven real items converted under it in `docs/design/samples/`, each verified field by field. The decisions and the arguments behind them are in this ticket's feedback; the draft is a specification and carries neither. Branch: `wi-k63zv-document-format-samples`. WHAT REMAINS IS IMPLEMENTATION.

THE SHAPE. An item file is a sequence of markdown chapters. `## Attributes` holds the item's own fact as a bullet list of DATA -- not an anthill application -- with `## Description`, `## Reason` and `## Changes` beside it:

    ## Attributes

    - id: WI-1121
    - created: 2026-08-17T08:43:54Z

    - status: Delivered
    - status_agent: claude
    - status_at: 2026-08-18T15:28:04Z

    - acceptance: cargo-test, scaland-sbt-test

    - depends_on: WI-1114

    - tags: wi437

against today's `fact WorkItem(...)` on one physical line, MEAN 279 characters and longest 2062.

FOUR THINGS THE ENCODING RESTS ON. (1) A value's spelling follows its DECLARED TYPE -- unquoted string, bare variant name, comma-separated list, absent means none -- with a BACKTICKED ANTHILL TERM as the total escape, so the writer never refuses a value. The reader therefore reads the domain's entity declarations alongside the mapping, which is a departure from §5.3's "never learns stage0's schema" and is stated as one. (2) BLANK LINES ARE THE COUPLING DECLARATION, measured on git 3-way merges: two edited lines with nothing between them CONFLICT, with one unchanged line between them MERGE. Adjacency says "these change together"; `FieldGroup` declares which. (3) A SATELLITE'S KEY IS NOT WRITTEN -- an entry in this file is about this item -- and it is filled from the document's own `id` ATTRIBUTE, never from the path, or a hand-renamed file would silently re-attribute every entry in it. (4) ENTRIES CARRY A KIND (`### <at> — feedback — <author>`), which is what makes status and tag entries additive later instead of a fourth full-tree rewrite.

TWO DOMAIN CHANGES, BOTH REQUIRED. `WorkStatus` becomes a plain nullary enum and `WorkItem` gains `status_agent` / `status_at` / `status_reason` as Options. This finishes WI-1120's job rather than merely tidying: per FIELD, the longest value in any head on this tracker is `status` at 1842 characters (WI-1115), so THE 2062-CHARACTER MAXIMUM LINE IS A REJECTION REASON -- prose WI-1120 missed because it sat inside a variant payload. `status_reason` becomes a `## Reason` chapter through the existing `Chapter` mechanism. It also records who acted for every transition; `Verified` carries no agent today.

THE MAPPING GAINS THREE KINDS, and they are in the draft's §5: `FieldGroup` (adjacency), `ScalarForm` (a bare scalar denoting a one-slot constructor -- `acceptance: cargo-test` is `ToolPasses(tool: "cargo-test")`, and `acceptance` is 100% `ToolPasses` across 1157 occurrences), and `SatelliteList` (a list field expanding to one fact per element, which is how `tags` works). `ChapterGroup` gains `kind` and `key`, and loses `named_by`/`decorate` to a single `heading` list.

THE MIGRATION IS NOT A PURE REFORMAT, and the earlier claim that a before/after per-functor row count is a complete correctness check is FALSE under these decisions: the row count is identical while 1127 status values change shape and 12 reasons move into chapters. THE CHECK MUST BE PER FIELD over the reconstructed status -- read the tree before, read it after, and compare each WorkItem fact field by field once `Claimed(agent: a, since: t)` is normalised against `status: Claimed / status_agent: a / status_at: t`. The conversion of the seven samples was checked exactly this way and is the model for it.

ONE FIELD IS KNOWINGLY LOSSY, decided rather than discovered: `depends_on: some(value: nil)` becomes absent, which reads back as `none`. `some([])` and `none` are different values and 692 items write the former. NO round-trip test can see this -- both sides read as "no dependencies" -- so it is recorded here because nothing will re-derive it.

DRIVE THE CAPABILITY, do not assert that it loads. Round-trip a real item -- add / feedback / tag / claim / update --description -- through the document format and assert the reparsed FACTS equal the pre-write facts. Then the test that justifies the ticket: change one item's status in one checkout and its description in another, and assert git merges them without conflict. CONTROL: the round-trip test passes either way against an unmodified store and measures only the encoding; the merge test is the one that fails when the head is a single line, and a THIRD test must fix the blank line -- two fields written adjacent instead of blank-separated conflict, which is why the separator is a rule and not a style.

COST: a THIRD full-tree rewrite of 1127 files, after WI-1118's and WI-1120's. §11 accepted that arithmetic once and the machinery is rehearsed -- `migrate --to document` exists, is idempotent, and was driven twice on copies before touching the live tree.

FOLLOW-ON, NOT PART OF THIS: a format-aware git merge driver. Measured, two agents appending different feedback entries CONFLICT under the default text merge and merge cleanly under `merge=union`, which is built in and needs no per-clone config -- but git grants a driver per PATH, never per region, and union over a whole item file would union a status change into two status lines. A driver (`anthill-todo merge %O %A %B`) is small because the reader and writer already exist, degrades to an ordinary conflict when not installed, and is independent of this ticket.

## Feedback

### 2026-08-18T15:37:52Z — claude

PRIOR ART SURVEYED 2026-08-18, because 'attach metadata to a document' is a solved problem elsewhere and this ticket should not re-invent it. THE FINDING IS THAT NOTHING FITS OFF THE SHELF, and the reason is precise rather than a matter of taste: EVERY EXISTING CONVENTION BUNDLES A LAYOUT WITH A VALUE LANGUAGE. We want the layout and already have the language — a field's value here is an anthill term (`status: Claimed(agent:, since:)`, `acceptance: [ToolPasses(…)]`), and §5.3 chose the fenced anthill block precisely so there would be no second scalar language and so the LOADER COULD CHECK the head (WI-928 found 921 mismatches the first time that check ran). So the question to ask of each candidate is not 'is it good' but 'does it bring a language we must then refuse'.

FOUR CONSTRAINTS, and a candidate has to meet all of them: (a) it RENDERS in a `.md` on GitHub — the trailing `.md` is the whole reason §5.4 chose that suffix; (b) it is LINE-ORIENTED, which is this ticket's actual prize (per-field diffs, so two agents editing different fields of one item merge); (c) it brings NO second scalar language; (d) the loader can still check it against the declared domain.

WHAT WAS SURVEYED:

* YAML FRONTMATTER (`---`) — the overwhelming default: Jekyll, Hugo, Obsidian, Pandoc, GitHub Docs. And it does render: GitHub turns a frontmatter block at the TOP of a `.md` into a table. DISQUALIFIED on (c), and WI-1120's own feedback already refused it on a second ground — 'two heads is two writable homes for one datum', the failure §7's governing principle exists to prevent. Worth recording that the render is ALSO reported as hard to read, because YAML is not written to be a table; so the rendering argument in its favour is weaker than it first looks.
* TOML (`+++`) and JSON frontmatter — same disqualification, less tooling.
* GIT TRAILERS / RFC-822 folding — the closest prior art to what you meant by 'attribution is a common problem', and genuinely well-tooled: `git interpret-trailers` parses, normalises and appends `Key: Value` lines, with RFC-822 style continuation for multi-line values. IT FAILS (a), DECISIVELY: in a `.md` file GitHub follows CommonMark and JOINS soft line breaks, so a block of bare `key: value` lines renders as one run-on paragraph. That is exactly why the convention works for commit messages — which are never rendered as markdown — and cannot work for a document. (GitHub does break single newlines in ISSUE COMMENTS, which is why the shape looks fine when pasted there and is not fine in the file.)
* DEFINITION LISTS (`term` / `: value`) — the markdown-native spelling of key→value, and the obvious answer. NOT IN GFM: kramdown and PHP Markdown Extra have them, GitHub does not. Out on (a).
* DATAVIEW INLINE FIELDS (`key:: value`) — Obsidian's, and the only convention surveyed that can attach fields to an individual LIST ITEM rather than the whole page. Renders as literal `::` text on GitHub. Ecosystem-specific.
* HTML-COMMENT FRONTMATTER — invisible by design, which is the opposite of what this format wants: §5.3 makes every projection loud precisely so it can be CHECKED and repaired, and a projection nobody can see is one nobody corrects.

WHAT SURVIVES ALL FOUR is a markdown LIST or a markdown TABLE of fields, with anthill terms as the values — i.e. borrow the LAYOUT, keep the language:

  - id: WI-1121
  - created: 2026-08-17T08:43:54Z
  - status: Claimed(agent: "claude", since: "…")

or

  | field | value |
  | --- | --- |
  | id | WI-1121 |
  | status | Claimed(agent: "claude", since: "…") |

The table is the interesting one: it gives GitHub a REAL table with no YAML anywhere — the thing people actually like about frontmatter rendering, without the second language that disqualified it. The list is denser and reads better as a diff. Both are one line per field, so both buy this ticket's merge property.

AND THE READER MACHINERY LARGELY EXISTS. A rendered field block would live BEFORE the first structural heading — which is exactly the region `Document::body_start` already delimits (`persistence/document.rs`: everything before the first chapter is one stretch of text the scanner does not interpret). So this is a new READER over a region the model already isolates, not a new document model.

THE OPEN QUESTION IS NARROWED, NOT ANSWERED: fenced field map (this ticket's proposal — invisible to a GitHub reader but unambiguously the machine's region), markdown list, or markdown table. Decide it by rendering ONE REAL ITEM three ways and looking at the page, which is what this ticket already says about tags — and decide the tag question in the same pass, since a `tags:` row in a field table and a `- tags: [wi437]` list item are the same decision wearing two hats.

Sources: git-scm.com/docs/git-interpret-trailers; github.github.com/gfm; blacksmithgu.github.io/obsidian-dataview/annotation/add-metadata; docs.github.com/en/contributing/writing-for-github-docs/using-yaml-frontmatter; github.com/orgs/community/discussions/70092 (GitHub's frontmatter-as-table rendering); github.com/orgs/community/discussions/178337 (that render reported as hard to read).

### 2026-08-18T15:47:13Z — claude

THE FIELD SET AND THE LAYOUT ARE SEPARABLE QUESTIONS, and this ticket currently runs them together. Recorded so the split is on the ticket rather than lost:

  * WHICH FIELDS EXIST is a data question — may `id:` leave the head, given the filename already carries it? may `Feedback.workitem` leave, given the file is its item?
  * HOW THEY ARE LAID OUT is a rendering question — fenced field map, markdown list, or markdown table (see the prior-art note above).

Either can be decided without the other, and each has its own argument.

ON THE FIELD SET, two corrections to reasoning that has been used loosely in this area — including by me:

1. `id` IS DUPLICATED, in the filename and in the head, and calling that 'a projection, not duplication' overstates it. It IS duplication. What makes it SAFE is three properties, and they are worth naming because they are the test any future duplication should be held to: the second copy is DERIVED (never authored), the direction is SETTLED IN ADVANCE (the fact wins, §4), and disagreement is LOUD AND REPAIRABLE (`PathDisagreement`, plus the filename-vs-id check WI-1120 added). Duplication is a COST; UNDECIDABLE duplication is the failure the one-writable-home rule (§7) exists to prevent. Do not read that rule as forbidding derived copies — it forbids two places you can WRITE.

2. §6.5's 'IDENTITY IS THE FACT, NOT THE PATH' — the third of its three deliberate divergences from OKF — DOES NOT BLOCK removing `id:` from the head, and it would be easy to think it does. That argument is about the DIRECTORY: status is in the path and status CHANGES, so path-as-identity would mean an item's identity changed every time it was claimed. The FILENAME does not change on a status change; §5.1's move carries the same filename to a new directory. So identity in the filename is not what that clause refuses.

WHAT ACTUALLY HOLDS `id:` IN PLACE IS A MECHANISM, NOT A PRINCIPLE: `ItemPerFileStore::route_of` routes a row BY ITS FIELDS — it reads the `id_field` to decide which file the row belongs in — so a row carrying no id cannot be routed. That is a real constraint and an implementation choice, not a rule: `record_file`/`record_document` already have the path in hand, so routing could take the ID FROM THE FILENAME and the STATUS FROM THE ROW. The two halves of the path would then have two different sources, which is worth thinking about rather than waving through.

AND THE MACHINERY FOR THE REST ALREADY EXISTS. Filling a field into a fact before the loader sees it is exactly the splice WI-1120 performs for chapters (§5.5: the splice produces the parse IR a plain `fact` file would have). So `id` from the filename, and `Feedback.workitem` from the file — 1173 repetitions of a key the path already carries — are the same mechanism pointed at a different source.

THE HONEST RESIDUAL COST, and it is the thing to weigh rather than the principle: a row that LEAVES its file no longer says what it is about. That is not hypothetical — `orphaned.anthill` (§11) holds satellite rows whose item has no file, an export writes rows outside the tree, and a query result renders a row with no path. Each would need the identity re-attached or would lose it. Weigh that against 1459 repeated keys and a 278-character mean head line.

RELATED, from the same conversation and worth keeping with it: IF EVERY DOCUMENT CARRIES ITS OWN FIELDS, A SECONDARY INDEX BECOMES UNNECESSARY — the tree is the index, which is what `list` and `fsck` already assume. If one is ever wanted anyway (for a reader that will not scan a tree), making it OKF-compatible costs little and is an EXPORT, not a change to the native format — the position WI-1120's own OKF feedback already reached, and still not filed anywhere.

### 2026-08-19T07:42:14Z — claude

THE LAYOUT QUESTION IS SETTLED BY MEASUREMENT, NOT BY LOOKING AT A PAGE, and three of the four candidates fall to facts rather than to taste. The prior note narrowed this to "fenced field map, markdown list, or markdown table -- decide by rendering one real item three ways". Two of those three are now disqualified, and the surviving one is not the one that note favoured.

(1) FIELD-PER-LINE IS NOT THE PRIZE. FIELD-PER-LINE PLUS A BLANK LINE IS. Measured on real git, one branch changing `status` against another changing `acceptance`:

  head as one physical line (today)          -> CONFLICT
  one field per line, the two ADJACENT       -> CONFLICT
  one field per line, a blank line between   -> clean

Isolating the rule: with 0 unchanged lines between the two edited lines git conflicts; with 1 or more it merges. So the ticket's reduction (2) as written does NOT buy the merge property -- two co-edited fields that happen to sit next to each other conflict exactly as the 278-character line does. The blank line is load-bearing and belongs in the ticket's text.

(2) THE TABLE IS DISQUALIFIED ON THIS TICKET'S OWN SUCCESS CRITERION, which is a stronger objection than the escaping one raised in review. GFM parses table cells as inline content and needs `|` escaped -- a second escaping layer -- but the decisive fact is that a blank line TERMINATES a table. Per (1) the blank line is what buys the merge, so a table cannot buy the property this ticket exists for. It is not a weaker candidate; it is a non-candidate. (github.github.com/gfm/#tables-extension-)

(3) YAML IS OUT ON A SYNTAX COLLISION, NOT ON A PRINCIPLE, and the collision is checkable. Run against a real YAML parser:

  REJECT  status: Claimed(agent: "claude", since: "2026-08-18T05:22:11Z")
     ==>  mapping values are not allowed in this context, line 1 column 22
  REJECT  acceptance: [ToolPasses(tool: "cargo-test"), ToolPasses(tool: "scaland-sbt-test")]
     ==>  did not find expected ',' or ']' while parsing a flow sequence
  OK      created: 2026-08-17T08:43:54Z
     ==>  {"created" => 2026-08-17 08:43:54 UTC}      <- a Time, NOT the String the domain declares

anthill's named-argument syntax IS YAML's mapping indicator (`: `). The two most information-dense fields in the head are YAML SYNTAX ERRORS, and the one field that parses is SILENTLY RETYPED. Repairing that means quoting every term-valued field -- the same second escaping layer that killed the table, except it bites UNIVERSALLY rather than occasionally. The prior note refused YAML on "it brings a language we must then refuse"; the sharper statement is that the two languages collide at the character level.

THIS ALSO CONVICTS THE HEAD THIS TICKET PROPOSES. `id: WI-1121`, `created: 2026-08-17T08:43:54Z` and `depends_on: [WI-1114]` are BARE SCALARS -- they mean something only under YAML's rule that an unquoted scalar is a string, which anthill does not have. The description says "THIS IS NOT A MOVE TO YAML" and then writes YAML's scalar language. Values must keep their anthill spelling.

And the third reading -- YAML's `---` delimiters around non-YAML content -- is the worst option rather than a compromise: GitHub attempts to parse frontmatter as YAML, fails, falls back to CommonMark where `---` is a thematic break and the field lines are soft-joined into ONE RUN-ON PARAGRAPH. That is precisely the failure the git-trailers survey already recorded, reached by a different road.

(4) THE GENERAL RULE THE TABLE OBJECTION IS AN INSTANCE OF: any layout that puts a value in MARKDOWN INLINE CONTEXT needs a second escaping layer over it. That convicts the bare bullet list too -- `[...]` is link syntax, `_`/`*` emphasis, backticks code spans, `<` HTML -- and every head carries at least two bracketed lists. BUT THE ESCAPE HATCH IS MARKDOWN'S OWN: a CODE SPAN suspends inline parsing. So the surviving shape is a bullet list whose values are code spans:

  - id: `WI-1121`
  - created: `2026-08-17T08:43:54Z`
  - acceptance: `[ToolPasses(tool: "cargo-test"), ToolPasses(tool: "scaland-sbt-test")]`

A blank line between bullets makes the list LOOSE, it does not end it -- which is exactly where the table died, and it is why the list survives (1) and the table does not. THE BACKTICKS ARE REQUIRED, NOT OPTIONAL: an optional wrapper is two spellings for one datum, which is the 344-bare-against-766-wrapped hazard §5.5 already recorded as the cause of a live bug.

THE FENCE REMAINS THE CHEAPER OPTION AND SHOULD BE STATED AS THE ALTERNATIVE rather than dropped: inside a fence the reader consumes ZERO markdown tokens (the list form must strip `- ` and a backtick pair), the region already exists, and the change becomes "what is inside the block" rather than a new region. What the list buys over it is that the head renders as CONTENT rather than as a code block, which is why `.md` was chosen at all. Correcting the prior note on one point of fact: a fenced block is NOT "invisible to a GitHub reader" -- it renders as a visible code block, un-pretty rather than unseen.

(5) THE BLANK LINE IS THE HEAD'S COUPLING DECLARATION, and this is what makes flattening `status` safe. From (1): adjacency conflicts, separation merges. Read that as a design tool rather than a constraint --

  A BLANK LINE MEANS "THIS FIELD CHANGES INDEPENDENTLY".
  ADJACENCY MEANS "THESE FIELDS CHANGE TOGETHER".

-- and the layout encodes which fields form a transition. `id`, `created`, `acceptance`, `depends_on` are blank-separated because they are independent; the status group is written ADJACENT with no blanks, so two concurrent status edits collide as they should instead of silently interleaving into a half-transition.

(6) STATUS FLATTENS -- `status: Claimed` plus sibling fields (user, 2026-08-19) -- AND THE MEASUREMENT SAYS IT FINISHES WI-1120'S JOB RATHER THAN MERELY TIDYING. Per-field, the longest value in any head on this tracker is not `depends_on` or `acceptance`. It is `status`, at 1842 characters (WI-1115): `ProposalRejected(reason: "SPLIT 2026-08-17, not abandoned ...")`. THE 2062-CHARACTER MAXIMUM HEAD LINE THIS TICKET OPENS WITH IS A REJECTION REASON. WI-1120 moved `description` and `Feedback.content` out of the head because they are prose, and MISSED this one because it was buried inside a variant payload. Flattening exposes it, and then the EXISTING `Chapter` mechanism takes it -- `status_reason` is prose and becomes a chapter, with no new machinery. 12 items carry a reason.

With the reason moved, every remaining head value is a one-liner: the longest is `depends_on` at 205 characters (WI-648, 19 dependencies) and exactly one field value on the whole tracker exceeds 110. So the code-span form in (4) needs NO multi-line spelling, and one spelling is what it should have.

TWO CONSEQUENCES THAT MUST BE DECIDED, NOT ASSUMED:

  * THE KEY MUST BE AN ANTHILL FIELD NAME. `status-change-agent` is not one -- this domain writes `snake_case` (`depends_on`, `requires_capability`) -- so it wants `status_agent` / `status_at` / `status_reason`.
  * THE DOMAIN FLATTENS TOO, or the reader learns the schema. `status: Claimed` bare is already valid anthill (the tracker writes `status: Open` bare in 121 places), but `Claimed` is NOT nullary today. Either `WorkStatus` becomes a plain nullary enum and `WorkItem` gains `status_agent`/`status_at`/`status_reason` as Options -- the document then being a direct field map -- or the mapping SYNTHESIZES `Claimed(agent:, since:)` from three head lines, which requires a per-variant payload table, i.e. exactly the stage0 schema knowledge §5.4 says the reader must never learn. TAKE THE DOMAIN CHANGE.

It also repairs a wart worth naming: today the payloads are irregular -- `since` on Claimed/Stale, `at` on the other four, `agent` on only two, and `Verified` carries NO agent at all, so "who verified this" is currently unrecorded. The uniform triple records it for every transition, and makes that one change instead of two.

AND IT CHANGES WHAT THE MIGRATION IS. The description promises "a pure reformat with no data change, so a before/after per-functor row count is a complete correctness check". With status flattened that is NO LONGER TRUE: the row count is unchanged while every status value is rewritten into a different shape. The check must become per-field, over the reconstructed status, or it proves nothing about the half of the change that can actually go wrong.

(7) THE FIELD SET, decided (user, 2026-08-19):

  * `id` STAYS. It is the filename-versus-fact integrity check, and it keeps a row meaningful in an export, in query output and in `orphaned.anthill`. Without it an accidental filename rename is an UNDETECTABLE identity change. This also settles `status`'s presence in the head by the identical argument -- it is duplicated by the DIRECTORY as `id` is by the filename, it is what §10's directory-versus-status check compares against, and without it a stray `mv` between status directories is an undetectable state change. The ticket's reduction (3) is therefore narrowed to the always-absent fields, not to the keys.
  * `Feedback.workitem` STAYS FOR NOW, deferred until every context-free representation has an explicit key-reattachment contract. `Tag.workitem` defers with it by the same argument, so `tags: [wi437]` as a collapsed head field waits too -- 287 rows, not the prize.

THE DEFERRAL HAS A COST, AND IT IS THE ONE THE NEXT POINT IS ABOUT: keeping `Feedback.workitem` in the head is what forces every feedback append through the one region that cannot be auto-merged.

(8) FEEDBACK APPENDS CONFLICT TODAY, AND THAT IS THE MOST COMMON CONCURRENT AGENT OPERATION. Measured -- two branches each appending a different `###` entry:

  default text merge                          -> CONFLICT
  `merge=union` via .gitattributes            -> clean, both entries kept

`union` is a BUILT-IN driver, so `.gitattributes` alone enables it with no per-clone `git config` -- it travels with the repo. Two caveats the run exposed: union does NOT order (the 08-03 entry landed before the 08-02 one), and it drops the blank line between joined hunks. The ordering caveat is harmless only where nothing binds entries POSITIONALLY -- so it is safe once feedback has one home, and BROKEN today, where §5.4 binds the Nth head row to the Nth entry and union would silently desynchronise them.

THE STRUCTURAL POINT: git grants a merge driver PER PATH, never per region. Union on the item file as a whole would union a `status:` change into TWO STATUS LINES. So append/append has exactly three answers --

  * one file per entry: conflict-free by construction, no git machinery, costs the single rendered page (the reason for `.md`);
  * a FORMAT-AWARE driver, `anthill-todo merge %O %A %B`: keeps one document, unions entries AND sorts by `at` AND merges the head field-wise AND can refuse loudly. It is small precisely because WI-1120 already built the reader and the writer. `.gitattributes` cannot install a custom driver, so each clone needs one `git config` line; ABSENT, git falls back to an ordinary conflict -- loud, not silent, which is the right failure. `fsck` should report the driver missing so its absence is not discovered by surprise;
  * nothing, and every concurrent feedback add conflicts.

The general shape worth recording: CONFLICT-FREEDOM HERE HAS ALWAYS COME FROM DISJOINT BYTES, NOT FROM CLEVER RESOLUTION. WI-1114 got it between items (a file each); the field map gets it between fields (a line each, plus a blank). Only append-into-a-shared-list resists that, because both sides insert after the same anchor. The driver is a separate ticket and independent of the layout; the layout should not wait for it.

(9) THE ALWAYS-ABSENT REDUCTION SHOULD RIDE IN THIS REWRITE, and it is bigger than the description says. Re-measured on 1127 files: `context`/`generates`/`requires_capability` are written 1124 times each (3372), and `params: none` a further 1148 times inside every `ToolPasses` -- so the reduction reaches NESTED applications, not only top-level head fields, and is a PRINTER rule rather than a layout one. About 4500 writes of nothing, roughly 40% of the 279-character mean head line, removable as a genuine reformat.

ONE EXCLUSION, AND THE ROW-COUNT CHECK WOULD NOT CATCH IT: `depends_on: some(value: nil)`, written 692 times, is NOT in that class. `some([])` and `none` are different values, so dropping it is a data change. Decide it deliberately or leave it.

MEASUREMENTS: 1127 item files, 1127 WorkItem / 1196 Feedback / 287 Tag rows; head line mean 279, median 273, max 2062. Merge and YAML results reproduced with git 3-way merges and a YAML 1.2 parser on the exact strings above.

### 2026-08-19T09:40:41Z — claude

DECISIONS TAKEN 2026-08-19, and the format they produce. The prior note argued the layout; this one records what was settled, so the draft at `rustland/anthill-todo/docs/design/DRAFT-document-mapping.md` can be read as a specification rather than as an argument. Seven real items are converted under it in `docs/design/samples/`, each verified field by field against its original.

THE HEAD IS DATA, NOT ANTHILL, and the reason is not taste. A head today is not a valid anthill expression and never was: `content:` and `description:` appear ZERO times in any head, and `Feedback.content` is a required `String` -- it can be neither written `none` nor legally omitted, and the loader tolerates the omission only by filling a fresh var, which §5.5 already records as a gap. So "the head is anthill syntax the loader checks" was never true; the check runs after the splice, on the assembled fact, and runs identically over data. Measured, there is almost nothing left to keep anthill FOR: after status flattens and the always-none fields go, `acceptance` is the only term-structured field and it is 100% `ToolPasses` (1157 occurrences, 8 distinct values).

THE LAYOUT IS A BULLET LIST IN A `## Attributes` CHAPTER. Making it a named chapter removed a special case rather than adding one -- there is now no region outside a chapter, so the data/prose boundary is a heading instead of a guess, and `Document::body_start`'s leading region disappears. A value's spelling follows its DECLARED TYPE (unquoted string, bare variant, comma-separated list, absent = none), with a BACKTICKED ANTHILL TERM as the total escape, so the writer never has to refuse a value. The reader consequently reads the domain's entity declarations alongside the mapping -- a real departure from §5.3's "never learns stage0's schema", stated in the draft rather than buried.

STATUS FLATTENS, AND SO DOES THE DOMAIN. `status` / `status_agent` / `status_at` / `status_reason`, with `WorkStatus` becoming a plain nullary enum. The alternative -- a mapping HOISTING three lines back into `Claimed(agent:, since:)` -- needs a kind keyed by VARIANT (`since` on Claimed and Stale, `at` on the other four), a dozen facts for one field, with nothing checking it stays in sync with the enum. Flattening also finishes WI-1120's job: per FIELD, the longest value in any head on this tracker is `status` at 1842 characters (WI-1115), so THE 2062-CHARACTER MAXIMUM LINE THIS TICKET OPENS WITH IS A REJECTION REASON -- prose that WI-1120 missed because it was buried in a variant payload. `status_reason` is now a `## Reason` chapter. It also records who did it for every transition: `Verified` carries no agent today.

CHAPTER HEADINGS ARE DISPLAY NAMES. `Attributes` / `Description` / `Reason` / `Changes`. The page read `## Attributes` beside `## description` because a container was named for its functor and a field chapter for its field; `Chapter(field:, named:)` already separated the two. Consequence: the names are now case-sensitive keys, so `## description` in a hand-edited file is a load error.

THE CONTAINER IS `Changes` AND ENTRIES CARRY A KIND, WITH NOTHING SYNTHESIZED. `### <at> — feedback — <author>`. The heading is one of the few parts that cannot change without rewriting every file, so paying the kind word now makes status and tag entries ADDITIVE later. The cost is stated rather than hidden: ~1200 entries carry a word all of them share, seventeen consecutively on WI-714. REJECTED: synthesizing one status entry per item from the current status, which would write 1127 entries duplicating the attributes they came from, each an event never recorded as one and nothing marking it manufactured -- real history cannot be migrated, since 985 of 1127 items have already lost who claimed them and when, and `untag` never left a record. A log that begins partly fictional is worse than one that begins short. ALSO REJECTED: omitting the kind for the default, which reads best and is two spellings for one position.

A SATELLITE'S KEY COMES FROM THE FACT, NOT THE FILENAME, and the earlier claim that this was BLOCKED on the `Feedback.workitem` deferral was wrong. Not writing the field in a document is not removing it from the domain: the reader fills it, every loaded fact carries it, and the three context-free representations the deferral protected -- exports, query output, `orphaned.anthill` -- render FACTS. `orphaned.anthill` is a plain `.anthill` file rather than a document and writes the key in ordinary fact syntax, so the whole contract is that a document omits the key and anything that is not a document writes it. The routing objection was wrong for the same reason: the store is handed the fact, never the file text. The key is taken from the document's own `id` ATTRIBUTE and never from the path -- otherwise a hand-renamed file silently re-attributes every entry in it while the filename check reports the rename as an unrelated fault. One fault class disappears: `MisfiledRow` is unrepresentable, a row that does not name an item being unable to name the wrong one.

BLANK LINES ARE THE COUPLING DECLARATION. Measured on git 3-way merges: two edited lines with NOTHING between them CONFLICT, with one unchanged line between them MERGE. So adjacency states "these change together" and a blank line states "these are independent", and `FieldGroup` declares which. Its guarantee is LAYOUT, so it reaches only fields written in the attributes chapter: `status_reason` lives in a chapter and cannot be adjacent to its group. What keeps that pair consistent is the command set, not the format -- `update --status --reason` writes both in one operation and nothing sets a reason alone -- so an inconsistent pair needs a hand-edit and is an `fsck` repair.

THREE SMALLER SETTLEMENTS. (1) A heading ABOVE the first structural level is a LOAD ERROR: `#` is unused in all 1127 files and was unspecified, and closing it beats leaving a level undefined in a format people hand-edit; the title question is separate and needs an authored `title` field, not a mechanical backfill. (2) ENTRY ORDER IS NOT DATA -- facts are unordered, the writer sorts for readability, `fsck --fix` re-sorts, and a reordered container is neither error nor diagnostic. That is also what makes an append-only container safe to merge by CONCATENATION, which cannot preserve order. (3) VALUE LENGTH IS A DIAGNOSTIC, NOT A RULE. A 255-character threshold was proposed to promote long values to sections; measured, it gives one field two shapes -- 35 of 1127 descriptions inline against 1092 in a chapter, 4 of 12 reasons against 8 -- fires on nothing else (every non-prose value maxes at 142 characters), would first cross on `depends_on` at about 24 dependencies where a long LIST is not prose, and would relocate an author's text as it grew past the line. It is now a diagnostic naming the field.

THE MIGRATION IS NO LONGER A PURE REFORMAT, and the description's claim that "a before/after per-functor row count is a complete correctness check" is FALSE under these decisions: the row count is identical while 1127 status values change shape and 12 reasons move into chapters. The check must be per FIELD over the reconstructed status. Separately, `depends_on: some(value: nil)` -> absent is a DATA change, approved 2026-08-19, affecting 692 items -- `some([])` and `none` are different values, and NO round-trip test can see the difference, both sides reading as "no dependencies". It had to be decided rather than measured, and it is written down where a reader will meet it.

Also settled in passing: `List[String]` is legal and idiomatic (`sort_binding` is `choice(param = type, type)`; 106 `List[String]`, 51 `Cell[State]`, 20 `Option[String]` in real sources), so the mapping declaration uses the positional form.

BRANCH: `wi-k63zv-document-format-samples`, docs and samples only, nothing merged.

