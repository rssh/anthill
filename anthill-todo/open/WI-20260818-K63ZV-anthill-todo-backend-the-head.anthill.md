```anthill
fact WorkItem(id: "WI-20260818-K63ZV-anthill-todo-backend-the-head", created: "2026-08-18T15:32:43Z", acceptance: [ToolPasses(tool: "cargo-test"), ToolPasses(tool: "scaland-sbt-test")], depends_on: some(value: ["WI-1120"]), status: Open)

fact Tag(workitem: "WI-20260818-K63ZV-anthill-todo-backend-the-head", name: "wi437")

fact Feedback(workitem: "WI-20260818-K63ZV-anthill-todo-backend-the-head", author: "claude", at: "2026-08-18T15:37:52Z")

fact Feedback(workitem: "WI-20260818-K63ZV-anthill-todo-backend-the-head", author: "claude", at: "2026-08-18T15:47:13Z")

fact Feedback(workitem: "WI-20260818-K63ZV-anthill-todo-backend-the-head", author: "claude", at: "2026-08-19T07:42:14Z")
```

## description

anthill-todo backend: THE HEAD SHOULD BE A FIELD MAP, NOT A FACT APPLICATION. WI-1120 moved an item's prose out of the head and left the structured half spelled as it always was — `fact WorkItem(id: …, created: …, …)` on ONE PHYSICAL LINE, plus a `fact Tag`/`fact Feedback` row per satellite. That is the wrong shape for what the file now is, and the measurements on this tracker say so: 1119 heads, MEAN 278 characters on a single line, longest 2062 (WI-1115); 3354 occurrences of `context: none` / `generates: none` / `requires_capability: none`, fields WI-1120 already measured as always-none; and 1459 satellite rows (1173 Feedback, 286 Tag) each repeating `workitem:` — a key the FILE already is.

THE PROPOSED HEAD, and the claim is that it says strictly less while meaning the same:

  id: WI-1121
  created: 2026-08-17T08:43:54Z
  status: Claimed(agent: "claude", since: "2026-08-18T05:22:11Z")
  acceptance: [ToolPasses(tool: "cargo-test")]
  depends_on: [WI-1114]
  tags: [wi437]

THREE SEPARATE REDUCTIONS, and they should be judged separately because their arguments differ:

(1) THE FUNCTOR IS IMPLIED BY THE TREE. The file is an item, in an item tree, under a status directory; `fact WorkItem(` is the most redundant token in it. The mapping already names the functor (`Chapter(functor: WorkItem, …)`), so the reader has it without the file saying it.

(2) ONE FIELD PER LINE, AND THIS IS THE REAL PRIZE — it is about CONFLICT-FREEDOM, not tidiness, which is WI-437's whole reason for existing. Today a status change rewrites a 278-character line, so two agents touching DIFFERENT fields of one item conflict in git; field-per-line makes `claim` a one-line diff and lets those two merge cleanly. File-per-item (WI-1114) got conflict-freedom BETWEEN items; this is the same win WITHIN one. It also makes the head genuinely reviewable in a PR, which a 2062-character line is not.

(3) A SATELLITE'S KEY IS THE FILE. `fact Tag(workitem: "WI-1121", name: "wi437")` reduces to a name, and N names are a list — so tags become one `tags:` field (or a markdown list, see below) and Feedback's `workitem:` disappears the same way. 1459 repetitions of a key the path already carries.

AND AN ABSENT FIELD IS SIMPLY ABSENT, which retires the 3354 always-none writes. That is not a new rule — it is exactly what WI-1120 already does for a chapter-bearing field, applied to the rest of the head.

WHAT MUST NOT BE LOST, because it is the thing §5.3 chose the fenced anthill block FOR: the head is anthill syntax, the loader CHECKS it against the declared domain, and WI-928 found 921 mismatches the first time that check ran. THIS IS NOT A MOVE TO YAML. Field VALUES stay anthill terms — `status: Claimed(agent: …, since: …)` needs no encoding and `acceptance: [ToolPasses(…)]` stays a term list. What is removed is only the APPLICATION SHELL around them. The reader synthesizes the fact from the field map before the loader sees it, which is the SAME splice WI-1120 already performs for chapters (see §5.5: the splice produces the parse IR a plain `fact` file would have) — so this extends a mechanism rather than adding one, and the equivalence test is the same: what reaches the loader must be indistinguishable from the fact syntax it replaces.

TAGS AS A MARKDOWN LIST is a THIRD mapping kind and should be recognised as one rather than bent into an existing one. `Chapter` is a prose field of the item's own fact; `ChapterGroup` is a repeated satellite WITH prose. A tag is a repeated satellite with NO prose whose whole content is one scalar — so it is neither, and forcing it into `ChapterGroup` would give every tag an empty chapter. Whether it lives as a head field (`tags: [wi437]`) or as a markdown list under `## tags` is the open question: the head field is denser and diffs the same as any other list; the markdown list is what a reader of the rendered page would expect to see, and is the only form GitHub shows without opening the fence. DECIDE IT BY LOOKING AT A RENDERED PAGE, not in the abstract.

COST, STATED HONESTLY: a THIRD full-tree rewrite of ~1119 files, after WI-1118's and WI-1120's. §11 already accepted that arithmetic once (`two mechanical diffs instead of one, against getting the conflict benefit two tickets earlier`) and the machinery is now well rehearsed — `migrate --to document` exists, is idempotent, and was driven twice on copies before it touched the live tree. The conversion is again a pure reformat with no data change, so a before/after per-functor row count is a complete correctness check.

DRIVE THE CAPABILITY, do not assert that it loads: round-trip a real item — add / feedback / tag / claim / update --description — through the field-map head, and assert the reparsed FACTS equal the pre-write facts. Then the test that justifies the whole ticket: take one item, change its status in one checkout and its description in another, and assert git merges the two without conflict — which fails today, because both rewrite the same physical line. CONTROL: the round-trip test passes either way against an unmodified store and measures only the encoding; the merge test is the one that fails when the head is a single line.

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

