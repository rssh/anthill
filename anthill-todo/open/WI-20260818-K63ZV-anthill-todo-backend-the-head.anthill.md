```anthill
fact WorkItem(id: "WI-20260818-K63ZV-anthill-todo-backend-the-head", created: "2026-08-18T15:32:43Z", acceptance: [ToolPasses(tool: "cargo-test"), ToolPasses(tool: "scaland-sbt-test")], depends_on: some(value: ["WI-1120"]), status: Open)

fact Tag(workitem: "WI-20260818-K63ZV-anthill-todo-backend-the-head", name: "wi437")

fact Feedback(workitem: "WI-20260818-K63ZV-anthill-todo-backend-the-head", author: "claude", at: "2026-08-18T15:37:52Z")

fact Feedback(workitem: "WI-20260818-K63ZV-anthill-todo-backend-the-head", author: "claude", at: "2026-08-18T15:47:13Z")
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

