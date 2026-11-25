## Attributes

- id: WI-20261125-D3PDK-anthill-cli-help-a-parameter
- created: 2026-11-25T11:43:07Z

- status: Open
- status_agent: user
- status_at: 2026-11-25T11:43:07Z

- acceptance: cargo-test

## Description

anthill.cli help: a parameter name longer than NAME_COLUMN runs into its description, with no space between
WHO NEEDS IT. Any program whose commands have a parameter of 14 characters or more, `--` counted: anthill-traces' check has --allow-undecided (17).
WHAT HAPPENS. MEASURED 2026-11-25 with anthill-traces built on 8ed4765f3: check's usage prints the row "  --allow-undecidedReport an undecided clause or comparison as a warning", the name and its description run together. Read from code (6e415e6ef): render_flags and render_args pad the name with padRight(…, NAME_COLUMN) (stdlib/anthill/cli/help.anthill:89, :103), NAME_COLUMN is 15 (:113), and padRight leaves a longer string unchanged, so nothing separates it from the description. The comment above the const (:107–112) says a longer name "costs that one row its alignment and nothing else"; it costs the separation too.
WHY IT MATTERS. The row reads as one word, and the comment's account of the case is wrong, so the next reader trusts it.
WHAT IS ASKED. A row's name and description always separated, whatever the name's length: the column taken from the command's longest rendered name plus two spaces, so every row of a command stays aligned, or at the least two spaces after a name past the column. Which is anthill's choice; the comment then says what the code does.
DONE WHEN. A row test: a command with a flag of 17 characters beside short ones renders each description separated from its name (and, if the column is computed, aligned with the others); a command whose names fit the column renders as today; anthill-todo's and anthill-traces' usage blocks show no row run together.

