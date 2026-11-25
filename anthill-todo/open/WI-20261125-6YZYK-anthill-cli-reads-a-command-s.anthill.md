## Attributes

- id: WI-20261125-6YZYK-anthill-cli-reads-a-command-s
- created: 2026-11-25T11:43:03Z

- status: Open
- status_agent: user
- status_at: 2026-11-25T11:43:03Z

- acceptance: cargo-test

## Description

anthill.cli reads a command's --help as an unknown flag: asking a command for its usage is a usage error
WHO NEEDS IT. Every program built on anthill.cli, and its users: `<program> <command> --help` is the usual first try for a command's usage. anthill-todo and anthill-traces are two such programs.
WHAT HAPPENS. MEASURED 2026-11-25: `anthill-todo list --help` prints "anthill-todo: list: unknown flag '--help'" and then the usage, and `show --help` the same for show (the installed anthill-todo, 13d71922). anthill-traces built on 8ed4765f3: `check --help` prints "anthill-traces check: unknown flag '--help'" and the usage, and exits 2. -h is worse: it does not begin with --, so it is read as a positional value. `anthill-todo show -h` answers "no work item matches '-h'", and anthill-traces' `check -h` takes -h for a trace path. Read from code (6e415e6ef): the parser looks a flag up among the command's declared parameters and answers unknown_flag where none matches (stdlib/anthill/cli/parse.anthill:67), so --help after a command is refused like a misspelt flag, and any token not led by -- is a positional (parse.anthill:58). Each program recognizes --help, -h and help only BEFORE a command, in its own bundle (rustland/anthill-todo/anthill/main.anthill:534; anthill-traces' bundle the same), and anthill-todo's host-served init handles its own (96be04f38).
WHY IT MATTERS. A request for help is reported as a mistake, to stderr, with exit 2. A script that asks a command for its usage sees a failure, and the message says the flag is wrong where the program knows exactly what was asked. Each program can patch it in its own dispatch, as anthill-todo did for init, but then each does, and differently.
WHAT IS ASKED. anthill.cli recognizes --help and -h among a command's arguments, and answers a help request distinct from a parse error (for example a ParseResult case carrying the command's spec), so that a program prints that command's usage to stdout and exits 0. How it meets a command that declares a parameter named help, and --help given as a flag's value, are anthill's to decide and say.
DONE WHEN. A parse of `list --help` and of `list -h` gives the help request for list's spec; anthill-todo `list --help` prints list's usage on stdout, nothing on stderr, and exits 0; a misspelt flag (`list --stauts`) is still unknown_flag, with its message and exit code as today; the two choices above have a row each.

