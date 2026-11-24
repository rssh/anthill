## Attributes

- id: WI-20261124-YYR1P-a-long-argv-overflows-the
- created: 2026-11-24T07:39:44Z

- status: Open
- status_agent: user
- status_at: 2026-11-24T07:39:44Z

- acceptance: cargo-test

## Description

A long argv overflows the stack before main reads it: main(args) = 0 aborts at 3500 words, regressed since 2ab7ca823
WHO NEEDS IT. A program run by anthill_stl::runner (anthill run, or an embedder through runner::build_args_value and Interpreter::call) that takes file paths as arguments gets them from a shell glob; a few thousand is ordinary. anthill-traces' check command takes any number of trace paths and aborts the same way (with its own bundle, `--version` and 2000 more words exits 0, 3500 aborts).
WHAT HAPPENS. MEASURED 2026-11-24, debug builds, macOS, the main thread's default stack. The program
  namespace probe ... sort Main requires anthill.cli.Main  operation main(args: List[String]) -> Int64 = 0  end end
run as `anthill run probe.anthill -- w0 w1 … w(n-1)`:
- on d5772d741 (the CLI rebuilt at it): n = 2000 exits 0; n = 3500 and n = 5000 abort, "thread 'main' has overflowed its stack", exit 134;
- on 2ab7ca823 (the CLI built 2026-11-23): n = 5000 exits 0; n = 20000 aborts the same way.
Three more mains behave the same on each build — pass at 2000 and abort at 3500 on d5772d741, pass at 5000 on 2ab7ca823: one matching the head (`match args case cons(_, _) -> 0 case nil() -> 0`), one matching a literal head (`case cons("check", _) -> 1 case _ -> 0`), and one walking the list by a tail call (`count(xs, n) = match xs case nil() -> n case cons(_, r) -> count(r, n + 1)`). The first never reads an element, so the depth is in building, passing or dropping the argument list — a cons chain of nested Value::Entity — not in the program.
THE RANGE, not bisected: 2ab7ca823..d5772d741 is 27 commits, 12 of them not `todo:`; of rustland/anthill-core/src/eval, mod.rs and builtins.rs changed in it.
WHY IT MATTERS. An abort is no error message and no exit code the program chose: a caller cannot tell it from any other crash. The bound is the stack, so it moves with every frame added on the way.
WHAT IS ASKED. (1) The regression found and removed. (2) The argument list built, lowered, passed and dropped without recursion over its length, so that the number of arguments is bounded by the OS, not by the stack — e.g. an iterative lowering and drop of a cons chain.
DONE WHEN. (1) The four mains above exit 0 with 100 000 words in a debug build, the walk answering through its result; (2) a row driving runner::build_args_value and Interpreter::call from outside the crate with 100 000 strings, the walk answering 100 000; (3) the control: the same rows at 10 words.

