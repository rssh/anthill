//! Integration test for WI-049: `stdlib/anthill/prelude/console.anthill`.
//!
//! Verifies the Console sort, its single entity, the ConsoleOutput /
//! ConsoleInput effect kinds, and the three operations (print, println,
//! read_line) all load and resolve after stdlib load. Handler wiring
//! (actually driving stdio) is WI-050 (M5 effect handlers).


use crate::common::load_kb_with;

#[test]
fn console_stdlib_symbols_resolve() {
    let kb = load_kb_with("namespace test.console_check end\n");

    for qname in [
        "anthill.prelude.Console",
        "anthill.prelude.Console.console",
        "anthill.prelude.Console.ConsoleOutput",
        "anthill.prelude.Console.ConsoleInput",
        "anthill.prelude.Console.print",
        "anthill.prelude.Console.println",
        "anthill.prelude.Console.read_line",
    ] {
        assert!(
            kb.try_resolve_symbol(qname).is_some(),
            "expected symbol `{qname}` to resolve after stdlib load",
        );
    }
}
