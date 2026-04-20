//! Integration tests for WI-050 effect handlers — the M5 slice that
//! registers handlers for `anthill.prelude.Console.ConsoleOutput` and
//! `anthill.prelude.Console.ConsoleInput`, and routes `Console.print`,
//! `Console.println`, `Console.read_line` through them.
//!
//! Real stdio is avoided here (tests shouldn't clobber stdout); we inject
//! a buffered output sink and a scripted input queue, then assert on the
//! captured traffic.

mod common;

use anthill_core::eval::Value;

use common::{buffered_console_output, interp_for, scripted_console_input};

#[test]
fn m5_println_captured_to_buffer() {
    let src = r#"
namespace test.m5_print
  import anthill.prelude.{Console, Unit, String}
  import anthill.prelude.Console.{console, print, println}

  operation greet(c: Console) -> Unit =
    println(c, "hello")
end
"#;
    let mut interp = interp_for(src);
    let (buf, handler) = buffered_console_output();
    interp.register_effect_handler("anthill.prelude.Console.ConsoleOutput", handler)
        .expect("register output handler");

    // Pass the Console entity as the argument.
    let console_sym = interp.kb().try_resolve_symbol("anthill.prelude.Console.console")
        .expect("Console.console symbol");
    let console_val = Value::Entity { functor: console_sym, pos: Vec::new(), named: Vec::new() };

    interp.call("test.m5_print.greet", &[console_val]).expect("greet runs");
    assert_eq!(buf.borrow().as_str(), "hello\n");
}

#[test]
fn m5_print_no_newline() {
    let src = r#"
namespace test.m5_print2
  import anthill.prelude.{Console, Unit, String}
  import anthill.prelude.Console.{console, print}

  operation speak(c: Console) -> Unit = print(c, "hi")
end
"#;
    let mut interp = interp_for(src);
    let (buf, handler) = buffered_console_output();
    interp.register_effect_handler("anthill.prelude.Console.ConsoleOutput", handler).unwrap();
    let console_sym = interp.kb().try_resolve_symbol("anthill.prelude.Console.console").unwrap();
    let console_val = Value::Entity { functor: console_sym, pos: Vec::new(), named: Vec::new() };
    interp.call("test.m5_print2.speak", &[console_val]).expect("speak runs");
    assert_eq!(buf.borrow().as_str(), "hi");
}

#[test]
fn m5_read_line_returns_scripted_input() {
    let src = r#"
namespace test.m5_read
  import anthill.prelude.{Console, Unit, String}
  import anthill.prelude.Console.{console, read_line}

  operation ask(c: Console) -> String = read_line(c)
end
"#;
    let mut interp = interp_for(src);
    let (queue, handler) = scripted_console_input(&["ruslan", "ignored_second_line"]);
    interp.register_effect_handler("anthill.prelude.Console.ConsoleInput", handler).unwrap();
    let console_sym = interp.kb().try_resolve_symbol("anthill.prelude.Console.console").unwrap();
    let console_val = Value::Entity { functor: console_sym, pos: Vec::new(), named: Vec::new() };

    let got = interp.call("test.m5_read.ask", &[console_val]).expect("ask runs");
    assert_eq!(got.as_str(), Some("ruslan"));
    // One line remains in the queue — the second scripted line.
    assert_eq!(queue.borrow().len(), 1);
}

#[test]
fn m5_read_then_print_roundtrip() {
    let src = r#"
namespace test.m5_round
  import anthill.prelude.{Console, Unit, String}
  import anthill.prelude.Console.{console, println, read_line}

  operation echo(c: Console) -> Unit =
    let line = read_line(c)
    println(c, line)
end
"#;
    let mut interp = interp_for(src);
    let (buf, out_h) = buffered_console_output();
    let (_q, in_h) = scripted_console_input(&["alice"]);
    interp.register_effect_handler("anthill.prelude.Console.ConsoleOutput", out_h).unwrap();
    interp.register_effect_handler("anthill.prelude.Console.ConsoleInput", in_h).unwrap();
    let console_sym = interp.kb().try_resolve_symbol("anthill.prelude.Console.console").unwrap();
    let console_val = Value::Entity { functor: console_sym, pos: Vec::new(), named: Vec::new() };
    interp.call("test.m5_round.echo", &[console_val]).expect("echo runs");
    assert_eq!(buf.borrow().as_str(), "alice\n");
}

#[test]
fn m5_unhandled_effect_errors_cleanly() {
    // No handler registered -> invoking Console.print should surface a
    // clean Internal error, not panic. This is the fallback if a user
    // forgets to register a handler (or registered only one side).
    let src = r#"
namespace test.m5_unhandled
  import anthill.prelude.{Console, Unit, String}
  import anthill.prelude.Console.{console, println}

  operation speak(c: Console) -> Unit = println(c, "x")
end
"#;
    let mut interp = interp_for(src);
    // Deliberately no register_effect_handler call.
    let console_sym = interp.kb().try_resolve_symbol("anthill.prelude.Console.console").unwrap();
    let console_val = Value::Entity { functor: console_sym, pos: Vec::new(), named: Vec::new() };
    let err = interp.call("test.m5_unhandled.speak", &[console_val]).unwrap_err();
    assert!(
        matches!(&err, anthill_core::eval::EvalError::Internal(msg)
            if msg.contains("no handler") && msg.contains("ConsoleOutput")),
        "expected 'no handler' for ConsoleOutput, got {err:?}",
    );
}

#[test]
fn m5_handler_replacement_works_mid_run() {
    // Register a handler, run, swap it, run again — verifies the
    // take/register round-trip actually replaces and doesn't just
    // stack underneath.
    let src = r#"
namespace test.m5_swap
  import anthill.prelude.{Console, Unit, String}
  import anthill.prelude.Console.{console, println}

  operation speak(c: Console, s: String) -> Unit = println(c, s)
end
"#;
    let mut interp = interp_for(src);
    let (buf1, h1) = buffered_console_output();
    interp.register_effect_handler("anthill.prelude.Console.ConsoleOutput", h1).unwrap();
    let console_sym = interp.kb().try_resolve_symbol("anthill.prelude.Console.console").unwrap();
    let console_val = Value::Entity { functor: console_sym, pos: Vec::new(), named: Vec::new() };
    interp.call("test.m5_swap.speak", &[console_val.clone(), Value::Str("first".into())]).unwrap();
    assert_eq!(buf1.borrow().as_str(), "first\n");

    let (buf2, h2) = buffered_console_output();
    interp.register_effect_handler("anthill.prelude.Console.ConsoleOutput", h2).unwrap();
    interp.call("test.m5_swap.speak", &[console_val, Value::Str("second".into())]).unwrap();
    assert_eq!(buf2.borrow().as_str(), "second\n", "new handler captured");
    // The original buffer is untouched by the second call.
    assert_eq!(buf1.borrow().as_str(), "first\n", "old buffer unchanged");
}
