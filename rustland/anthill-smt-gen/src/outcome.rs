//! Parse Z3's textual outcome output (model / unsat-core) into
//! lightweight records the CLI can serialise into anthill facts.
//! WI-099, proposal 025.1 §Outcome layer.
//!
//! The full Z3 model grammar is rich; we only extract what's
//! load-bearing for `ProofCounterexample` / `ProofCore` facts:
//!   * model: variable_name → string-rendered value pairs
//!   * unsat-core: list of named-assertion identifiers
//!
//! The model parser is best-effort. The raw model text is preserved
//! verbatim so consumers can re-parse if they need finer detail.

/// Parsed outcome data extracted from a Z3 output stream. The fields
/// are populated only when the corresponding `:produce-*` option was
/// set on the input — otherwise they stay empty/None.
#[derive(Debug, Clone, Default)]
pub struct OutcomeData {
    /// First line of Z3 output: `unsat` | `sat` | `unknown` (or other).
    pub verdict: String,
    /// Raw model block (`(model ...)` or `((define-fun ...) ...)`),
    /// with surrounding whitespace trimmed. Empty when the run
    /// reports `unsat` / no `(get-model)` appended.
    pub model_text: String,
    /// Best-effort `name → value-text` extraction from the model.
    /// Only `define-fun <name> () <sort> <value>` shapes are picked
    /// up — first-order constants. Higher-order/uninterpreted-fn
    /// entries fall through and stay raw in `model_text`.
    pub variable_assignments: Vec<(String, String)>,
    /// Names from `(get-unsat-core)` output. Empty when
    /// `:produce-unsat-cores` was off or the run reported `sat`.
    pub unsat_core: Vec<String>,
    /// Raw `(get-interpolants)` block, when present. Reserved.
    pub interpolants_text: String,
}

/// Parse a Z3 stdout dump into an `OutcomeData`. Lossy by design —
/// non-recognised output is preserved in the relevant raw_* field.
pub fn parse_z3_output(stdout: &str) -> OutcomeData {
    let mut data = OutcomeData::default();
    let trimmed = stdout.trim_start();

    // First non-blank line is the verdict.
    if let Some(verdict_line) = trimmed.lines().next() {
        data.verdict = verdict_line.trim().to_string();
    }

    // Walk top-level S-expression blocks after the verdict line.
    // We split by paren-balance, not regex — Z3's model output is
    // newline-formatted but the grammar is paren-driven.
    let after_verdict = trimmed.find('\n').map(|i| &trimmed[i + 1..]).unwrap_or("");
    let blocks = split_top_level_sexprs(after_verdict);

    for block in blocks {
        let trimmed = block.trim();
        // Model: any block containing `define-fun`. Covers both
        // `(model (define-fun ...))` and bare `((define-fun ...))`,
        // tolerant of whitespace between parens.
        if trimmed.contains("define-fun") {
            data.model_text = trimmed.to_string();
            data.variable_assignments = extract_define_funs(trimmed);
        } else if looks_like_unsat_core(trimmed) {
            data.unsat_core = extract_unsat_core(trimmed);
        }
    }
    data
}

/// Split a string into top-level parenthesised S-expressions. Anything
/// outside parens (whitespace) is dropped. Quoted-string content is
/// treated as opaque so `"a)b"` doesn't break paren counting.
fn split_top_level_sexprs(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth: i32 = 0;
    let mut current = String::new();
    let mut in_string = false;
    let mut prev = '\0';

    for c in s.chars() {
        match c {
            '"' if prev != '\\' => {
                in_string = !in_string;
                if depth > 0 { current.push(c); }
            }
            '(' if !in_string => {
                if depth == 0 { current.clear(); }
                depth += 1;
                current.push(c);
            }
            ')' if !in_string => {
                depth -= 1;
                current.push(c);
                if depth == 0 {
                    out.push(std::mem::take(&mut current));
                }
            }
            _ if depth > 0 => current.push(c),
            _ => {}
        }
        prev = c;
    }
    out
}

/// Heuristic: an unsat-core block is a flat paren-list of identifiers,
/// e.g. `(a1 a2 a3)`. Not nested. Distinguishes from `(model ...)`
/// which starts with the keyword.
fn looks_like_unsat_core(s: &str) -> bool {
    let inner = match s.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
        Some(i) => i,
        None => return false,
    };
    !inner.contains('(') && !inner.contains("define-fun")
        && !inner.contains("model")
}

fn extract_unsat_core(s: &str) -> Vec<String> {
    s.trim_start_matches('(')
        .trim_end_matches(')')
        .split_whitespace()
        .map(|t| t.to_string())
        .collect()
}

/// Extract `(define-fun <name> () <sort> <value>)` constants from a
/// model text. Skips anything more complex (lambdas,
/// uninterpreted-fn entries, datatype constructors).
fn extract_define_funs(model: &str) -> Vec<(String, String)> {
    const MARKER: &str = "(define-fun ";
    let mut out = Vec::new();
    let mut rest = model;
    while let Some(idx) = rest.find(MARKER) {
        // Advance past the marker once; reusing the find result avoids
        // an O(n²) rescan from position 0 on every iteration.
        let after = &rest[idx + MARKER.len()..];
        let name_end = after.find(char::is_whitespace).unwrap_or(after.len());
        let name = after[..name_end].to_string();
        let after_name = after[name_end..].trim_start();
        // Nullary signature `()`. Anything else (lambda body) — skip
        // and let the next iteration find the next marker.
        if !after_name.starts_with("()") {
            rest = after;
            continue;
        }
        let after_arity = after_name[2..].trim_start();
        let sort_end = after_arity.find(char::is_whitespace).unwrap_or(after_arity.len());
        let after_sort = after_arity[sort_end..].trim_start();
        let value = take_balanced_value(after_sort);
        if !name.is_empty() && !value.is_empty() {
            out.push((name, value.trim().to_string()));
        }
        rest = after;
    }
    out
}

/// Read characters up to the close-paren that matches the *enclosing*
/// `(define-fun ...)`. We balance parens locally; when depth goes
/// from 0 → -1, that's the closing paren of the outer form.
fn take_balanced_value(s: &str) -> String {
    let mut out = String::new();
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut prev = '\0';
    for c in s.chars() {
        match c {
            '"' if prev != '\\' => {
                in_string = !in_string;
                out.push(c);
            }
            '(' if !in_string => { depth += 1; out.push(c); }
            ')' if !in_string => {
                if depth == 0 { break; }
                depth -= 1;
                out.push(c);
            }
            _ => out.push(c),
        }
        prev = c;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_unsat_only() {
        let d = parse_z3_output("unsat\n");
        assert_eq!(d.verdict, "unsat");
        assert!(d.model_text.is_empty());
        assert!(d.unsat_core.is_empty());
    }

    #[test]
    fn parse_sat_with_model() {
        let z3 = "sat\n(\n  (define-fun x () Int 5)\n  (define-fun y () Bool true)\n)\n";
        let d = parse_z3_output(z3);
        assert_eq!(d.verdict, "sat");
        assert!(d.model_text.contains("define-fun x"));
        assert_eq!(d.variable_assignments.len(), 2);
        assert_eq!(d.variable_assignments[0], ("x".into(), "5".into()));
        assert_eq!(d.variable_assignments[1], ("y".into(), "true".into()));
    }

    #[test]
    fn parse_model_keyword_form() {
        let z3 = "sat\n(model\n  (define-fun x () Int 42)\n)\n";
        let d = parse_z3_output(z3);
        assert_eq!(d.verdict, "sat");
        assert_eq!(d.variable_assignments.len(), 1);
        assert_eq!(d.variable_assignments[0], ("x".into(), "42".into()));
    }

    #[test]
    fn parse_unsat_with_core() {
        let z3 = "unsat\n(a1 a2 a3)\n";
        let d = parse_z3_output(z3);
        assert_eq!(d.verdict, "unsat");
        assert_eq!(d.unsat_core, vec!["a1".to_string(), "a2".into(), "a3".into()]);
    }

    #[test]
    fn parse_unknown() {
        let d = parse_z3_output("unknown\n");
        assert_eq!(d.verdict, "unknown");
        assert!(d.model_text.is_empty());
        assert!(d.unsat_core.is_empty());
    }

    #[test]
    fn parse_sat_with_model_and_negative_value() {
        let z3 = "sat\n(\n  (define-fun d_next () Real (- 1.5))\n)\n";
        let d = parse_z3_output(z3);
        assert_eq!(d.verdict, "sat");
        assert_eq!(d.variable_assignments.len(), 1);
        assert_eq!(d.variable_assignments[0].0, "d_next");
        assert!(d.variable_assignments[0].1.contains("- 1.5"));
    }

    #[test]
    fn malformed_input_doesnt_panic() {
        let _ = parse_z3_output("");
        let _ = parse_z3_output("(((((");
        let _ = parse_z3_output("not even a verdict");
    }
}
