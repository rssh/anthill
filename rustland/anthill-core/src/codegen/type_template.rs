//! The grammar of a `TypeMapping` `host_type`, shared by the generators that write
//! one: host text, with `$Name` standing for the mapped sort's type parameter `Name`
//! (`std::map<$K, $V>`, `Result<$T, $E>`).

/// One piece of a parsed host-type template.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeTemplatePart {
    Text(String),
    Param(String),
}

/// Parse a host-type template: `$` followed by an identifier names a type parameter,
/// everything else is host text. `Err` says what is wrong, as a clause the caller
/// completes ("has a `$` at byte 4 that names no type parameter").
pub fn parse_type_template(src: &str) -> Result<Vec<TypeTemplatePart>, String> {
    let mut parts = Vec::new();
    let mut text = String::new();
    let mut chars = src.char_indices().peekable();
    while let Some((at, c)) = chars.next() {
        if c != '$' {
            text.push(c);
            continue;
        }
        let mut name = String::new();
        while let Some(&(_, n)) = chars.peek() {
            let fits = if name.is_empty() {
                n.is_ascii_alphabetic() || n == '_'
            } else {
                n.is_ascii_alphanumeric() || n == '_'
            };
            if !fits {
                break;
            }
            name.push(n);
            chars.next();
        }
        if name.is_empty() {
            return Err(format!(
                "has a `$` at byte {at} that names no type parameter"
            ));
        }
        if !text.is_empty() {
            parts.push(TypeTemplatePart::Text(std::mem::take(&mut text)));
        }
        parts.push(TypeTemplatePart::Param(name));
    }
    if !text.is_empty() {
        parts.push(TypeTemplatePart::Text(text));
    }
    Ok(parts)
}

/// The name of the host template `template` applies, when it is exactly that name
/// applied to `params` in their order (`std::vector<$T>` over `[T]` is `std::vector`):
/// what stands for the sort where it is passed unapplied, to a higher-kinded parameter.
/// `None` for any other shape — `Result<$T, $E>` over `[E, T]` reorders, so the name
/// `Result` would take the arguments in the wrong order.
pub fn bare_template_name(template: &str, params: &[String]) -> Option<String> {
    if params.is_empty() {
        return None;
    }
    let compact: String = template.chars().filter(|c| !c.is_whitespace()).collect();
    let (name, rest) = compact.split_once('<')?;
    let applied: Vec<String> = params.iter().map(|p| format!("${p}")).collect();
    (rest == format!("{}>", applied.join(",")) && !name.is_empty()).then(|| name.to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_template_parses_into_text_and_parameters() {
        assert_eq!(
            parse_type_template("std::map<$K, $V>").unwrap(),
            vec![
                TypeTemplatePart::Text("std::map<".into()),
                TypeTemplatePart::Param("K".into()),
                TypeTemplatePart::Text(", ".into()),
                TypeTemplatePart::Param("V".into()),
                TypeTemplatePart::Text(">".into()),
            ]
        );
        assert!(parse_type_template("box<$>").is_err());
        assert!(parse_type_template("box<$1>").is_err());
    }

    #[test]
    fn the_bare_name_is_the_template_applied_in_declaration_order() {
        let params = |ps: &[&str]| ps.iter().map(|p| p.to_string()).collect::<Vec<_>>();
        assert_eq!(
            bare_template_name("std::optional<$T>", &params(&["T"])).as_deref(),
            Some("std::optional")
        );
        assert_eq!(
            bare_template_name("std::map<$K, $V>", &params(&["K", "V"])).as_deref(),
            Some("std::map")
        );
        assert_eq!(
            bare_template_name("Result<$T, $E>", &params(&["E", "T"])),
            None
        );
        assert_eq!(bare_template_name("int64_t", &params(&[])), None);
        assert_eq!(bare_template_name("const $T *", &params(&["T"])), None);
    }
}
