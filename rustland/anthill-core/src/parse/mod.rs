/// Parser — tree-sitter CST → typed parse IR.
///
/// Entry point: `parse(source) -> Result<ParsedFile, Vec<ParseError>>`

pub mod ir;
pub mod error;
mod convert;

use ir::ParsedFile;
use error::ParseError;

/// Parse an `.anthill` source string into a typed parse IR.
pub fn parse(source: &str) -> Result<ParsedFile, Vec<ParseError>> {
    let mut parser = tree_sitter::Parser::new();
    parser
        .set_language(&tree_sitter_anthill::LANGUAGE.into())
        .map_err(|e| vec![ParseError::new(format!("failed to load grammar: {e}"), crate::span::Span::default())])?;

    let tree = parser
        .parse(source, None)
        .ok_or_else(|| vec![ParseError::new("tree-sitter parse returned None", crate::span::Span::default())])?;

    let mut converter = convert::Converter::new(source);
    converter.convert_file(tree.root_node());

    if converter.errors.is_empty() {
        Ok(ParsedFile {
            items: converter.items,
            symbols: converter.symbols,
            terms: converter.terms,
        })
    } else {
        Err(converter.errors)
    }
}
