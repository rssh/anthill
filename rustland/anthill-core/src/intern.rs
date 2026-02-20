/// Symbol interner — maps strings to compact `Symbol(u32)` handles.
///
/// Every unique string gets interned once; subsequent calls to `intern`
/// return the same `Symbol`. This is the basis for cheap name comparison
/// throughout the IR.

use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Symbol(u32);

impl Symbol {
    pub fn index(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Default)]
pub struct Interner {
    map: HashMap<String, Symbol>,
    vec: Vec<String>,
}

impl Interner {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn intern(&mut self, s: &str) -> Symbol {
        if let Some(&sym) = self.map.get(s) {
            return sym;
        }
        let sym = Symbol(self.vec.len() as u32);
        self.vec.push(s.to_owned());
        self.map.insert(s.to_owned(), sym);
        sym
    }

    pub fn resolve(&self, sym: Symbol) -> &str {
        &self.vec[sym.0 as usize]
    }
}
