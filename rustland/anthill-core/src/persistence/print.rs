/// Term printer — converts terms back to `.anthill` text.
///
/// Generic over [`PrintView`] so it works against either a `KnowledgeBase` (a hash-consed
/// term, a value, an occurrence, read through [`TermView`]) or a `ParsedFile` (parse-IR).
/// The canonical printed form is the same in both cases — used by persistence-side retract
/// matching.
use crate::parse::desugar_target as dt;
use std::rc::Rc;

use crate::eval::value::Value;
use crate::intern::{is_positional_label_at, Symbol};
use crate::kb::node_occurrence::{Expr, NodeKind, NodeOccurrence, TypeNode};
use crate::kb::term::{Literal, Term, TermId, TermSource, Var};
use crate::kb::term_view::{type_child_view_item, TermView, ViewHead, ViewItem};
use crate::kb::KnowledgeBase;
use crate::parse::ir::ParsedFile;

/// A literal in `.anthill` SURFACE spelling — a quoted `String`, a `Float` that keeps
/// its decimal point, `true`/`false`.
///
/// Free rather than a `TermPrinter` method (which delegates here) because it reads no
/// `view`: a literal is already the whole term. The second caller is a DIAGNOSTIC —
/// `load::constant_in_goal_position_message` quotes the constant the author wrote
/// (WI-20260822-J38JE) — and the surface spelling is exactly what a diagnostic wants,
/// so the two share one renderer rather than growing a second copy that could print
/// `hello` where the source says `"hello"`.
pub fn write_literal(lit: &Literal, buf: &mut String) {
    match lit {
        Literal::Int(n) => {
            buf.push_str(&n.to_string());
        }
        Literal::BigInt(n) => {
            buf.push_str(&n.to_string());
        }
        // The IEEE specials have NO literal (`float_literal` is digits-dot-digits); the
        // language names them as the consts `Float.infinity` / `negativeInfinity` / `nan`
        // (spec §2.4), and that name is what prints (WI-20260907-VM9Q7). Every other
        // spelling was worse: Rust's `inf` reloads SILENTLY as an identifier, and the
        // `.0` fix-up below garbled it into `inf.0`.
        //
        // RELOAD-FAITHFUL since WI-20261001-KDMQS: the loader folds a const in a clause
        // data slot to its value, so a persisted `f(v: Float.infinity)` loads as the
        // Float. The reload scope must import `Float`, as it must import every other name
        // a store writes. The parse of that text keys as `Float.infinity` too
        // ([`TermPrinter::dotted_chain_name`]), so the file store can still retract it.
        Literal::Float(f) if f.is_nan() => buf.push_str("Float.nan"),
        Literal::Float(f) if f.is_infinite() => buf.push_str(if f.is_sign_positive() {
            "Float.infinity"
        } else {
            "Float.negativeInfinity"
        }),
        Literal::Float(f) => {
            let s = f.to_string();
            buf.push_str(&s);
            // Ensure there's a decimal point so it parses back as float
            if !s.contains('.') {
                buf.push_str(".0");
            }
        }
        Literal::String(s) => write_anthill_string(s, buf),
        Literal::Bool(b) => {
            buf.push_str(if *b { "true" } else { "false" });
        }
    }
}

/// Append `s` quoted with `.anthill`-syntax escapes (spec §2.4): `"`, `\`, `\n`, `\r`,
/// `\t` by name, and EVERY OTHER control character as `\u{…}`. Shared by `TermPrinter`
/// and any other code that needs to emit a string literal in canonical form; the
/// matching decoder is `parse::convert::decode_string_escapes`.
///
/// WHY CONTROL CHARACTERS ARE ESCAPED (WI-20260907-VM9Q7): they used to be written raw,
/// because the language had no escape that could spell one. That made a printed string
/// a carrier for live terminal sequences — `anthill query` over a fact holding ESC
/// emitted ESC — and a raw one is invisible in a file even where it is harmless. With
/// `\u{…}` in the grammar, the escaped text reads back as the same string.
pub fn write_anthill_string(s: &str, buf: &mut String) {
    use std::fmt::Write as _;
    buf.push('"');
    for ch in s.chars() {
        match ch {
            '"' => buf.push_str("\\\""),
            '\\' => buf.push_str("\\\\"),
            '\n' => buf.push_str("\\n"),
            '\r' => buf.push_str("\\r"),
            '\t' => buf.push_str("\\t"),
            c if c.is_control() => {
                write!(buf, "\\u{{{:x}}}", c as u32).expect("writing to a String cannot fail")
            }
            _ => buf.push(ch),
        }
    }
    buf.push('"');
}

/// WI-20261022-DRGCP — WHAT THE PRINTER READS: a term's head and its children, through a
/// view, whichever carrier holds them.
///
/// One walk over this trait prints everything [`TermPrinter`] prints as data or as a type —
/// a fact, a goal a diagnostic quotes, a query answer, a type an occurrence carries — so one
/// value prints one text on every carrier. The knowledge base reads [`ViewItem`]s through
/// [`TermView`], where a hash-consed term, a value a substitution rebuilt over one, and a
/// type or effect occurrence all read as the term twin (WI-342, WI-361, WI-425); the parse
/// side reads its own terms by id. Before, the term printer read `TermId`s alone, a type's
/// occurrence carrier had a hand-kept twin of its type writer, and a value had two more
/// writers: a precondition a call had put on an occurrence went to the TYPE renderer and was
/// quoted `flows_to(Untrusted, Public)` for `flows_to(Untrusted[], Public[])`, and a list in
/// it `cons(head: …)` where its term printed `[…]`.
///
/// The file store needs the two sides to agree: its retract key compares a parse-side print
/// of the text on disk with a knowledge-base print of the loaded fact. One walk over two
/// readers that give one term one head is what makes them agree.
///
/// A [`TermSource`], for the names: both sides name a symbol as they do for any reader.
pub trait PrintView: TermSource {
    /// What the walk holds. Owned, so a walk can keep a child past its parent (a list
    /// spine's elements).
    type Item: Clone;
    /// The item a hash-consed term is.
    fn term_item(&self, id: TermId) -> Self::Item;
    fn head(&self, item: &Self::Item) -> ViewHead;
    fn pos_arg(&self, item: &Self::Item, i: usize) -> Option<Self::Item>;
    fn named_arg(&self, item: &Self::Item, key: Symbol) -> Option<Self::Item>;
    /// The named keys, in the order the carrier holds them, which is the order printed.
    fn named_keys(&self, item: &Self::Item) -> Vec<Symbol>;
    /// The named child whose key's local name is `key` — the forms the walk reads (an
    /// arrow's `param`, a cons cell's `head`) by the name their declaration gives it.
    fn named_child(&self, item: &Self::Item, key: &str) -> Option<Self::Item>;
    /// Is the application `item`, headed by `sym`, a TYPE whatever slot it stands in —
    /// headed by a constructor's type face, or by a sort with no constructor, predicate or
    /// operation of its name (WI-20260902-JB6RS, kernel-language.md §4.4)? Such an
    /// application is written with the bracket, since its parenthesized spelling is refused.
    /// The knowledge base asks its kind table; the parse side, which has none, the face and
    /// the written bracket.
    fn heads_only_a_type(&self, item: &Self::Item, sym: Symbol) -> bool;
    /// Was the bare name `item` WRITTEN with an empty bracket, `Foo[]`? Only the parse side
    /// can say, and must: the knowledge base holds a constructor's type by its face, which
    /// [`TermPrinter::write_symbol_ref`] writes with the bracket, so the parse side's print of
    /// the text on disk has to write the bracket it read or the file store's key misses.
    fn written_bracket(&self, _item: &Self::Item) -> bool {
        false
    }
    /// Writes `item` when this side spells it with a writer of its own rather than the walk,
    /// answering whether it did: on the knowledge base an EXPRESSION or PATTERN occurrence,
    /// whose view is its reflect-term twin and not the source it was written as; on the
    /// parse side a parse-only form.
    fn own_spelling(printer: &TermPrinter<'_, Self>, item: &Self::Item, buf: &mut String) -> bool;
}

impl PrintView for KnowledgeBase {
    type Item = ViewItem<'static>;

    fn term_item(&self, id: TermId) -> Self::Item {
        ViewItem::Term(id)
    }

    fn head(&self, item: &Self::Item) -> ViewHead {
        item.head(self)
    }

    fn pos_arg(&self, item: &Self::Item, i: usize) -> Option<Self::Item> {
        item.pos_arg(self, i).map(owned_item)
    }

    fn named_arg(&self, item: &Self::Item, key: Symbol) -> Option<Self::Item> {
        item.named_arg(self, key).map(owned_item)
    }

    fn named_keys(&self, item: &Self::Item) -> Vec<Symbol> {
        item.named_keys(self)
    }

    fn named_child(&self, item: &Self::Item, key: &str) -> Option<Self::Item> {
        item.named_field(self, key).map(owned_item)
    }

    fn heads_only_a_type(&self, _item: &Self::Item, sym: Symbol) -> bool {
        self.is_type_value_head(sym)
    }

    /// An occurrence the walk does not spell ([`TermPrinter::write_own_occurrence`]), and an
    /// OPAQUE value — a closure, a stream, a cell — named by its kind, `<Closure>`: it has no
    /// surface, and the kind is what tells two of them apart in an answer.
    fn own_spelling(printer: &TermPrinter<'_, Self>, item: &Self::Item, buf: &mut String) -> bool {
        match item {
            ViewItem::Node(occ) | ViewItem::Owned(Value::Node(occ)) => {
                printer.write_own_occurrence(occ, buf)
            }
            ViewItem::Owned(v) if matches!(v.head(printer.view), ViewHead::Opaque) => {
                buf.push('<');
                buf.push_str(v.type_name());
                buf.push('>');
                true
            }
            _ => false,
        }
    }
}

/// A child read off a view holding nothing borrowed from its parent: a borrowed value is
/// cloned — an `Rc`, or a scalar — so the walk can keep the child once the parent is gone.
fn owned_item(item: ViewItem<'_>) -> ViewItem<'static> {
    match item {
        ViewItem::Term(t) => ViewItem::Term(t),
        ViewItem::Value(v) => ViewItem::Owned(v.clone()),
        ViewItem::Node(n) => ViewItem::Node(n),
        ViewItem::Owned(v) => ViewItem::Owned(v),
    }
}

impl PrintView for ParsedFile {
    type Item = TermId;

    fn term_item(&self, id: TermId) -> TermId {
        id
    }

    /// The heads `TermIdView` gives the knowledge base's terms, so one term has one head on
    /// both sides: a `Ref` and a nullary application alike (WI-20260902-CZJ2N).
    fn head(&self, id: &TermId) -> ViewHead {
        match self.terms.get(*id) {
            Term::Var(v) => ViewHead::Var(*v),
            Term::Const(lit) => ViewHead::Const(lit.clone()),
            Term::Fn {
                functor,
                pos_args,
                named_args,
            } => ViewHead::Functor {
                functor: *functor,
                pos_arity: pos_args.len(),
                named_arity: named_args.len(),
            },
            Term::Ref(s) => ViewHead::nullary(*s),
            Term::Ident(s) => ViewHead::Ident(*s),
            Term::Bottom => ViewHead::Bottom,
            // Written by `own_spelling`.
            Term::ParseAux(_) => ViewHead::Opaque,
        }
    }

    fn pos_arg(&self, id: &TermId, i: usize) -> Option<TermId> {
        match self.terms.get(*id) {
            Term::Fn { pos_args, .. } => pos_args.get(i).copied(),
            _ => None,
        }
    }

    fn named_arg(&self, id: &TermId, key: Symbol) -> Option<TermId> {
        match self.terms.get(*id) {
            Term::Fn { named_args, .. } => {
                named_args.iter().find(|(s, _)| *s == key).map(|(_, t)| *t)
            }
            _ => None,
        }
    }

    fn named_keys(&self, id: &TermId) -> Vec<Symbol> {
        match self.terms.get(*id) {
            Term::Fn { named_args, .. } => named_args.iter().map(|(s, _)| *s).collect(),
            _ => Vec::new(),
        }
    }

    fn named_child(&self, id: &TermId, key: &str) -> Option<TermId> {
        match self.terms.get(*id) {
            Term::Fn { named_args, .. } => named_args
                .iter()
                .find(|(s, _)| self.symbols.local_name(*s) == key)
                .map(|(_, t)| *t),
            _ => None,
        }
    }

    fn written_bracket(&self, id: &TermId) -> bool {
        self.terms.is_type_application(*id)
    }

    /// The parse side has no kind table, but it has the surface: an application WRITTEN
    /// with the bracket is a type (WI-20260902-JB6RS), and printing it with parentheses
    /// would give a spelling the loader refuses.
    fn heads_only_a_type(&self, id: &TermId, sym: Symbol) -> bool {
        sym.is_type_face() || self.terms.is_type_application(*id)
    }

    /// `Term::ParseAux` — parse-only; it reaches the printer only when it is invoked on a
    /// parse-side term (e.g. for an error message), the loader stripping it before any KB
    /// allocation. Its payload is printed in Debug form, so a diagnostic carries the
    /// annotation or type-argument text even though it is not surface syntax.
    fn own_spelling(printer: &TermPrinter<'_, Self>, id: &TermId, buf: &mut String) -> bool {
        use crate::parse::ir::ParseAux;
        let Term::ParseAux(aux) = printer.view.terms.get(*id) else {
            return false;
        };
        match aux.as_ref() {
            ParseAux::TypeExpr(te) => buf.push_str(&format!("<type-anno {:?}>", te)),
            ParseAux::EntryType(te) => buf.push_str(&format!("<type-entry {:?}>", te)),
            ParseAux::SortBindings(b) => buf.push_str(&format!("<type-args {:?}>", b)),
            ParseAux::ProofStmt(m) => buf.push_str(&format!("<proof-meta {:?}>", m)),
        }
        true
    }
}

/// Prints terms as `.anthill` source text.
pub struct TermPrinter<'a, V: PrintView + ?Sized> {
    view: &'a V,
    /// WI-1099 — WHICH QUESTION THIS PRINT ANSWERS. Two callers want different
    /// text from one term, and conflating them is why a reflect-built
    /// `ListLiteral` could not survive being written to disk:
    ///
    ///  - `false` (default) — THE CANONICAL SURFACE: the text a reader, a
    ///    diagnostic, or a query answer should show, and the file store's
    ///    content KEY. A key must be INVARIANT under the loader's lowering,
    ///    because `apply_retracts` compares a print of the on-disk PARSE term
    ///    against a print of the LOADED head, and §4.6 lowers `[…]` to the
    ///    `cons`/`nil` spine between them. So a flat `ListLiteral` and a ground
    ///    `cons` spine deliberately share `[…]` here: were they to differ, a
    ///    persisted list's retract would stop matching its own file text.
    ///  - `true` — RELOAD-FAITHFUL: text that loads back to THIS term. `[…]` is
    ///    position-dependent (§4.6: it stays flat only where a declared type
    ///    names a rival collection), so a flat `ListLiteral` must be written by
    ///    NAME, the one spelling that is never lowered (parse/ir.rs's
    ///    `collection_literals` mark, `kb::load::list_literal_lowering`).
    ///
    /// THE TWO CANNOT BE ONE PRINT, and no bit added to the printer would let it
    /// choose per term: the KB is hash-consed, so a `[1, 2]` the loader declined
    /// to lower in a `Set[T = Int64]` field and a written `ListLiteral(1, 2)` are
    /// the SAME `TermId`. The parse-time mark that separates them cannot be
    /// carried in (it survives only because parse terms are not deduped — the
    /// same reason `mark_type_application` lives there, WI-927).
    ///
    /// The retract key stays mark-BLIND and structural, which is what keeps the
    /// two modes compatible: a fact this mode writes as `ListLiteral(1, 2)` still
    /// keys as `[1, 2]` on both sides, so it is found and dropped.
    ///
    /// WHAT THIS MODE STILL DOES NOT MAKE FAITHFUL, stated because the name would
    /// otherwise over-promise. A ground `cons`/`nil` spine prints `[…]` in BOTH
    /// modes, and that is faithful everywhere except one position: MEASURED, a
    /// spine written into a slot declared `Set[T = Int64]` persists as `[1, 2]`
    /// and reloads as the flat `ListLiteral` (§4.6 declines to lower there). The
    /// remedy would be to print the spine as `cons(head: 1, tail: …)`, which is
    /// position-independent — and it is refused twice over: every persisted list
    /// in every store would become a cons chain, and the parse side of such a
    /// chain does not fold back to `[…]`, so the content key above would stop
    /// matching its own file text. Pre-existing, unchanged here, and NOT claimed.
    ///
    /// Governs the TERM writer only. `write_occurrence` (rule bodies) has its own
    /// `Expr::ListLit` arm and is not taught this mode, because no reload-faithful
    /// caller reaches it — a persisted fact is a term. Wire the two together
    /// before persisting a rule.
    ///
    /// THE CONTENT KEY IS NOT INJECTIVE, and this mode does not make it so — a
    /// review pass asked. Two facts under ONE functor, `held(ListLiteral(1, 2))`
    /// and `held([1, 2])`, key alike, and `apply_retracts` drops EVERY block
    /// matching a key (file_store.rs), so retracting either erases both lines
    /// while both are still live in the KB. MEASURED IDENTICALLY WITH THIS MODE
    /// AND WITHOUT IT (without it the two also persist as the same text, so the
    /// pair was indistinguishable on disk to begin with): the loss lives in the
    /// KEY, not in the print, and this mode only makes the two lines legible.
    /// Keying both sides reload-faithfully is refused for the reason under
    /// `write_term`'s short-name test — the parse side cannot produce that text.
    /// The path without the weakness is `IndexedFileStore`'s SPAN retract, which
    /// exists for this class of miss (WI-187); the content key is its fallback for
    /// facts with no source span.
    reload_faithful: bool,
    /// WI-20261022-DRGCP — A DIAGNOSTIC QUOTING WHAT ITS AUTHOR WROTE. A parameter
    /// reference is the loader's `var_ref(name: c)` wrapper (WI-552), and a type variable a
    /// body is checked under is a skolem `!m`; neither is a line anthill parses. Here the
    /// wrapper is written as the name it wraps and a rigid as `?m`, the spelling its
    /// declaration used — for a refusal that quotes a clause for its reader to match against
    /// the line they wrote, or to write as the declaration it asks for
    /// ([`TermPrinter::quoting_source`]). It replaced a pass that rebuilt the goal in that
    /// spelling before printing it, which read a hash-consed goal only, and left a goal on
    /// any other carrier quoting `var_ref[name = k]`.
    source_spelling: bool,
}

impl<'a> TermPrinter<'a, KnowledgeBase> {
    pub fn new(kb: &'a KnowledgeBase) -> Self {
        Self {
            view: kb,
            reload_faithful: false,
            source_spelling: false,
        }
    }

    /// A printer for a diagnostic that quotes a clause as its author wrote it — see
    /// [`TermPrinter::source_spelling`].
    pub fn quoting_source(kb: &'a KnowledgeBase) -> Self {
        Self {
            view: kb,
            reload_faithful: false,
            source_spelling: true,
        }
    }

    /// Print a rule-body-atom occurrence as `.anthill` text (WI-246). Mirrors
    /// `write_term` over the occurrence `Expr` substrate (rule bodies are now
    /// occurrences, not terms); embedded `TermId` fields (patterns, params)
    /// defer to `write_term`. Used by CLI rule/query display.
    pub fn print_occurrence(&self, occ: &Rc<NodeOccurrence>) -> String {
        let mut buf = String::new();
        self.write_occurrence(occ, &mut buf);
        buf
    }

    /// Render a stored rule as `head :- body` source-ish text (a fact prints
    /// as just its head). Diagnostic-quality, not persistence-canonical —
    /// used by the bodied-rule refusal messages (WI-770/WI-772) that must
    /// name the offending rule. A WI-348 value-carrier head (`Node`/`Entity`,
    /// not loader-producible for a bodied rule today) still names the rule
    /// rather than trading the diagnostic for `rule_head`'s carrier panic,
    /// which would misattribute the failure.
    pub fn print_rule(&self, rid: crate::kb::RuleId) -> String {
        // A head that is no term or occurrence is printed by `print_value` (WI-20261022-DRGCP)
        // where it was a placeholder, `f(…)`; no bodied rule's head is one today, so no row
        // tells the two apart.
        let head = match self.view.rule_head_value(rid) {
            Value::Node(occ) => self.print_occurrence(occ),
            other => self.print_value(other),
        };
        let body: Vec<String> = self
            .view
            .rule_body_nodes(rid)
            .iter()
            .map(|atom| self.print_occurrence(atom))
            .collect();
        if body.is_empty() {
            head
        } else {
            format!("{head} :- {}", body.join(", "))
        }
    }

    /// WI-318: render a Pattern-kind occurrence in surface form.
    /// Recurses into sub-patterns (Constructor.pos_args /
    /// Tuple.positional). WI-819: the occurrence's optional `type_ann` is
    /// rendered as `<pattern>: <type>` (the type is an Expr-kind occurrence),
    /// uniformly for every pattern shape. If a
    /// sub-occurrence isn't Pattern-kind (the reflection-meta-var case
    /// from term_pattern_as_expr_occ), delegate to `write_occurrence`
    /// so the term shape is rendered as data instead of the literal
    /// `<not-a-pattern>` placeholder.
    fn write_pattern(&self, occ: &Rc<NodeOccurrence>, buf: &mut String) {
        use crate::kb::node_occurrence::Pattern;
        let Some(pat) = occ.as_pattern() else {
            // Expr-kind (or RuleHead) child in a pattern slot — render
            // via the generic occurrence writer so the term shape
            // surfaces faithfully.
            return self.write_occurrence(occ, buf);
        };
        // WI-819: the `: T` annotation hangs on the OCCURRENCE, so every pattern
        // shape renders it the same way — `let (a, b): (Int64, String)` prints
        // like `let x: Int64`, which is the point of the single channel.
        let write_ann = |buf: &mut String| {
            if let Some(t) = occ.pattern_type_ann() {
                buf.push_str(": ");
                self.write_occurrence(t, buf);
            }
        };
        match pat {
            Pattern::Var { name } => buf.push_str(self.view.sym_name(*name)),
            Pattern::Wildcard => buf.push('_'),
            Pattern::Literal { value } => write_literal(value, buf),
            Pattern::Constructor {
                name,
                pos_args,
                named_args,
            } => {
                buf.push_str(self.view.sym_name(*name));
                buf.push('(');
                for (i, p) in pos_args.iter().enumerate() {
                    if i > 0 {
                        buf.push_str(", ");
                    }
                    self.write_pattern(p, buf);
                }
                // WI-445: named sub-patterns render `field: pat` after the
                // positionals (the `Foo(field: pat)` surface form).
                for (i, (field, p)) in named_args.iter().enumerate() {
                    if i > 0 || !pos_args.is_empty() {
                        buf.push_str(", ");
                    }
                    buf.push_str(self.view.sym_name(*field));
                    buf.push_str(": ");
                    self.write_pattern(p, buf);
                }
                buf.push(')');
            }
            Pattern::Tuple { positional, .. } => {
                buf.push('(');
                for (i, p) in positional.iter().enumerate() {
                    if i > 0 {
                        buf.push_str(", ");
                    }
                    self.write_pattern(p, buf);
                }
                buf.push(')');
            }
        }
        write_ann(buf);
    }

    /// A value as `.anthill` text, on whatever carrier it rides — a hash-consed term, an
    /// entity or a tuple a substitution rebuilt, an occurrence, a scalar — read through the
    /// view as [`Self::print_term`] reads a term, so one value prints one text
    /// (WI-20261022-DRGCP). The DATA spelling: a constructor's type named bare is `Foo[]`
    /// (kernel-language.md §4.4), an application `f(a, k: v)`.
    pub fn print_value(&self, v: &Value) -> String {
        self.print_item(&ViewItem::Owned(v.clone()))
    }

    /// The occurrences the walk does not spell ([`PrintView::own_spelling`]), written here,
    /// answering whether `occ` was one: an EXPRESSION or a PATTERN, by
    /// [`Self::write_occurrence`] — the view reads it as its reflect-term twin, which is not
    /// the source it was written as — and the one TYPE shape the view cannot read, a
    /// parameterized type whose base is itself an occurrence (a projection in base position,
    /// which `elim_child` can build and the view heads `Opaque`), written from its parts as
    /// the deleted type-node writer wrote it. No row builds that shape — the type renderer's
    /// twin of this arm (`type_display_name_occ`) says the same — so backing the arm out
    /// fails nothing; without it the shape prints `<opaque>`.
    fn write_own_occurrence(&self, occ: &Rc<NodeOccurrence>, buf: &mut String) -> bool {
        match &occ.kind {
            NodeKind::Type(TypeNode::Parameterized { base, bindings })
                if matches!(occ.head(self.view), ViewHead::Opaque) =>
            {
                self.write_type_item(&type_child_view_item(base), buf);
                buf.push('[');
                for (i, (sym, c)) in bindings.iter().enumerate() {
                    if i > 0 {
                        buf.push_str(", ");
                    }
                    buf.push_str(self.view.sym_name(*sym));
                    buf.push_str(" = ");
                    self.write_type_item(&type_child_view_item(c), buf);
                }
                buf.push(']');
                true
            }
            NodeKind::Type(_) | NodeKind::EffectExpr(_) => false,
            _ => {
                self.write_occurrence(occ, buf);
                true
            }
        }
    }

    /// The element terms of a GROUND cons/nil list spine, or `None` for anything else —
    /// [`Self::unwrap_spine`] over a term, for a caller holding `TermId`s.
    pub fn unwrap_list_spine(&self, id: TermId) -> Option<Vec<TermId>> {
        self.unwrap_spine(&ViewItem::Term(id))?
            .iter()
            .map(|item| item.as_term_id())
            .collect()
    }

    fn write_occurrence(&self, occ: &Rc<NodeOccurrence>, buf: &mut String) {
        if occ.as_pattern().is_some() {
            self.write_pattern(occ, buf);
            return;
        }
        // WI-348/349: a `Type` / `EffectExpr` occurrence (e.g. a `Modify[c]` effect label
        // on an `OperationInfo` value fact) is no `Expr`. It is written in the type spelling,
        // by the walk that writes its term twin (WI-20261022-DRGCP), where it had a hand-kept
        // writer of its own. A value that holds one is DATA, and [`Self::print_value`] writes
        // it as data.
        if occ.as_type().is_some() || occ.as_effect_expr().is_some() {
            self.write_type_item(&ViewItem::Node(Rc::clone(occ)), buf);
            return;
        }
        let Some(expr) = occ.as_expr() else {
            // A genuine rule-head wrapper has no surface body form; bodies are Expr.
            buf.push_str("<head>");
            return;
        };
        match expr {
            Expr::Var(var) => self.write_var(*var, buf),
            Expr::Const(lit) => write_literal(lit, buf),
            // WI-714: a macro-spliced pre-built value generally has no surface syntax —
            // it appears in a post-expansion op body, never in round-tripped source —
            // so it renders as an opaque marker.
            //
            // …EXCEPT a spliced hash-consed TERM, which has exactly the surface syntax
            // `write_term` prints. WI-20260904-J0RM4 made that reachable from a place a
            // user reads: a query pattern carrying a written empty effect row
            // (`Spec[E = {}]`) splices the canonical `effects_rows` term rather than
            // rebuilding it transiently, and `anthill query --query-file` labels each
            // query with this printer. It read `<spliced>` where the term spelling was
            // available one call away.
            //
            // …AND a carried term whose variables a substitution bound, which is a
            // transient entity over values where it is not that term: a structural type
            // written as a bracket's entry holding a clause's variable, read back from an
            // answer. The walk prints the structure it has, as it prints the term
            // (WI-20261022-DRGCP).
            Expr::Spliced(v) => self.write_item(&ViewItem::Owned(v.clone()), buf),
            Expr::Ref(sym) | Expr::Ident(sym) | Expr::VarRef { name: sym } => {
                buf.push_str(self.view.sym_name(*sym));
            }
            Expr::Bottom => buf.push_str("bottom"),
            Expr::Apply {
                functor,
                pos_args,
                named_args,
                ..
            } => {
                let fname = self.view.sym_name(*functor);
                // Round-trip the forall_impl encoding to surface syntax — the
                // occurrence twin of `write_term`'s special case. Asked of the QUALIFIED
                // name: the markers are kernel addresses, and a user's own `forall_impl`
                // shares only the short one.
                let qname = self.view.qualified_name(*functor);
                if dt::is_control(qname, dt::FORALL_IMPL)
                    && pos_args.len() == 3
                    && named_args.is_empty()
                {
                    if let (Some(binders), Some(ants), Some(cons)) = (
                        self.occ_unwrap_tuple(&pos_args[0]),
                        self.occ_unwrap_tuple(&pos_args[1]),
                        self.occ_unwrap_tuple(&pos_args[2]),
                    ) {
                        buf.push_str("(forall(");
                        self.write_occ_inner(binders, &[], buf);
                        buf.push_str("), ");
                        self.write_occ_inner(ants, &[], buf);
                        buf.push_str(" -: ");
                        self.write_occ_inner(cons, &[], buf);
                        buf.push(')');
                        return;
                    }
                }
                // WI-027: `forall_in(?x, xs, tuple(body))` / `some_in(…)` →
                // surface `(forall ?x in xs: body)` / `(some ?x in xs: body)`.
                let is_forall_in = dt::is_control(qname, dt::FORALL_IN);
                if (is_forall_in || dt::is_control(qname, dt::SOME_IN))
                    && pos_args.len() == 3
                    && named_args.is_empty()
                {
                    if let Some(body) = self.occ_unwrap_tuple(&pos_args[2]) {
                        let kw = if is_forall_in {
                            "forall"
                        } else {
                            "some"
                        };
                        buf.push('(');
                        buf.push_str(kw);
                        buf.push(' ');
                        self.write_occurrence(&pos_args[0], buf);
                        buf.push_str(" in ");
                        self.write_occurrence(&pos_args[1], buf);
                        buf.push_str(": ");
                        self.write_occ_inner(body, &[], buf);
                        buf.push(')');
                        return;
                    }
                }
                // WI-20260904-J0RM4 — THE TWO LIST SURFACES `write_term` COLLAPSES, and
                // they are here for the same reason: `anthill query --query-file` labels
                // each query with this printer, and a query pattern is now an occurrence
                // tree, so a surface `write_term` restored and this one did not is a
                // visible regression in the label. Both were driven by `/code-review`
                // against the built CLI.
                //
                // (a) A ground cons/nil SPINE — see [`Self::unwrap_list_spine`] for why
                //     the bare `nil`/`cons` form must not be the printed one. A rule
                //     body's `[…]` is an `Expr::ListLit` and never reaches here; a spine
                //     built as occurrences is what does.
                if let Some(items) = self.occ_unwrap_list_spine(occ) {
                    self.write_occ_seq('[', ']', &items, buf);
                    return;
                }
                // (b) The FLAT literal `ListLiteral(e…)`, which is what a `[…]` in a slot
                //     whose declared type names a RIVAL collection stays as
                //     (`list_literal_lowering` answers `None` there, spec §4.6). MEASURED
                //     before this: `entity Tagged(tags: Set[T = Int64])` queried with
                //     `tagged(Tagged(tags: [1, 2]))` labelled `ListLiteral(1, 2)`, with
                //     the `List`-declared sibling still labelling `[1, 2]` as the control.
                //     `dt::is` and `named_args.is_empty()` are `write_term`'s own gates —
                //     the named spelling parses positional-only (WI-560) and folding it
                //     would drop the payload. No `reload_faithful` arm: that mode is for
                //     writing facts to disk, and a fact is a term (see the note at
                //     `TermPrinter::reload_faithful`).
                if dt::is(fname, dt::LIST_LITERAL) && named_args.is_empty() {
                    self.write_occ_seq('[', ']', pos_args, buf);
                    return;
                }
                // WHAT IS STILL NOT MIRRORED, said rather than left to be rediscovered:
                // `write_term`'s `is_type_functor` → `write_type_term` surface rendering
                // (`(A) -> B @ {E}` for `TypeExtractor.Arrow`, and its siblings). It
                // cannot be delegated — `write_type_term` takes a `TermId` and this side
                // has no term to hand it — so mirroring it means an occurrence-side type
                // writer, which is its own piece of work. What reaches it is narrow: a
                // NodeKind::Type occurrence is already rendered structurally above, and
                // an `Expr::Apply` headed by a type functor needs the author to have
                // written `anthill.prelude.TypeExtractor.Arrow(…)` by name — the `[…]`
                // and `{}` surfaces both land elsewhere.
                self.write_occ_fn(fname, pos_args, named_args, buf);
            }
            Expr::ApplyWithin {
                functor,
                args,
                named_args,
                ..
            } => {
                self.write_occ_fn(self.view.sym_name(*functor), args, named_args, buf);
            }
            // Proposal 055 — a nominal type value round-trips to its own SURFACE, and
            // it needs its own writer twice over. `write_occ_fn` would print
            // `Cell(V: Int64)`: PARENTHESES, which the WI-710 surface gate re-reads as a
            // construction, and `k: v`, which is argument syntax rather than the
            // `V = Int64` a type binding is written with. Either alone makes a printed
            // body fail to load back as what it was.
            Expr::TypeValue {
                head,
                pos_args,
                named_args,
            } => self.write_type_value(*head, pos_args, named_args, true, buf),
            // The body-written `(…)` is a constructor over `TupleLiteral`
            // (`literal_as_constructor`), and prints as the literal, as `Expr::TupleLit` does.
            Expr::Constructor {
                name,
                pos_args,
                named_args,
                ..
            } if self.is_tuple_literal(*name) => self.write_occ_tuple(pos_args, named_args, buf),
            Expr::Constructor {
                name,
                pos_args,
                named_args,
                ..
            }
            | Expr::Instantiation {
                name,
                pos_args,
                named_args,
            }
            | Expr::ConstructorWithin {
                name,
                pos_args,
                named_args,
                ..
            } => {
                self.write_occ_fn(self.view.sym_name(*name), pos_args, named_args, buf);
            }
            Expr::DotApply {
                receiver,
                name,
                pos_args,
                named_args,
            } => {
                self.write_occurrence(receiver, buf);
                buf.push('.');
                buf.push_str(self.view.sym_name(*name));
                if !pos_args.is_empty() || !named_args.is_empty() {
                    self.write_occ_args(pos_args, named_args, buf);
                }
            }
            Expr::HoApply { predicate, args }
            | Expr::HoApplyWithin {
                predicate, args, ..
            } => {
                self.write_occurrence(predicate, buf);
                self.write_occ_args(args, &[], buf);
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                buf.push_str("if ");
                self.write_occurrence(condition, buf);
                buf.push_str(" then ");
                self.write_occurrence(then_branch, buf);
                buf.push_str(" else ");
                self.write_occurrence(else_branch, buf);
            }
            Expr::Let {
                pattern,
                value,
                body,
                ..
            } => {
                // WI-318: pattern is a Pattern-kind occurrence.
                buf.push_str("let ");
                self.write_pattern(pattern, buf);
                buf.push_str(" = ");
                self.write_occurrence(value, buf);
                buf.push_str(" in ");
                self.write_occurrence(body, buf);
            }
            Expr::Lambda { param, body } | Expr::LambdaWithin { param, body, .. } => {
                // WI-318: `param` is a Pattern-kind occurrence — render
                // structurally via `write_pattern`.
                buf.push('(');
                self.write_pattern(param, buf);
                buf.push_str(") => ");
                self.write_occurrence(body, buf);
            }
            Expr::Proof {
                target,
                strategy,
                using,
                conclude,
                body,
            } => {
                // WI-538: proof <target> [using …] [by …] [conclude …] end <body>
                buf.push_str("proof ");
                buf.push_str(self.view.sym_name(*target));
                if !using.is_empty() {
                    buf.push_str(" using ");
                    for (i, u) in using.iter().enumerate() {
                        if i > 0 {
                            buf.push_str(", ");
                        }
                        buf.push_str(self.view.sym_name(*u));
                    }
                }
                if let Some(strat) = strategy {
                    buf.push_str(" by ");
                    buf.push_str(self.view.sym_name(*strat));
                }
                if let Some(c) = conclude {
                    buf.push_str(" conclude ");
                    self.write_occurrence(c, buf);
                }
                buf.push_str(" end ");
                self.write_occurrence(body, buf);
            }
            Expr::Match {
                scrutinee,
                branches,
            } => {
                buf.push_str("match ");
                self.write_occurrence(scrutinee, buf);
                buf.push_str(" { ");
                for b in branches.iter() {
                    // WI-318: b.pattern is a Pattern-kind occurrence.
                    self.write_pattern(&b.pattern, buf);
                    // WI-20260907-0QV5A: the GUARD is rendered too. It decides at run
                    // time whether the arm is entered
                    // (`eval/eval.rs::scan_match_arms`), so dropping it rendered a
                    // guarded arm and an unguarded one as the same text — and this
                    // writer is what the load diagnostics quoting a body use.
                    if let Some(g) = &b.guard {
                        buf.push_str(" | ");
                        self.write_occurrence(g, buf);
                    }
                    buf.push_str(" => ");
                    self.write_occurrence(&b.body, buf);
                    buf.push_str("; ");
                }
                buf.push('}');
            }
            Expr::ListLit(es) => self.write_occ_seq('[', ']', es, buf),
            Expr::SetLit(es) => self.write_occ_seq('{', '}', es, buf),
            Expr::TupleLit { positional, named } => self.write_occ_tuple(positional, named, buf),
            Expr::RequirementAtSort { chain, slot } => {
                buf.push_str("requirement_at_sort(");
                self.write_occurrence(chain, buf);
                buf.push_str(&format!(", {slot})"));
            }
            // WI-1045 — printed the way the VALUE reads: `Dictionary(sub₀ … subₙ₋₁,
            // impl: S)`. One spelling, so a printed IR node and a printed dictionary
            // are the same text (`requirement-channel.md` §9).
            Expr::Dictionary { impl_sort, subs } => {
                buf.push_str("Dictionary(");
                for sub in subs.iter() {
                    self.write_occurrence(sub, buf);
                    buf.push_str(", ");
                }
                buf.push_str("impl: ");
                buf.push_str(self.view.sym_name(*impl_sort));
                buf.push(')');
            }
        }
    }

    /// Proposal 055's nominal type value. As DATA — an expression by itself — a bare one is a
    /// name in a data context, so a constructor's type face is written `red[]`, as its `Ref`
    /// twin is (kernel §4.4, WI-20261022-DRGCP). Its bindings are a TYPE context, where a
    /// type value is written bare, `Box[V = Untrusted]`, as the term printer writes the
    /// binding of its term twin; a binding that is no type value is the occurrence it is.
    fn write_type_value(
        &self,
        head: Symbol,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
        as_data: bool,
        buf: &mut String,
    ) {
        if pos_args.is_empty() && named_args.is_empty() {
            if as_data {
                self.write_symbol_ref(head, buf);
            } else {
                buf.push_str(self.view.sym_name(head));
            }
            return;
        }
        buf.push_str(self.view.sym_name(head));
        buf.push('[');
        let binding = |c: &Rc<NodeOccurrence>, buf: &mut String| match c.as_expr() {
            Some(Expr::TypeValue {
                head,
                pos_args,
                named_args,
            }) => self.write_type_value(*head, pos_args, named_args, false, buf),
            _ => self.write_occurrence(c, buf),
        };
        let mut first = true;
        for c in pos_args.iter() {
            if !std::mem::take(&mut first) {
                buf.push_str(", ");
            }
            binding(c, buf);
        }
        for (sym, c) in named_args.iter() {
            if !std::mem::take(&mut first) {
                buf.push_str(", ");
            }
            buf.push_str(self.view.sym_name(*sym));
            buf.push_str(" = ");
            binding(c, buf);
        }
        buf.push(']');
    }

    /// [`Self::unwrap_list_spine`] over the occurrence carrier — the element
    /// occurrences of a `cons(head:, tail:)` / positional-`cons` chain ending in a bare
    /// `nil`, or `None` for anything else (a var tail, a non-`nil` end, a `cons` carrying
    /// extra args, a non-list node).
    ///
    /// The ACCEPTANCE CONDITIONS are the term version's, deliberately down to the "exactly
    /// head+tail" test: a print that folded a `cons` with extras would silently drop them.
    /// Kept as a second function rather than shared, because the two walk different
    /// carriers and neither `TermView` nor `TermSource` exposes the "is this node a `Fn`
    /// with exactly these two named keys" question the fold turns on.
    fn occ_unwrap_list_spine(&self, occ: &NodeOccurrence) -> Option<Vec<Rc<NodeOccurrence>>> {
        let mut items: Vec<Rc<NodeOccurrence>> = Vec::new();
        let mut cur: &NodeOccurrence = occ;
        // Keeps each visited node alive while `cur` borrows into the next one.
        let mut owned: Rc<NodeOccurrence>;
        // BORROWED, not `to_string()`: this runs on every `Expr::Apply` the printer
        // meets, not only on lists, and the `write_term` twin compares on a `&str`.
        let short = |s: Symbol| {
            let n = self.view.sym_name(s);
            n.rsplit('.').next().unwrap_or(n)
        };
        loop {
            match cur.as_expr()? {
                Expr::Ref(s) if short(*s) == "nil" => return Some(items),
                Expr::Apply {
                    functor,
                    pos_args,
                    named_args,
                    ..
                } => {
                    let name = short(*functor);
                    if name == "nil" && pos_args.is_empty() && named_args.is_empty() {
                        return Some(items);
                    }
                    if name != "cons" {
                        return None;
                    }
                    let by_key = |k: &str| {
                        named_args
                            .iter()
                            .find(|(s, _)| self.view.sym_name(*s) == k)
                            .map(|(_, c)| Rc::clone(c))
                    };
                    let (head, tail) = match (by_key("head"), by_key("tail")) {
                        (Some(h), Some(t)) if named_args.len() == 2 && pos_args.is_empty() => {
                            (h, t)
                        }
                        (None, None) if pos_args.len() == 2 && named_args.is_empty() => {
                            (Rc::clone(&pos_args[0]), Rc::clone(&pos_args[1]))
                        }
                        _ => return None,
                    };
                    items.push(head);
                    owned = tail;
                    cur = &owned;
                }
                _ => return None,
            }
        }
    }

    fn write_occ_fn(
        &self,
        fname: &str,
        pos: &[Rc<NodeOccurrence>],
        named: &[(Symbol, Rc<NodeOccurrence>)],
        buf: &mut String,
    ) {
        buf.push_str(fname);
        if !pos.is_empty() || !named.is_empty() {
            self.write_occ_args(pos, named, buf);
        }
    }

    fn write_occ_args(
        &self,
        pos: &[Rc<NodeOccurrence>],
        named: &[(Symbol, Rc<NodeOccurrence>)],
        buf: &mut String,
    ) {
        buf.push('(');
        self.write_occ_inner(pos, named, buf);
        buf.push(')');
    }

    fn write_occ_inner(
        &self,
        pos: &[Rc<NodeOccurrence>],
        named: &[(Symbol, Rc<NodeOccurrence>)],
        buf: &mut String,
    ) {
        let mut first = true;
        for c in pos.iter() {
            if !first {
                buf.push_str(", ");
            }
            first = false;
            self.write_occurrence(c, buf);
        }
        for (sym, c) in named.iter() {
            if !first {
                buf.push_str(", ");
            }
            first = false;
            buf.push_str(self.view.sym_name(*sym));
            buf.push_str(": ");
            self.write_occurrence(c, buf);
        }
    }

    /// A tuple occurrence as its literal. Components named `_1`, `_2`, … in their own slots,
    /// two or more, are written without their labels, and a lone positional one with its
    /// label, as [`Self::write_tuple`] writes a tuple value.
    fn write_occ_tuple(
        &self,
        pos: &[Rc<NodeOccurrence>],
        named: &[(Symbol, Rc<NodeOccurrence>)],
        buf: &mut String,
    ) {
        let unlabelled = pos.is_empty()
            && named.len() > 1
            && named
                .iter()
                .enumerate()
                .all(|(i, (s, _))| is_positional_label_at(self.view.sym_name(*s), i));
        buf.push('(');
        if unlabelled {
            let components: Vec<Rc<NodeOccurrence>> =
                named.iter().map(|(_, c)| Rc::clone(c)).collect();
            self.write_occ_inner(&components, &[], buf);
        } else if let ([only], []) = (pos, named) {
            // `(x)` alone is grouping: a lone positional component keeps its label.
            buf.push_str(&crate::intern::positional_label(0));
            buf.push_str(": ");
            self.write_occurrence(only, buf);
        } else {
            self.write_occ_inner(pos, named, buf);
        }
        buf.push(')');
    }

    fn write_occ_seq(&self, open: char, close: char, es: &[Rc<NodeOccurrence>], buf: &mut String) {
        buf.push(open);
        for (i, e) in es.iter().enumerate() {
            if i > 0 {
                buf.push_str(", ");
            }
            self.write_occurrence(e, buf);
        }
        buf.push(close);
    }

    /// If `occ` is a `tuple(...)` apply occurrence with no named args, return a
    /// borrowed slice over its positional children — the occurrence twin of
    /// `unwrap_tuple`, used by the `forall_impl` surface-syntax rendering.
    fn occ_unwrap_tuple<'o>(&self, occ: &'o NodeOccurrence) -> Option<&'o [Rc<NodeOccurrence>]> {
        match occ.as_expr()? {
            Expr::Apply {
                functor,
                pos_args,
                named_args,
                ..
            } if self.view.sym_name(*functor) == "tuple" && named_args.is_empty() => Some(pos_args),
            _ => None,
        }
    }
}

impl<'a, V: PrintView + ?Sized> TermPrinter<'a, V> {
    /// Construct a printer over an arbitrary [`PrintView`].
    pub fn over(view: &'a V) -> Self {
        Self {
            view,
            reload_faithful: false,
            source_spelling: false,
        }
    }

    /// A printer whose text LOADS BACK to the term it was given, for writing
    /// facts to disk. See [`TermPrinter::reload_faithful`] for what it changes
    /// and why the content-key mode must not change with it (WI-1099).
    pub fn reload_faithful(view: &'a V) -> Self {
        Self {
            view,
            reload_faithful: true,
            source_spelling: false,
        }
    }

    /// Print a term as `.anthill` source text.
    pub fn print_term(&self, id: TermId) -> String {
        self.print_item(&self.view.term_item(id))
    }

    fn print_item(&self, item: &V::Item) -> String {
        let mut buf = String::new();
        self.write_item(item, &mut buf);
        buf
    }

    // ── Reading through the view ──────────────────────────────────

    /// The functor and arities of an application; `None` for anything else.
    fn application(&self, item: &V::Item) -> Option<(Symbol, usize, usize)> {
        match self.view.head(item) {
            ViewHead::Functor {
                functor: f,
                pos_arity,
                named_arity,
            } => Some((f, pos_arity, named_arity)),
            _ => None,
        }
    }

    /// The symbol a bare name is: a `Ref`, the nullary application that is the same term
    /// (WI-20260902-CZJ2N), an unresolved `Ident`.
    fn bare_name(&self, item: &V::Item) -> Option<Symbol> {
        match self.view.head(item) {
            ViewHead::Ident(s)
            | ViewHead::Functor {
                functor: s,
                pos_arity: 0,
                named_arity: 0,
            } => Some(s),
            _ => None,
        }
    }

    /// The named child whose key's local name is `key`.
    fn child(&self, item: &V::Item, key: &str) -> Option<V::Item> {
        self.view.named_child(item, key)
    }

    /// The name a parameter reference is written by where the text quotes its author
    /// ([`TermPrinter::source_spelling`]): the `name` child of the loader's `var_ref`
    /// wrapper, which may stand in a data slot or in a type's binding (`holds(Box[V = n])`).
    fn source_name(&self, item: &V::Item, f: Symbol) -> Option<V::Item> {
        if !self.source_spelling || self.view.qualified_name(f) != "anthill.reflect.Expr.var_ref" {
            return None;
        }
        self.child(item, "name")
    }

    /// The last dotted segment of a symbol's name. The parse side names a functor as written,
    /// so a qualified `anthill.prelude.List.cons` and a bare `cons` are one name here.
    fn short_name(&self, sym: Symbol) -> &str {
        let n = self.view.sym_name(sym);
        n.rsplit('.').next().unwrap_or(n)
    }

    // ── Data ───────────────────────────────────────────────────────

    /// Write `item` as DATA: the surface a fact, a goal's argument and a query answer take.
    fn write_item(&self, item: &V::Item, buf: &mut String) {
        if V::own_spelling(self, item, buf) {
            return;
        }
        match self.view.head(item) {
            ViewHead::Const(lit) => write_literal(&lit, buf),
            ViewHead::Var(var) => self.write_var(var, buf),
            ViewHead::Bottom => buf.push_str("bottom"),
            ViewHead::Ident(sym) => buf.push_str(self.view.sym_name(sym)),
            // A closure, a stream: nothing with a surface to print.
            ViewHead::Opaque => buf.push_str("<opaque>"),
            ViewHead::Functor {
                functor: f,
                pos_arity: 0,
                named_arity: 0,
            } if self.is_tuple_literal(f) => buf.push_str("()"),
            ViewHead::Functor {
                functor: f,
                pos_arity: 0,
                named_arity: 0,
            } => self.write_bare_name(item, f, buf),
            ViewHead::Functor {
                functor: f,
                pos_arity,
                named_arity,
            } => self.write_application(item, f, pos_arity, named_arity, buf),
        }
    }

    /// A bare name, as [`Self::write_symbol_ref`] writes it — save the EMPTY FLAT list
    /// literal (WI-1099), the one nullary application a store keeps as one rather than as
    /// its name: `[]` as the content key, and `ListLiteral()` where the text is read back,
    /// since written bare it reloads as a name. A name the parse side read with an empty
    /// bracket keeps it ([`PrintView::written_bracket`]): `Foo[]` on disk is the knowledge
    /// base's `Foo[]`, its type face, and the file store's key compares the two prints.
    fn write_bare_name(&self, item: &V::Item, f: Symbol, buf: &mut String) {
        let fname = self.view.sym_name(f);
        if dt::is(fname, dt::LIST_LITERAL) {
            if self.reload_faithful {
                buf.push_str(fname);
                buf.push_str("()");
            } else {
                buf.push_str("[]");
            }
            return;
        }
        self.write_symbol_ref(f, buf);
        if !f.is_type_face() && self.view.written_bracket(item) {
            buf.push_str("[]");
        }
    }

    /// An application with arguments, as DATA, in its surface form where it has one.
    fn write_application(
        &self,
        item: &V::Item,
        f: Symbol,
        pos_arity: usize,
        named_arity: usize,
        buf: &mut String,
    ) {
        if let Some(name) = self.source_name(item, f) {
            self.write_item(&name, buf);
            return;
        }
        // WI-20260902-JB6RS — a constructor's TYPE FACE heads a type, and so does a sort with
        // no constructor of its name; a type written as DATA takes the bracket (kernel §4.4):
        // `Foo[X = Int64]`, `List[T = Int64]`. Written with parentheses, a face's would reload
        // as an instance and a sort's is refused. WI-173: a type form carries a distinct
        // `TypeExtractor.*` functor, printed in its surface syntax (`(A) -> B @ {E}`).
        if self.view.heads_only_a_type(item, f) || self.is_type_form(f) {
            self.write_type_item(item, buf);
            return;
        }
        // WI-20261001-KDMQS — a NAME-ROOTED `field_access` chain prints as the dotted name it
        // spells. See [`Self::dotted_chain_name`].
        if let Some(name) = self.dotted_chain_name(item) {
            buf.push_str(&name);
            return;
        }
        // A ground cons/nil spine prints as a list literal (see [`Self::unwrap_spine`] for why
        // the cons form must not be written to disk).
        if let Some(items) = self.unwrap_spine(item) {
            buf.push('[');
            self.write_seq(&items, buf);
            buf.push(']');
            return;
        }
        let fname = self.view.sym_name(f);
        // The parse-IR list form (`[…]` parses to `Fn(ListLiteral, pos_args)`) prints back as
        // a bracket literal too, so the KB-side and parse-side canonical forms agree — the
        // content-keyed retract match in the file store compares exactly these two prints.
        //
        // WI-1099: NOT IN RELOAD-FAITHFUL MODE. A ground `cons` spine prints `[…]` too (just
        // above), so this text does not say WHICH of the two terms it came from — and `[…]`
        // reloads as the spine in every position that declares nothing (§4.6). Written by NAME
        // the flat literal survives, because only the bracket surface is lowered. The two
        // modes and why they cannot be one print: [`TermPrinter::reload_faithful`].
        //
        // `dt::is` and THE SHORT NAME, deliberately (WI-20260825-5W3RJ): the parse side names
        // the functor verbatim — `anthill.reflect.ListLiteral` where the desugar named its
        // target — and the KB view by its local name, and keying on one spelling splits the two
        // sides of the retract comparison (MEASURED with `==`:
        // `wi1099_list_literal_twin_test::a_persisted_literal_is_still_retractable` left the
        // fact on disk). The cost is narrow: a user's own `entity ListLiteral` prints as `[…]`
        // here though the loader would not lower it.
        if self.is_tuple_literal(f) && pos_arity == 0 {
            self.write_tuple(item, buf);
            return;
        }
        if dt::is(fname, dt::LIST_LITERAL) && named_arity == 0 && !self.reload_faithful {
            buf.push('[');
            self.write_positional(item, pos_arity, buf);
            buf.push(']');
            return;
        }
        // Round-trip the forall_impl encoding produced by convert_nested_implication back to
        // surface syntax. Asked of the QUALIFIED name, as the occurrence twin does: the
        // markers are kernel addresses, and a user's own `forall_impl` shares only the short
        // one (WI-20260827-J03AT).
        let qname = self.view.qualified_name(f);
        if dt::is_control(qname, dt::FORALL_IMPL) && pos_arity == 3 && named_arity == 0 {
            let parts: Vec<Option<Vec<V::Item>>> = (0..3)
                .map(|i| self.view.pos_arg(item, i).and_then(|p| self.unwrap_tuple(&p)))
                .collect();
            if let [Some(binders), Some(ants), Some(cons)] = parts.as_slice() {
                buf.push_str("(forall(");
                self.write_seq(binders, buf);
                buf.push_str("), ");
                self.write_seq(ants, buf);
                buf.push_str(" -: ");
                self.write_seq(cons, buf);
                buf.push(')');
                return;
            }
        }
        // WI-027: `forall_in` / `some_in` → surface bounded quantifier.
        let is_forall_in = dt::is_control(qname, dt::FORALL_IN);
        if (is_forall_in || dt::is_control(qname, dt::SOME_IN)) && pos_arity == 3 && named_arity == 0 {
            let body = self.view.pos_arg(item, 2).and_then(|b| self.unwrap_tuple(&b));
            if let (Some(var), Some(range), Some(body)) =
                (self.view.pos_arg(item, 0), self.view.pos_arg(item, 1), body)
            {
                buf.push('(');
                buf.push_str(if is_forall_in { "forall" } else { "some" });
                buf.push(' ');
                self.write_item(&var, buf);
                buf.push_str(" in ");
                self.write_item(&range, buf);
                buf.push_str(": ");
                self.write_seq(&body, buf);
                buf.push(')');
                return;
            }
        }
        buf.push_str(fname);
        buf.push('(');
        self.write_args(item, pos_arity, buf);
        buf.push(')');
    }

    /// The arguments of an application or a tuple, as DATA: the positional ones, then
    /// `k: v` for each named one.
    fn write_args(&self, item: &V::Item, pos_arity: usize, buf: &mut String) {
        self.write_positional(item, pos_arity, buf);
        for (i, key) in self.view.named_keys(item).into_iter().enumerate() {
            if pos_arity > 0 || i > 0 {
                buf.push_str(", ");
            }
            buf.push_str(self.view.sym_name(key));
            buf.push_str(": ");
            match self.view.named_arg(item, key) {
                Some(c) => self.write_item(&c, buf),
                None => buf.push('?'),
            }
        }
    }

    /// Is `f` the reflect `TupleLiteral` — asked of its QUALIFIED name, so a user's own
    /// entity of that short name is the application it is.
    fn is_tuple_literal(&self, f: Symbol) -> bool {
        let qname = self.view.qualified_name(f);
        qname == dt::TUPLE_LITERAL || qname == dt::qualified(dt::TUPLE_LITERAL)
    }

    /// A tuple as DATA, written as its literal: `(1, 2)`, `(a: 1, b: 2)`. A rule's tuple term
    /// and the tuple an operation built read alike, every component under its label. A
    /// positional component goes without its `_N` label, except as the only one, where
    /// `(x)` would be grouping. The tuple of no components is written `()` where its head is
    /// read.
    fn write_tuple(&self, item: &V::Item, buf: &mut String) {
        let keys = self.view.named_keys(item);
        let positional = keys.len() > 1
            && keys
                .iter()
                .enumerate()
                .all(|(i, k)| is_positional_label_at(self.view.sym_name(*k), i));
        buf.push('(');
        for (i, key) in keys.into_iter().enumerate() {
            if i > 0 {
                buf.push_str(", ");
            }
            if !positional {
                buf.push_str(self.view.sym_name(key));
                buf.push_str(": ");
            }
            match self.view.named_arg(item, key) {
                Some(c) => self.write_item(&c, buf),
                None => buf.push('?'),
            }
        }
        buf.push(')');
    }

    fn write_positional(&self, item: &V::Item, pos_arity: usize, buf: &mut String) {
        for i in 0..pos_arity {
            if i > 0 {
                buf.push_str(", ");
            }
            match self.view.pos_arg(item, i) {
                Some(c) => self.write_item(&c, buf),
                None => buf.push('?'),
            }
        }
    }

    fn write_seq(&self, items: &[V::Item], buf: &mut String) {
        for (i, c) in items.iter().enumerate() {
            if i > 0 {
                buf.push_str(", ");
            }
            self.write_item(c, buf);
        }
    }

    /// If `item` is a `tuple(...)` application with no named args, its positional contents.
    /// Used by the `forall_impl` / `forall_in` surface forms.
    fn unwrap_tuple(&self, item: &V::Item) -> Option<Vec<V::Item>> {
        let (f, pos_arity, named_arity) = self.application(item)?;
        if self.view.sym_name(f) != "tuple" || named_arity != 0 {
            return None;
        }
        (0..pos_arity).map(|i| self.view.pos_arg(item, i)).collect()
    }

    /// The element items of a GROUND cons/nil list spine (named `cons(head: …, tail: …)` or
    /// positional `cons(…, …)`, ending in a nullary `nil`), or `None` for anything else — a
    /// var tail, a non-nil end, a non-list term. Used to print list spines as `[…]` literals:
    /// the bare-name nullary print (`nil`) reloads as a NAME REFERENCE, which no longer unifies
    /// with `nil()` / `cons(…)` patterns — the round-trip bug that made runtime-persisted work
    /// items invisible to the workflow rules.
    fn unwrap_spine(&self, item: &V::Item) -> Option<Vec<V::Item>> {
        let mut items = Vec::new();
        let mut cur = item.clone();
        loop {
            let (f, pos_arity, named_arity) = self.application(&cur)?;
            let short = self.short_name(f);
            // WI-511: the canonical nullary `nil` terminator is the bare `Ref(nil)` form (the
            // alloc flip stores 0-ary constructors as `Ref`), which heads as this.
            if short == "nil" && pos_arity == 0 && named_arity == 0 {
                return Some(items);
            }
            if short != "cons" {
                return None;
            }
            // EXACTLY head+tail — a cons carrying extra named or positional args is not a list
            // spine; folding it would silently drop the extras.
            let (head, tail) = if pos_arity == 0 && named_arity == 2 {
                (self.child(&cur, "head")?, self.child(&cur, "tail")?)
            } else if pos_arity == 2 && named_arity == 0 {
                (self.view.pos_arg(&cur, 0)?, self.view.pos_arg(&cur, 1)?)
            } else {
                return None;
            };
            items.push(head);
            cur = tail;
        }
    }

    /// The elements of a list a type form holds — a tuple's fields, a ∀'s binders, a row
    /// guard's goals: a spine as [`Self::unwrap_spine`] reads it, and otherwise the heads of
    /// its `cons` cells up to the first that is none, as `value_list_elements` reads a
    /// value-carried list.
    fn list_elements(&self, item: &V::Item) -> Vec<V::Item> {
        if let Some(items) = self.unwrap_spine(item) {
            return items;
        }
        let mut out = Vec::new();
        let mut cur = Some(item.clone());
        while let Some(cell) = cur {
            if !matches!(self.application(&cell), Some((f, _, _)) if self.short_name(f) == "cons") {
                break;
            }
            match self.child(&cell, "head") {
                Some(h) => out.push(h),
                None => break,
            }
            cur = self.child(&cell, "tail");
        }
        out
    }

    /// WI-20261001-KDMQS — the dotted name a NAME-ROOTED `field_access` chain spells
    /// (`field_access(Float, infinity)` is `Float.infinity`), or `None` for anything else.
    /// Name-rooted means every receiver down the chain is a name or another such chain, and
    /// every selector is a name: the shape §6.7 lowers a written `A.B` to. A projection on a
    /// value (`?x.f`) or a typer-minted selector (a string) is not one and prints as its
    /// structure.
    ///
    /// THE CONTENT KEY NEEDS IT. The loader folds a const in a data slot to its value, so a
    /// persisted `+∞` is written `Float.infinity` (the const's name, [`write_literal`]), loads
    /// as the Float, and keys as `Float.infinity` on the KB side, while the parse of the same
    /// on-disk text is the minted chain `field_access(Float, infinity)`. The file store's
    /// retract compares those two prints. Printed structurally they differ and the retract is
    /// a silent no-op.
    ///
    /// ON BOTH VIEWS, and not gated on the parse side's `is_minted` provenance. Gated, a
    /// HAND-written dotted name that is not a const (`fact h(o: Option.none)`) would key
    /// `Option.none` from its text and `field_access(Option, none)` from the KB, which is the
    /// same silent no-op one spelling over. Ungated, both views print one text for one chain.
    fn dotted_chain_name(&self, item: &V::Item) -> Option<String> {
        let (f, pos_arity, named_arity) = self.application(item)?;
        if named_arity != 0 || pos_arity != 2 || !dt::is(self.view.sym_name(f), dt::FIELD_ACCESS) {
            return None;
        }
        let selector = self.bare_name(&self.view.pos_arg(item, 1)?)?;
        let receiver = self.view.pos_arg(item, 0)?;
        let receiver = match self.bare_name(&receiver) {
            Some(s) => self.view.sym_name(s).to_owned(),
            None => self.dotted_chain_name(&receiver)?,
        };
        Some(format!("{receiver}.{}", self.view.sym_name(selector)))
    }

    /// WI-173: is `functor` one of the distinct `TypeExtractor.*` type functors the data
    /// walk writes in their surface syntax? Matched on the QUALIFIED name so a user
    /// sort/entity sharing a short name is never misread as a type. `EffectExpression` atoms
    /// (`present`/`merge`/…) and `NamedTupleElement` are deliberately absent: as data they are
    /// the applications they are — `present(label: Int64)` is not the label `Int64` — and
    /// within a row or a tuple's fields the dedicated walkers read them.
    fn is_type_form(&self, functor: Symbol) -> bool {
        matches!(
            self.view.qualified_name(functor),
            "anthill.prelude.TypeExtractor.Arrow"
                | "anthill.prelude.TypeExtractor.NamedTuple"
                | "anthill.prelude.TypeExtractor.EffectsRows"
                | "anthill.prelude.TypeExtractor.Denoted"
                | "anthill.prelude.TypeExtractor.ExprCarried"
                | "anthill.prelude.TypeExtractor.RigidTypeProjection"
                | "anthill.prelude.TypeExtractor.TypeVar"
                | "anthill.prelude.TypeExtractor.Nothing"
        )
    }

    /// The one spelling of a logic variable — `?x` (flex global), `?#n` (De Bruijn), `!x`
    /// (rigid) — shared by the walk and the CLI's answer renderer for a value-level
    /// `Value::Var`. WI-20260905-N20EZ: an unbound answer rides that carrier now (the
    /// resolver's fresh var is no longer an interned term), and the renderer's `Debug`
    /// fallback printed `Var(Global(VarId { .. }))` where `?_` was the answer — the same
    /// cross-carrier divergence `write_symbol_ref` exists to prevent, one leaf over.
    ///
    /// A rigid is `?x` where the text quotes its author ([`TermPrinter::source_spelling`]):
    /// the skolem is how a body is checked, and its declaration wrote `?x`.
    pub fn write_var(&self, var: Var, buf: &mut String) {
        match var {
            Var::Global(vid) => {
                buf.push('?');
                buf.push_str(self.view.sym_name(vid.name()));
            }
            Var::DeBruijn(n) => buf.push_str(&format!("?#{n}")),
            Var::Rigid(vid) => {
                buf.push(if self.source_spelling { '?' } else { '!' });
                buf.push_str(self.view.sym_name(vid.name()));
            }
        }
    }

    /// Render a bare symbol reference — a `Ref`, its nullary twins, and the
    /// `Value::SymbolRef` carrier, which has no `TermId` to hand.
    ///
    /// ONE owner so two carriers of one symbol can never render — and so never KEY —
    /// differently; `Interpreter::write_value_canonical` builds a store key from this, and a
    /// key that disagrees with its own twin's is the WI-425 cross-carrier wrong answer, not a
    /// cosmetic difference.
    pub fn write_symbol_ref(&self, sym: Symbol, buf: &mut String) {
        if self.view.qualified_name(sym) == "anthill.prelude.TypeExtractor.Nothing" {
            buf.push_str("nothing");
        } else {
            buf.push_str(self.view.sym_name(sym));
            // A constructor's TYPE written as data is `Foo[]`: its bare name there is the
            // instance (kernel §4.4, WI-20260902-JB6RS). The type writer prints a face bare —
            // [`Self::write_type_item`]'s own bare-name arm, which does not come here.
            if sym.is_type_face() {
                buf.push_str("[]");
            }
        }
    }

    // ── Types ──────────────────────────────────────────────────────

    /// WI-173: write `item` as a TYPE, the spelling a type annotation takes: an application
    /// is the PARAMETERIZED type `S[k = v]` — unambiguous here, unlike the data walk, where the
    /// same shape is a data term `S(k: v)` (WI-361: types and data share the application) —
    /// a type form is its surface syntax, and a constructor's type face named bare is its
    /// name. A variable, a value in a type and anything else with no type surface is written
    /// as data.
    fn write_type_item(&self, item: &V::Item, buf: &mut String) {
        if V::own_spelling(self, item, buf) {
            return;
        }
        match self.view.head(item) {
            ViewHead::Ident(s)
            | ViewHead::Functor {
                functor: s,
                pos_arity: 0,
                named_arity: 0,
            } => match self.view.qualified_name(s) {
                // WI-511: the nullary `Nothing` type extractor is the canonical bare name.
                "anthill.prelude.TypeExtractor.Nothing" => buf.push_str("nothing"),
                // The empty row standing alone, as its occurrence was written: `{}`.
                "anthill.prelude.EffectExpression.empty_row" => buf.push_str("{}"),
                _ => buf.push_str(self.view.sym_name(s)),
            },
            ViewHead::Functor {
                functor: f,
                pos_arity,
                ..
            } => match self.source_name(item, f) {
                Some(name) => self.write_item(&name, buf),
                None => self.write_type_application(item, f, pos_arity, buf),
            },
            _ => self.write_item(item, buf),
        }
    }

    fn write_type_application(&self, item: &V::Item, f: Symbol, pos_arity: usize, buf: &mut String) {
        match self.view.qualified_name(f) {
            "anthill.prelude.TypeExtractor.Arrow" => self.write_arrow_type(item, buf),
            "anthill.prelude.TypeExtractor.NamedTuple" => self.write_named_tuple_type(item, buf),
            // A standalone effect-row type renders its braced row.
            "anthill.prelude.TypeExtractor.EffectsRows" => {
                buf.push('{');
                if let Some(row) = self.child(item, "effects_expr") {
                    buf.push_str(&self.effect_atoms(&row).join(", "));
                }
                buf.push('}');
            }
            // A value-in-type (`Modify[c]`'s `c`) — the carried value, as data.
            "anthill.prelude.TypeExtractor.Denoted" => match self.child(item, "value") {
                Some(v) => self.write_item(&v, buf),
                None => buf.push('?'),
            },
            // `s.member` — the receiver value then `.member`.
            "anthill.prelude.TypeExtractor.ExprCarried" => {
                self.write_dotted(item, "value", "member", buf)
            }
            // `subject.member` — the type-receiver projection (`P.Key`).
            "anthill.prelude.TypeExtractor.RigidTypeProjection" => {
                self.write_dotted(item, "var", "member", buf)
            }
            // A type variable prints as the inference var `?name`.
            "anthill.prelude.TypeExtractor.TypeVar" => {
                buf.push('?');
                if let Some(n) = self.child(item, "name") {
                    self.write_item(&n, buf);
                }
            }
            "anthill.prelude.TypeExtractor.Nothing" => buf.push_str("nothing"),
            "anthill.prelude.TypeExtractor.PolyType" => self.write_poly_type(item, buf),
            // An effect row's algebra standing alone, unwrapped, in a type position: its atoms,
            // as a row's `{…}` holds them — the spelling its occurrence was given (the empty
            // row, nullary, is the bare-name arm's).
            q if q.starts_with("anthill.prelude.EffectExpression.") => {
                buf.push_str(&self.effect_atoms(item).join(", "))
            }
            // Any other functor is the parameterized type `S[k = v, …]` (WI-361: the base sort
            // IS the functor, the bindings ARE the named args).
            base => {
                buf.push_str(base.rsplit('.').next().unwrap_or(base));
                buf.push('[');
                for i in 0..pos_arity {
                    if i > 0 {
                        buf.push_str(", ");
                    }
                    match self.view.pos_arg(item, i) {
                        Some(c) => self.write_type_item(&c, buf),
                        None => buf.push('?'),
                    }
                }
                for (i, key) in self.view.named_keys(item).into_iter().enumerate() {
                    if pos_arity > 0 || i > 0 {
                        buf.push_str(", ");
                    }
                    buf.push_str(self.view.sym_name(key));
                    buf.push_str(" = ");
                    match self.view.named_arg(item, key) {
                        Some(c) => self.write_type_item(&c, buf),
                        None => buf.push('?'),
                    }
                }
                buf.push(']');
            }
        }
    }

    /// `receiver.member`, each read as data.
    fn write_dotted(&self, item: &V::Item, receiver: &str, member: &str, buf: &mut String) {
        if let Some(r) = self.child(item, receiver) {
            self.write_item(&r, buf);
        }
        buf.push('.');
        if let Some(m) = self.child(item, member) {
            self.write_item(&m, buf);
        }
    }

    /// WI-1083: `forall A, B. <body>` — the quantifier is rendered even though it is not
    /// stored (a PolyType is ∀ by construction), because the whole point of the form is that
    /// the ∀ used to be invisible. WI-20260904-50B2K part (c): `forall A. C => body`, the `=>`
    /// written only when there IS a context.
    fn write_poly_type(&self, item: &V::Item, buf: &mut String) {
        buf.push_str("forall ");
        let binders = self.child(item, "binders").map(|b| self.list_elements(&b)).unwrap_or_default();
        self.write_type_seq(&binders, buf);
        buf.push_str(". ");
        let context = self.child(item, "context").map(|c| self.list_elements(&c)).unwrap_or_default();
        if !context.is_empty() {
            self.write_type_seq(&context, buf);
            buf.push_str(" => ");
        }
        match self.child(item, "body") {
            Some(b) => self.write_type_item(&b, buf),
            None => buf.push('?'),
        }
    }

    fn write_type_seq(&self, items: &[V::Item], buf: &mut String) {
        for (i, c) in items.iter().enumerate() {
            if i > 0 {
                buf.push_str(", ");
            }
            self.write_type_item(c, buf);
        }
    }

    /// WI-173: `arrow(param, result, effects)` → `(<param>) -> <result>` with an optional
    /// `@ <effects>`. When `param` is itself a named tuple its own parenthesised form is used
    /// directly (avoids double-wrapping `((a: T)) ->`).
    ///
    /// WI-766: that direct form is AMBIGUOUS at arity one, and only there. The loader reads a
    /// single arrow parameter by its TYPE and drops the label, so `(a: T) -> R` loads as
    /// `arrow(param = T)` — meaning a genuine one-component tuple parameter, `arrow(param =
    /// (a: T))`, would print to that same text and read back as the scalar. Arity one
    /// therefore keeps the outer parens.
    ///
    /// WI-791: which case this IS is read from the arrow's own `arity` child instead of
    /// guessed from the param's component count. That distinction is what makes the round
    /// trip FAITHFUL rather than merely stable: the two spellings that used to print alike —
    /// `(t: (a: A, b: B)) -> R` (arity 1) and `(a: A, b: B) -> R` (arity 2) — print as
    /// `((a: A, b: B)) -> R` and `(a: A, b: B) -> R`, each reparsing to the arrow it came
    /// from.
    fn write_arrow_type(&self, item: &V::Item, buf: &mut String) {
        let arity = self.child(item, "arity").and_then(|a| self.const_usize(&a));
        match self.child(item, "param") {
            None => buf.push_str("()"),
            Some(p) => {
                // Does the `param` slot ALREADY render as the parameter list? Only a named
                // tuple can, and only when the arrow says it is one; a count this cannot read
                // falls back to the pre-WI-791 shape heuristic.
                let slot_is_the_list = self.is_named_tuple(&p)
                    && match arity {
                        Some(n) => n != 1,
                        None => self.named_tuple_arity(&p) != 1,
                    };
                if slot_is_the_list {
                    self.write_tuple_components(&p, buf);
                } else {
                    buf.push('(');
                    self.write_type_item(&p, buf);
                    buf.push(')');
                }
            }
        }
        buf.push_str(" -> ");
        match self.child(item, "result") {
            Some(r) => self.write_type_item(&r, buf),
            None => buf.push('?'),
        }
        // `@ E` for a single atom, `@ {E1, E2}` for a set, and nothing for the pure row.
        if let Some(e) = self.child(item, "effects") {
            let atoms = self.effect_atoms(&e);
            if !atoms.is_empty() {
                buf.push_str(" @ ");
                if atoms.len() == 1 {
                    buf.push_str(&atoms[0]);
                } else {
                    buf.push('{');
                    buf.push_str(&atoms.join(", "));
                    buf.push('}');
                }
            }
        }
    }

    /// WI-791: an arrow's `arity` child, a non-negative integer literal; `None` for any other
    /// shape, which keeps the pre-WI-791 rendering rather than inventing a parenthesisation.
    fn const_usize(&self, item: &V::Item) -> Option<usize> {
        match self.view.head(item) {
            ViewHead::Const(Literal::Int(n)) => usize::try_from(n).ok(),
            _ => None,
        }
    }

    fn is_named_tuple(&self, item: &V::Item) -> bool {
        matches!(self.application(item), Some((f, _, _))
            if self.view.qualified_name(f) == "anthill.prelude.TypeExtractor.NamedTuple")
    }

    /// Component count of a named tuple. Only the arity-one case is acted on (see
    /// [`Self::write_arrow_type`]); a shape this cannot read counts 0, which routes to the
    /// pre-WI-766 behaviour rather than inventing parens.
    fn named_tuple_arity(&self, item: &V::Item) -> usize {
        self.child(item, "fields").map_or(0, |f| self.list_elements(&f).len())
    }

    /// WI-173: `named_tuple(fields)` → `(<f1>, <f2>, …)`. A positional field (name `_N`) prints
    /// as the bare type; a named field as `n: T`. The tuple of no components is `Unit`, the
    /// prelude's name for it.
    fn write_named_tuple_type(&self, item: &V::Item, buf: &mut String) {
        if self.child(item, "fields").is_some_and(|f| self.list_elements(&f).is_empty()) {
            buf.push_str("Unit");
        } else {
            self.write_tuple_components(item, buf);
        }
    }

    /// A named tuple's components in parentheses — a tuple type of one or more, and an
    /// arrow's parameter list of any count, `()` for none.
    fn write_tuple_components(&self, item: &V::Item, buf: &mut String) {
        buf.push('(');
        if let Some(fields) = self.child(item, "fields") {
            for (i, elem) in self.list_elements(&fields).iter().enumerate() {
                if i > 0 {
                    buf.push_str(", ");
                }
                self.write_named_tuple_element(elem, i, buf);
            }
        }
        buf.push(')');
    }

    /// One `NamedTupleElement(name, type)` → `n: T`, or bare `T` for a positional `_N` field
    /// name (the surface tuple form `(A, B)` has no field labels). `index` is the component's
    /// own position, which is what decides whether its label is the synthetic one — see
    /// [`Self::is_positional_name`].
    fn write_named_tuple_element(&self, elem: &V::Item, index: usize, buf: &mut String) {
        if self.application(elem).is_none() {
            self.write_type_item(elem, buf);
            return;
        }
        let name = self.child(elem, "name");
        let positional = name
            .as_ref()
            .map(|n| self.is_positional_name(n, index))
            .unwrap_or(true);
        if let (false, Some(n)) = (positional, &name) {
            self.write_item(n, buf);
            buf.push_str(": ");
        }
        match self.child(elem, "type") {
            Some(t) => self.write_type_item(&t, buf),
            None => buf.push('?'),
        }
    }

    /// Is this component's name the synthetic label for its OWN position — i.e. is it the
    /// surface `(A, B)` form, whose labels the printer must omit?
    ///
    /// This was the LOOSEST of the five recognizers: `_` + digits at ANY index, which the
    /// caller then ERASED. Two classes of user label were lost that way, both MEASURED before
    /// the fix: `(_01: Int64, b: Int64)` printed as `(Int64, b: Int64)` — `_01` is a user label
    /// (WI-786), and the output mixes positional and named fields, which the parser REJECTS —
    /// and `(_2: Int64, b: Int64)` printed the same way, where the loader then mints `_1` for
    /// slot 0: a silent field RENAME across a persistence round trip. Asking
    /// [`is_positional_label_at`] with the component's own index refuses both, and a genuine
    /// `(Int64, Int64)` still prints without labels (WI-790/WI-789).
    fn is_positional_name(&self, name: &V::Item, index: usize) -> bool {
        self.bare_name(name)
            .is_some_and(|s| is_positional_label_at(self.view.sym_name(s), index))
    }

    /// WI-173: an effect row's atoms as rendered surface strings — `present(L)` → `L`,
    /// `absent(L)` → `-L`, `guarded(L, g)` → `L :- g`, `open(tail)` → the tail variable,
    /// `merge(a, b)` → both, `empty_row` → none, an `EffectsRows` wrapper → its row. The
    /// right-folded `merge` chain `build_canonical_effects_rows` produces flattens back to the
    /// ordered atom list the surface row `{…}` parses from. Anything else — a label standing
    /// where the row is (a bare `effects Modify[c]`), a row variable — is one atom, its type.
    fn effect_atoms(&self, item: &V::Item) -> Vec<String> {
        let mut out = Vec::new();
        self.collect_effect_atoms(item, &mut out);
        out
    }

    fn collect_effect_atoms(&self, item: &V::Item, out: &mut Vec<String>) {
        let form = self.application(item).map(|(f, _, _)| self.view.qualified_name(f));
        match form {
            Some("anthill.prelude.TypeExtractor.EffectsRows") => {
                if let Some(row) = self.child(item, "effects_expr") {
                    self.collect_effect_atoms(&row, out);
                }
            }
            Some("anthill.prelude.EffectExpression.empty_row") => {}
            Some("anthill.prelude.EffectExpression.merge") => {
                for side in ["left", "right"] {
                    if let Some(c) = self.child(item, side) {
                        self.collect_effect_atoms(&c, out);
                    }
                }
            }
            Some("anthill.prelude.EffectExpression.present") => {
                if let Some(l) = self.child(item, "label") {
                    out.push(self.type_text(&l));
                }
            }
            Some("anthill.prelude.EffectExpression.absent") => {
                if let Some(l) = self.child(item, "label") {
                    out.push(format!("-{}", self.type_text(&l)));
                }
            }
            // WI-478: `guarded(label, guard)` renders as the surface `E :- g1, …` — a single
            // goal uses the bare form, a conjunctive guard the parenthesized `( E :- g1, g2 )`
            // so it round-trips through the parser.
            Some("anthill.prelude.EffectExpression.guarded") => {
                if let Some(l) = self.child(item, "label") {
                    let label = self.type_text(&l);
                    let goals: Vec<String> = self
                        .child(item, "guard")
                        .map(|g| self.list_elements(&g))
                        .unwrap_or_default()
                        .iter()
                        .map(|g| self.print_item(g))
                        .collect();
                    let body = goals.join(", ");
                    out.push(if goals.len() > 1 {
                        format!("( {label} :- {body} )")
                    } else {
                        format!("{label} :- {body}")
                    });
                }
            }
            Some("anthill.prelude.EffectExpression.open") => {
                if let Some(tail) = self.child(item, "tail") {
                    out.push(self.type_text(&tail));
                }
            }
            _ => out.push(self.type_text(item)),
        }
    }

    fn type_text(&self, item: &V::Item) -> String {
        let mut s = String::new();
        self.write_type_item(item, &mut s);
        s
    }
}

/// Print a fact as a `fact` declaration in `.anthill` syntax — the text
/// `FileStore::persist` writes to disk. Generic over `TermSource` for the same
/// reason the printer is: a caller may hold either a live-KB head or a parse-IR
/// one.
///
/// WI-1099: this is the RELOAD-FAITHFUL question and NOT the retract path's
/// (which calls `TermPrinter::print_term` on both sides itself, and needs the
/// canonical surface). The two are one function's two modes —
/// [`TermPrinter::reload_faithful`] carries the rule, the measurement, and why
/// no single text can serve both.
/// Render one fact as the `.anthill` text a loader reads back.
///
/// WI-1099: the text this writes is READ BACK by the loader, so it is the
/// reload-faithful question, not the canonical-surface one. The file store's
/// retract key keeps the surface print — see [`TermPrinter::reload_faithful`].
pub fn print_fact<V: PrintView + ?Sized>(view: &V, term: TermId, meta: Option<TermId>) -> String {
    let printer = TermPrinter::reload_faithful(view);
    let mut out = String::from("fact ");
    out.push_str(&printer.print_term(term));
    if let Some(meta_id) = meta {
        out.push_str(" {\n  ");
        out.push_str(&printer.print_term(meta_id));
        out.push_str("\n}");
    }
    out.push('\n');
    out
}

/// [`print_fact`], with the named arguments in `omit` LEFT OUT of the top-level
/// application (WI-1120).
///
/// The one caller is the document encoding, where a prose field moves out of the
/// head and becomes a markdown chapter (design §5.3): the head must then be
/// printed without it, and there is no term to print — `Store::persist` is handed
/// `&KnowledgeBase`, so a stripped copy of the fact cannot be interned on the
/// way past.
///
/// TOP LEVEL ONLY, and by NAME. A nested `Feedback(content: …)` inside some other
/// term is not this fact's field, and dropping it would silently edit a subterm
/// nobody asked about. If the top-level term carries none of the named arguments,
/// this IS [`print_fact`] — same text, same round trip.
pub fn print_fact_omitting<V: PrintView + ?Sized>(
    view: &V,
    term: TermId,
    meta: Option<TermId>,
    omit: &[&str],
) -> String {
    let item = view.term_item(term);
    let (functor, pos_arity) = match view.head(&item) {
        ViewHead::Functor {
            functor: f,
            pos_arity,
            ..
        } => (f, pos_arity),
        _ => return print_fact(view, term, meta),
    };
    let keys = view.named_keys(&item);
    if omit.is_empty() || !keys.iter().any(|s| omit.contains(&view.sym_name(*s))) {
        return print_fact(view, term, meta);
    }
    let printer = TermPrinter::reload_faithful(view);
    let mut out = String::from("fact ");
    out.push_str(view.sym_name(functor));
    out.push('(');
    let mut first = true;
    for i in 0..pos_arity {
        if !std::mem::take(&mut first) {
            out.push_str(", ");
        }
        match view.pos_arg(&item, i) {
            Some(c) => out.push_str(&printer.print_item(&c)),
            None => out.push('?'),
        }
    }
    for key in keys {
        if omit.contains(&view.sym_name(key)) {
            continue;
        }
        if !std::mem::take(&mut first) {
            out.push_str(", ");
        }
        out.push_str(view.sym_name(key));
        out.push_str(": ");
        match view.named_arg(&item, key) {
            Some(c) => out.push_str(&printer.print_item(&c)),
            None => out.push('?'),
        }
    }
    out.push(')');
    if let Some(meta_id) = meta {
        out.push_str(" {\n  ");
        out.push_str(&printer.print_term(meta_id));
        out.push_str("\n}");
    }
    out.push('\n');
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kb::term::Literal;
    use ordered_float::OrderedFloat;
    use smallvec::SmallVec;

    /// A value carried on an occurrence prints the structure it has: an entity a
    /// substitution rebuilt, with a term, a variable and a scalar under it. Before, any
    /// carried value that was no term printed `<spliced>`. With the walk's `ViewHead::Const`
    /// arm writing `?`, the `1` and the `3` below print `?` (WI-20261022-DRGCP: the walk that
    /// prints a term prints the value too).
    #[test]
    fn a_carried_entity_prints_its_arguments() {
        use crate::kb::node_occurrence::{Expr, NodeOccurrence};
        let mut kb = KnowledgeBase::new();
        let (f, n, k) = (kb.intern("f"), kb.intern("n"), kb.intern("k"));
        let leaf = kb.alloc(Term::Const(Literal::Int(1)));
        let var = kb.fresh_var(k);
        let entity = Value::Entity {
            functor: f,
            pos: vec![Value::term(leaf), Value::Var(Var::Global(var))].into(),
            named: vec![(n, Value::Int(3))].into(),
        };
        let occ = NodeOccurrence::new_expr(
            Expr::Spliced(entity),
            crate::kb::node_occurrence::empty_span(),
            None,
        );
        let printed = TermPrinter::new(&kb).print_occurrence(&occ);
        assert_eq!(printed, "f(1, ?k, n: 3)");
    }

    /// An opaque value inside a value is named by its kind (WI-20261022-DRGCP): it has no
    /// surface, and the kind is what an answer can say of it.
    #[test]
    fn an_opaque_value_in_a_value_is_named_by_its_kind() {
        let mut kb = KnowledgeBase::new();
        let (f, h, d) = (kb.intern("f"), kb.intern("h"), kb.intern("d"));
        let one = kb.alloc(Term::Const(Literal::Int(1)));
        let head = kb.alloc(Term::Fn {
            functor: h,
            pos_args: SmallVec::from_elem(one, 1),
            named_args: SmallVec::new(),
        });
        let rid = kb.assert_fact(head, crate::kb::ClauseKind::Fact, d, None);
        let v = Value::Entity {
            functor: f,
            pos: vec![Value::FactRef(crate::kb::extent::FactRef::resident(rid))].into(),
            named: vec![].into(),
        };
        assert_eq!(TermPrinter::new(&kb).print_value(&v), "f(<FactRef>)");
    }

    #[test]
    fn print_int_literal() {
        let mut kb = KnowledgeBase::new();
        let t = kb.alloc(Term::Const(Literal::Int(42)));
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "42");
    }

    #[test]
    fn print_float_literal() {
        let mut kb = KnowledgeBase::new();
        let t = kb.alloc(Term::Const(Literal::Float(OrderedFloat(3.14))));
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "3.14");
    }

    #[test]
    fn print_string_literal() {
        let mut kb = KnowledgeBase::new();
        let t = kb.alloc(Term::Const(Literal::String("hello \"world\"".into())));
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "\"hello \\\"world\\\"\"");
    }

    #[test]
    fn print_bool_literal() {
        let mut kb = KnowledgeBase::new();
        let t = kb.alloc(Term::Const(Literal::Bool(true)));
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "true");
    }

    #[test]
    fn print_var() {
        let mut kb = KnowledgeBase::new();
        let sym = kb.intern("x");
        let vid = kb.fresh_var(sym);
        let t = kb.alloc(Term::Var(Var::Global(vid)));
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "?x");
    }

    #[test]
    fn print_nullary_fn() {
        let mut kb = KnowledgeBase::new();
        let t = kb.make_name_term("Account");
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "Account");
    }

    #[test]
    fn print_fn_with_positional_args() {
        let mut kb = KnowledgeBase::new();
        let sym = kb.intern("parent");
        let a = kb.alloc(Term::Const(Literal::String("alice".into())));
        let b = kb.alloc(Term::Const(Literal::String("bob".into())));
        let t = kb.alloc(Term::Fn {
            functor: sym,
            pos_args: SmallVec::from_slice(&[a, b]),
            named_args: SmallVec::new(),
        });
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "parent(\"alice\", \"bob\")");
    }

    #[test]
    fn print_fn_with_named_args() {
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("Account");
        let id_sym = kb.intern("id");
        let name_sym = kb.intern("name");
        let id_val = kb.alloc(Term::Const(Literal::String("A001".into())));
        let name_val = kb.alloc(Term::Const(Literal::String("Savings".into())));
        let t = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(id_sym, id_val), (name_sym, name_val)]),
        });
        let printer = TermPrinter::new(&kb);
        assert_eq!(
            printer.print_term(t),
            "Account(id: \"A001\", name: \"Savings\")"
        );
    }

    #[test]
    fn print_bottom() {
        let mut kb = KnowledgeBase::new();
        let t = kb.alloc(Term::Bottom);
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "bottom");
    }

    #[test]
    fn print_fact_no_meta() {
        let mut kb = KnowledgeBase::new();
        let sym = kb.intern("Eq");
        let t_sym = kb.intern("T");
        let int = kb.make_name_term("Int64");
        let t = kb.alloc(Term::Fn {
            functor: sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(t_sym, int)]),
        });
        let out = print_fact(&kb, t, None);
        assert_eq!(out, "fact Eq(T: Int64)\n");
    }
}
