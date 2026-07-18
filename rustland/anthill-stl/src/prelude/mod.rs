pub mod meta;
pub mod stream;
pub mod logical_stream;

use anthill_core::eval::Value;

pub type List<T> = Vec<T>;
pub use std::option::Option;
pub type Bool = bool;
pub type Int = i64;
pub type Float = f64;
pub type Unit = ();
pub type Pair<A, B> = (A, B);

pub use stream::Stream;
pub use logical_stream::LogicalStream;
pub use meta::Meta;

/// Marker trait paralleling `fact Modifiable[T = X]` in
/// `stdlib/anthill/prelude/effects.anthill` (and per proposal 037 Rule 8).
/// Anthill-side facts assert which types admit `Modify[T]`; this Rust
/// stub exists so the codegen-emitted `use crate::prelude::Modifiable;`
/// (in `filesystem.rs`, `cell.rs`, etc.) resolves. The Rust trait has no
/// methods — runtime dispatch lives in `anthill-core`'s effect-handler /
/// cell-arena machinery, not in trait impls.
pub trait Modifiable {}

/// Opaque host carrier for the kernel `Type` sort (WI-542). The generated
/// reflect subset emits `use crate::prelude::{Type}` from `reflect.anthill`'s
/// imports. In that subset `Type` appears only as an entity/sort REFERENCE —
/// `KB.facts_of(kb, sort: Type)` / `KB.assert(kb, term, sort: Type)` are
/// documented to take the entity "by reference, resolved to its qualified
/// symbol via the caller's import" — so the host carrier wraps that
/// referencing `Value` (e.g. a `Ref(WorkItem)`); the bridge extracts the
/// functor at the impl boundary. (Not the full structural `Type` enum, which
/// the reflect-host subset never needs.)
#[derive(Clone, Debug)]
pub struct Type(Value);

impl Type {
    // Constructs the carrier from an entity-reference Value. The lib path only
    // ever *receives* a `Type` (the bridge never builds one), so the only
    // current callers are the bridge tests — hence `#[cfg(test)]`, which keeps
    // the method's real scope honest. When a non-test caller appears (e.g. a
    // host `KB.assert` call site), the compile error here is the signal to drop
    // the attribute.
    #[cfg(test)]
    pub(crate) fn new(v: Value) -> Self {
        Type(v)
    }
    pub(crate) fn value(&self) -> &Value {
        &self.0
    }
}

/// Opaque host stub for the kernel `TypeExtractor` sort (WI-540). Appears only
/// in the excluded free op `extract`, so it need only exist as a host type.
#[derive(Clone, Debug)]
pub struct TypeExtractor;

/// Opaque host stub for the kernel `FieldOf[T, Name]` type constructor (WI-759),
/// the sibling of `TypeExtractor` above and for the same reason: `reflect.anthill`
/// imports it, so the codegen emits `use crate::prelude::{FieldOf}`, but it appears
/// only in the excluded free op `field_access` — so it need only EXIST as a host
/// type, never carry anything. `FieldOf` is inert by construction: it is reduced by
/// the typer (to the type of `T`'s member named `Name`) and never reaches a runtime
/// value, exactly as `Concat` / `Without` never do.
#[derive(Clone, Debug)]
pub struct FieldOf;
