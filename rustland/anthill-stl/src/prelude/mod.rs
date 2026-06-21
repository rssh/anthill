pub mod meta;
pub mod stream;
pub mod logical_stream;

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

/// Opaque host stubs for the kernel `Type` / `TypeExtractor` sorts (WI-540).
/// The generated reflect subset emits `use crate::prelude::{Type}` /
/// `{TypeExtractor}` from `reflect.anthill`'s imports; these appear only in
/// loud-stubbed (`KB.facts_of` / `assert`) or excluded paths, so they need
/// only exist as a host type.
#[derive(Clone, Debug)]
pub struct Type;

#[derive(Clone, Debug)]
pub struct TypeExtractor;
