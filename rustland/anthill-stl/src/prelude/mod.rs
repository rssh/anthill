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
