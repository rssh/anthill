#![allow(unused_imports)]

use crate::prelude::{Pair};
use crate::prelude::stream::Stream;

pub trait LogicalStream<T>: Stream<T, ()> + Sized {
    fn empty() -> Self;

    fn pure_val(x: T) -> Self;

    fn mplus(&self, b: &Self) -> Self;

    fn guard(cond: bool) -> Self;

    fn interleave(&self, b: &Self) -> Self;
}
