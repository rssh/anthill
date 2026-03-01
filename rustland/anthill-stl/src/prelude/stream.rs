#![allow(unused_imports)]

use crate::prelude::{Pair};

pub trait Stream<T, E> {
    fn split_first(&self) -> Result<Option<Pair<T, Box<dyn Stream<T, E>>>>, E>;

    fn head(&self) -> Result<Option<T>, E>;

    fn tail(&self) -> Result<Box<dyn Stream<T, E>>, E>;

    fn take_n(&self, n: i64) -> Result<Vec<T>, E>;

    fn collect_all(&self) -> Result<Vec<T>, E>;

    fn is_empty(&self) -> Result<bool, E>;
}
