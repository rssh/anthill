pub mod cgres {
    use anthill::prelude::{Pair};

    enum Boom {
        Boom {
            why: String,
        },
    }

    enum Two<A, B> {
        Two {
            a: A,
            b: B,
        },
    }

    trait Api {
        fn find(n: i64) -> Option<i64>;

        fn check(n: i64) -> Result<i64, Boom>;

        fn check_all(ns: Vec<i64>) -> Result<Vec<i64>, Boom>;

        fn swap(p: Pair<i64, String>) -> Two<i64, String>;
    }
}
