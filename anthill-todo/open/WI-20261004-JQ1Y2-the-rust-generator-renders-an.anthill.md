## Attributes

- id: WI-20261004-JQ1Y2-the-rust-generator-renders-an
- created: 2026-10-04T22:29:03Z

- status: Open
- status_agent: claude
- status_at: 2026-10-04T22:29:03Z

- acceptance: cargo-test

- depends_on: WI-20261001-80ZV8-a-bare-parametric-sort-means

## Description

THE RUST GENERATOR RENDERS AN APPLICATION OF THE ENCLOSING SORT BY ITS ARGUMENTS — today `anthill codegen rust` emits Rust's `Self` for every application of the sort being generated, whatever its arguments, so an explicitly DIFFERENT instance is emitted as this one. Filed on the user's word (2026-10-04), found while finishing WI-20261001-80ZV8's stage (e); older than proposal 070.

THE PROGRAM, and what is emitted today (MEASURED 2026-10-04 on the stage (e) tree):

  sort Chain
    sort T = ?
    entity link(item: T, next: Self)
    entity jump(next: Chain[T = Int64])                                 -- next: Box<Chain<T>>          WRONG: a chain of Int64
    operation same(a: Self, b: Chain[T = T]) -> Bool                    -- fn same(&self, b: Self)      right: this instance, written out
    operation other(a: Self, b: Chain[T = Int64]) -> Chain[T = Bool]    -- fn other(&self, b: Self) -> Self      WRONG twice
    operation named[X](a: Self, b: Chain[T = X]) -> Chain[T = X]        -- fn named(&self, b: Self) -> Self      WRONG, and [X] is dropped
    operation first(a: Chain[T = Int64]) -> Int64                       -- fn first(&self) -> i64       WRONG: the receiver is no Chain<T>
  end
  sort Strm
    sort T = ?
    sort E = ?
    operation split(s: Self) -> Option[T = Strm[T = s.T, E = s.E]]      -- fn split(&self) -> Option<Self>     right: the receiver's own parameters
    operation mapped[B](s: Self) -> Strm[T = B, E = E]                  -- fn mapped<B>(&self) -> Self         WRONG: a stream of B
  end

The interpreter reads each of these as written (`Chain[T = Int64]` is a chain of Int64). The generator does not: `type_to_rust_in_sort`'s `Parameterized` arm returns `Self` as soon as the head names the sort (`names_this_sort`), `type_to_rust_for_enum_field` boxes any field whose head names the sort at the sort's own parameters, and `check_self_arg` takes any first parameter whose head names the sort for the receiver (anthill-core/src/codegen/rust.rs). All three ask only for the NAME.

WHAT IT SHOULD EMIT. `Self` where the application IS this instance — every parameter written at the sort's own parameter (`Chain[T = T]`), or at a projection of a receiver typed `Self` (`Strm[T = s.T, E = s.E]`, which is how the stdlib states a result in the receiver's terms). Otherwise the application rendered by its arguments: `b: Chain<i64>`, `-> Chain<bool>`, `next: Box<Chain<i64>>`, `-> Strm<B, E>` (boxed as a trait object where the profile boxes `Self`). That needs two things the generator lacks today: an operation's own type parameters on an IMPL method (`fn named<X>(&self, b: Chain<X>) -> Chain<X>` — `emit_method_signature` emits none, only `emit_trait_method` does), and a first parameter at another instance NOT becoming `&self`.

WHY IT IS A TICKET AND NOT A PATCH. (1) This generator builds the STL crate (anthill-stl/build.rs over stream, logical_stream, meta, reflect, store, filesystem), and hand-written Rust implements the generated traits: `Stream.splitFirst(s: Self) -> Option[Pair[A = s.T, B = Stream[T = s.T, E = s.E]]]` comes out `Box<dyn Stream<T, E>>` BECAUSE of the `Self` rendering, so the receiver-projection case has to be recognised before anything else changes, and the six generated files compared before and after. (2) The trait-object wrapping keys on the rendered STRING `Self` (`wrap_trait_return_in_sort`, `wrap_trait_param`), so a `Strm<B, E>` return needs its own boxing rule. (3) Identity is by LEAF name (`names_this_sort`): a same-leaf sort of another namespace written inside this one is taken for it — scaland's generator fixed the same thing in WI-1081 (a written prefix is honoured), and the fix here should take that with it.

RELATED. WI-20261001-80ZV8 stage (e) made this generator REFUSE a reference that leaves the sort's own parameter OPEN (bare name, partial application, anonymous `?`); its refusal offers only `Self`, deliberately, because the named repair the typer offers (`[X]`, `Chain[T = X]`) is exactly what this ticket's bug mis-renders — once fixed, that refusal can offer it too. scaland's generator already renders an explicit application of the enclosing sort by its arguments (TypeGen, `Placement.Enclosing` with arguments), so rustland is the one behind. WI-586 (per-op generics colliding with the trait's) and WI-1108 (a parameterized spec claim rendered as a bare supertrait) touch the same emitters.

ACCEPTANCE. Each line of the program above generates what its comment says it should, and each is a row that names its text: another instance in a parameter, in a return and in an enum field; an operation's own type parameter on an impl method; a first parameter at another instance that is no receiver. CONTROLS: the sort's own parameters written out is `Self`; a receiver's projections are `Self`, and the STL crate builds with its six generated files byte-identical — or changed on purpose with the hand-written implementations beside them. Each row says which rows fail when its part is backed out. docs/rust-forward-mapping.md's "Self substitution" paragraph drops its "known inaccuracy" sentence.

