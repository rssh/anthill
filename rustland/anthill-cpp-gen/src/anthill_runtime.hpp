// anthill_runtime.hpp — runtime support for anthill-emitted C++.
//
// Hand-authored, header-only, C++17. Header-only so it composes with
// any build system; include from generated namespace headers via
//   #include "anthill_runtime.hpp"
//
// Provides SFINAE detection traits — `satisfies_<spec>_v<T>` — that
// answer "does host type T support the operations spec X declares?"
// at compile time. Generated traits-classes can plant
//   static_assert(anthill::runtime::satisfies_indexed_seq_v<C>,
//                 "carrier must support .size() and operator[]");
// to surface mismatches at the obvious site instead of deep inside a
// `std::optional<…>` instantiation.
//
// Conventions:
//   - One trait per anthill prelude typeclass we generate against.
//   - Uses `std::declval<const T&>()` for read-only operations (Eq,
//     Ordered, IndexedSeq) — moved from `T` for value-producing ones
//     (Numeric arithmetic).
//   - `_v` shortcuts mirror std::, callable from `if constexpr`.

#pragma once

#include <cstddef>
#include <type_traits>
#include <utility>

namespace anthill::runtime {

// ── Eq ────────────────────────────────────────────────────────────────
template <typename T, typename = void>
struct satisfies_eq : std::false_type {};

template <typename T>
struct satisfies_eq<T, std::void_t<
    decltype(std::declval<const T&>() == std::declval<const T&>())
>> : std::true_type {};

template <typename T>
inline constexpr bool satisfies_eq_v = satisfies_eq<T>::value;

// ── IndexedSeq ───────────────────────────────────────────────────────
//
// `length(xs)` lowers to `xs.size()`; `nth(xs, i)` lowers to
// `xs[i]` after a bounds check. Match those two operations.
template <typename T, typename = void>
struct satisfies_indexed_seq : std::false_type {};

template <typename T>
struct satisfies_indexed_seq<T, std::void_t<
    decltype(std::declval<const T&>().size()),
    decltype(std::declval<const T&>()[std::declval<std::size_t>()])
>> : std::true_type {};

template <typename T>
inline constexpr bool satisfies_indexed_seq_v = satisfies_indexed_seq<T>::value;

// ── Numeric ──────────────────────────────────────────────────────────
template <typename T, typename = void>
struct satisfies_numeric : std::false_type {};

template <typename T>
struct satisfies_numeric<T, std::void_t<
    decltype(std::declval<const T&>() + std::declval<const T&>()),
    decltype(std::declval<const T&>() - std::declval<const T&>()),
    decltype(std::declval<const T&>() * std::declval<const T&>())
>> : std::true_type {};

template <typename T>
inline constexpr bool satisfies_numeric_v = satisfies_numeric<T>::value;

// ── Ordered ──────────────────────────────────────────────────────────
//
// Uses `<` and `==` — sufficient for the prelude `compare(a, b) -> Int`
// surface; `>`, `>=`, `<=` are derived from those by Ordered's rules.
template <typename T, typename = void>
struct satisfies_ordered : std::false_type {};

template <typename T>
struct satisfies_ordered<T, std::void_t<
    decltype(std::declval<const T&>() < std::declval<const T&>()),
    decltype(std::declval<const T&>() == std::declval<const T&>())
>> : std::true_type {};

template <typename T>
inline constexpr bool satisfies_ordered_v = satisfies_ordered<T>::value;

// ── dependent_false (WI-891) ─────────────────────────────────────────
//
// For an operation body cpp-gen cannot lower, it emits a build-breaking
//   static_assert(::anthill::runtime::dependent_false_v<T>, "<why>");
// in the method body, so a diagnosed gap FAILS the C++ build carrying the
// codegen-time message, instead of the old `return {};` — which COMPILED
// and answered a zero-initialized value, turning a diagnosis into a
// silently wrong program.
//
// Inside a template member a bare `static_assert(false, …)` is ill-formed,
// no diagnostic required, before C++23 (a conforming compiler may accept
// it and miscompile), so cpp-gen keys the assert on an in-scope template
// parameter through this trait: it is always `false`, but — being a
// dependent expression — is evaluated only when the member is
// instantiated, firing the diagnostic exactly then and never eagerly. A
// non-template method uses `static_assert(false, …)` directly and never
// reaches here.
template <typename...>
inline constexpr bool dependent_false_v = false;

}  // namespace anthill::runtime
