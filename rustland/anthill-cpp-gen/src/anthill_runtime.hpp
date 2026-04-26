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

}  // namespace anthill::runtime
