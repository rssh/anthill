// anthill_runtime.hpp — runtime support for anthill-emitted C++.
//
// Hand-authored, header-only, C++17. Header-only so it composes with
// any build system; include from generated namespace headers via
//   #include "anthill_runtime.hpp"
//
// Two kinds of thing live here:
//
//   1. SFINAE detection traits — `satisfies_<spec>_v<T>` — that answer
//      "does host type T support the operations spec X declares?" at
//      compile time. Generated traits-classes can plant
//        static_assert(anthill::runtime::satisfies_indexed_seq_v<C>,
//                      "carrier must support .size() and operator[]");
//      to surface mismatches at the obvious site instead of deep inside a
//      `std::optional<…>` instantiation.
//
//   2. Operation REALIZATIONS — `str_*` and friends (WI-890) — the
//      hand-authored C++ backing for primitive operations whose lowering is
//      an algorithm no `$1`/`$2` expression template can carry (scalar-indexed
//      UTF-8, whitespace tables). A carrier's `operation_map` names them
//      (`anthill::runtime::str_length($1)`), and the `anthill::runtime::`
//      `IncludeMapping` probe pulls this header when one appears in emitted C++.
//
// New entries of either kind land here — a new typeclass detection trait, or a
// new host operation whose realization is more than an expression template.
//
// Conventions:
//   - One trait per anthill prelude typeclass we generate against.
//   - Uses `std::declval<const T&>()` for read-only operations (Eq,
//     Ordered, IndexedSeq) — moved from `T` for value-producing ones
//     (Numeric arithmetic).
//   - `_v` shortcuts mirror std::, callable from `if constexpr`.

#pragma once

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

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

// ── String operations (WI-890) ───────────────────────────────────────
//
// `std::string` is BYTES throughout, but `anthill.prelude.String`'s index unit
// is the UNICODE SCALAR (code point) — WI-884 measured that a byte answer makes
// `substring(s, indexOf(s, sub), …)` cut the wrong span on any string with a
// multi-byte prefix. So `length`/`substring`/`indexOf` are scalar-indexed here,
// which is more than an expression template can carry: they, and the operations
// that build a structured result (`replace`/`split`/`trim`/`repeat`) or read an
// operand twice (`endsWith`), are realized by these helpers, named from
// `rustland/anthill-cpp-gen/anthill/string.anthill`'s `operation_map`. The
// semantics each one commits to are argued on the declarations in
// `stdlib/anthill/prelude/string.anthill`; this header reproduces them for
// `std::string`, matching the rust host in `anthill-core/src/eval/builtins.rs`.
//
// The strings anthill hands these helpers are valid UTF-8 (they are anthill
// `String` values), so the decoders trust the encoding; continuation-byte reads
// are still bounds-guarded so a truncated input degrades to a scalar rather than
// an out-of-range access.

// A byte begins a Unicode scalar iff it is not a UTF-8 continuation byte
// (`10xxxxxx`) — the one bit-test every scalar walk below keys on.
inline bool utf8_is_start_byte(char b) {
    return (static_cast<unsigned char>(b) & 0xC0) != 0x80;
}

// The byte length of the scalar whose lead byte is `c0` (1–4), read from the
// high bits — the forward-walk peer of `utf8_is_start_byte`'s backward test.
inline std::size_t utf8_scalar_len(char c0) {
    unsigned char c = static_cast<unsigned char>(c0);
    if (c < 0x80) return 1;
    if ((c & 0xE0) == 0xC0) return 2;
    if ((c & 0xF0) == 0xE0) return 3;
    return 4;
}

// Byte offsets of each Unicode scalar's first byte, with `s.size()` appended as a
// sentinel — so the vector has `scalar_count + 1` entries and scalar `k` spans
// `[starts[k], starts[k+1])`. Used by the helpers that address a scalar BY INDEX
// (`substring`, and the empty-pattern branches of `replace`/`split`); the ones
// that only count (`length`/`indexOf`) or walk the ends (`trim`) avoid it.
inline std::vector<std::size_t> utf8_starts(const std::string& s) {
    std::vector<std::size_t> starts;
    starts.reserve(s.size() + 1);
    for (std::size_t i = 0; i < s.size(); ++i) {
        if (utf8_is_start_byte(s[i])) starts.push_back(i);
    }
    starts.push_back(s.size());
    return starts;
}

// The Unicode scalar beginning at byte offset `i` (a scalar boundary).
inline char32_t utf8_codepoint(const std::string& s, std::size_t i) {
    unsigned char c0 = static_cast<unsigned char>(s[i]);
    auto cont = [&](std::size_t k) -> char32_t {
        return (i + k < s.size())
            ? static_cast<char32_t>(static_cast<unsigned char>(s[i + k]) & 0x3F)
            : char32_t{0};
    };
    if (c0 < 0x80) return c0;
    if ((c0 & 0xE0) == 0xC0) return (char32_t(c0 & 0x1F) << 6) | cont(1);
    if ((c0 & 0xF0) == 0xE0) return (char32_t(c0 & 0x0F) << 12) | (cont(1) << 6) | cont(2);
    return (char32_t(c0 & 0x07) << 18) | (cont(1) << 12) | (cont(2) << 6) | cont(3);
}

// The Unicode `White_Space` property — the set `str::trim` (and thus
// `String.trim`) strips, NOT the ASCII subset. A closed, finite table.
inline bool is_unicode_whitespace(char32_t c) {
    switch (c) {
        case 0x0009: case 0x000A: case 0x000B: case 0x000C: case 0x000D:
        case 0x0020: case 0x0085: case 0x00A0: case 0x1680:
        case 0x2000: case 0x2001: case 0x2002: case 0x2003: case 0x2004:
        case 0x2005: case 0x2006: case 0x2007: case 0x2008: case 0x2009:
        case 0x200A: case 0x2028: case 0x2029: case 0x202F: case 0x205F:
        case 0x3000:
            return true;
        default:
            return false;
    }
}

// length(s) — the count of Unicode scalars (O(1) space, unlike the sentinel
// vector, since only the total is wanted).
inline int64_t str_length(const std::string& s) {
    int64_t n = 0;
    for (char b : s) {
        if (utf8_is_start_byte(b)) ++n;
    }
    return n;
}

// indexOf(s, sub) — the SCALAR index of the first occurrence, -1 if absent, 0
// for sub = "". `std::string::find` answers in BYTES and finds on a scalar
// boundary; the byte offset is converted by counting the scalars before it.
inline int64_t str_index_of(const std::string& s, const std::string& sub) {
    std::size_t byte = s.find(sub);
    if (byte == std::string::npos) return -1;
    int64_t idx = 0;
    for (std::size_t i = 0; i < byte; ++i) {
        if (utf8_is_start_byte(s[i])) ++idx;
    }
    return idx;
}

// substring(s, start, end) — the half-open scalar range [start, end).
// Out-of-range indices CLAMP to the string's bounds and a reversed range gives
// "" — so it is total, matching the rust host's bounds arithmetic exactly.
inline std::string str_substring(const std::string& s, int64_t start, int64_t end) {
    std::vector<std::size_t> starts = utf8_starts(s);
    int64_t n = static_cast<int64_t>(starts.size()) - 1;  // scalar count, always >= 0
    int64_t lo = std::clamp<int64_t>(start, 0, n);
    int64_t hi = std::clamp<int64_t>(end, 0, n);
    if (hi <= lo) return std::string();
    std::size_t lo_b = starts[static_cast<std::size_t>(lo)];
    std::size_t hi_b = starts[static_cast<std::size_t>(hi)];
    return s.substr(lo_b, hi_b - lo_b);
}

// endsWith(s, suffix) — a helper rather than an expression because C++17 has no
// `std::string::ends_with` and the byte-compare reads both operands' sizes.
inline bool str_ends_with(const std::string& s, const std::string& suffix) {
    return s.size() >= suffix.size() &&
           s.compare(s.size() - suffix.size(), suffix.size(), suffix) == 0;
}

// replace(s, old, nw) — EVERY non-overlapping occurrence, left to right. old = ""
// interleaves `nw` at every scalar boundary, ends included (so
// replace("abc", "", "-") = "-a-b-c-").
inline std::string str_replace(const std::string& s, const std::string& old_s,
                               const std::string& nw) {
    std::string out;
    if (old_s.empty()) {
        std::vector<std::size_t> starts = utf8_starts(s);
        for (std::size_t k = 0; k < starts.size(); ++k) {
            out += nw;
            if (k + 1 < starts.size()) {
                out.append(s, starts[k], starts[k + 1] - starts[k]);
            }
        }
        return out;
    }
    std::size_t pos = 0;
    while (true) {
        std::size_t found = s.find(old_s, pos);
        if (found == std::string::npos) {
            out.append(s, pos, s.size() - pos);
            return out;
        }
        out.append(s, pos, found - pos);
        out += nw;
        pos = found + old_s.size();
    }
}

// trim(s) — leading and trailing Unicode whitespace removed. Walks in from each
// END and stops at the first non-space, so it is O(whitespace stripped), not
// O(|s|), and allocates nothing but the result — matching `str::trim`'s cost
// rather than materializing the whole scalar-boundary table for an ends-only job.
inline std::string str_trim(const std::string& s) {
    std::size_t lo = 0;
    while (lo < s.size() && is_unicode_whitespace(utf8_codepoint(s, lo))) {
        lo += utf8_scalar_len(s[lo]);
    }
    std::size_t hi = s.size();
    while (hi > lo) {
        std::size_t p = hi - 1;                          // back up over this scalar's
        while (p > lo && !utf8_is_start_byte(s[p])) --p; // continuation bytes to its lead
        if (!is_unicode_whitespace(utf8_codepoint(s, p))) break;
        hi = p;
    }
    return s.substr(lo, hi - lo);
}

// split(s, sep) — every piece between consecutive separators, EMPTY pieces kept
// (so rejoining with `sep` reproduces `s`). An empty separator matches at every
// scalar boundary: split("abc", "") = ["", "a", "b", "c", ""].
inline std::vector<std::string> str_split(const std::string& s, const std::string& sep) {
    std::vector<std::string> out;
    if (sep.empty()) {
        out.emplace_back();  // leading boundary
        std::vector<std::size_t> starts = utf8_starts(s);
        for (std::size_t k = 0; k + 1 < starts.size(); ++k) {
            out.push_back(s.substr(starts[k], starts[k + 1] - starts[k]));
        }
        out.emplace_back();  // trailing boundary
        return out;
    }
    std::size_t pos = 0;
    while (true) {
        std::size_t found = s.find(sep, pos);
        if (found == std::string::npos) {
            out.push_back(s.substr(pos));
            return out;
        }
        out.push_back(s.substr(pos, found - pos));
        pos = found + sep.size();
    }
}

// repeat(s, n) — n copies concatenated; n <= 0 (or empty `s`) gives "". The
// result size is known, so reserve it up front (as `str::repeat` does) for a
// single allocation — guarded against `size_t` overflow, past which the reserve
// is skipped and the append loop throws on the absurd n, where the rust host
// raises EvalError::Overflow. The two hosts differ only in HOW they refuse.
inline std::string str_repeat(const std::string& s, int64_t n) {
    if (n <= 0 || s.empty()) return std::string();
    std::string out;
    std::size_t reps = static_cast<std::size_t>(n);
    if (reps <= out.max_size() / s.size()) out.reserve(s.size() * reps);
    for (std::size_t k = 0; k < reps; ++k) out += s;
    return out;
}

}  // namespace anthill::runtime
