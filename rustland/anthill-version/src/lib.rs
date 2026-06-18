//! Build-time version stamp shared by Anthill workspace CLIs.
//!
//! The git SHA and build date are baked in at compile time by this crate's
//! `build.rs`. The per-binary name and semver come from the *consuming*
//! crate via [`version_string!`], so every CLI reports its own
//! `name version` line with the shared `(sha date)` provenance suffix:
//!
//! ```text
//! anthill-todo 0.1.0 (c4b469a 2026-06-18T12:34:56Z)
//! ```
//!
//! Motivation (WI-160): a stale binary on `PATH` was previously only
//! diagnosable by diffing file mtimes — the embedded SHA makes the build
//! identifiable directly.

/// Git short SHA of the commit this build was produced from, or `"unknown"`
/// when built outside a git checkout.
pub const GIT_SHA: &str = env!("ANTHILL_VERSION_GIT_SHA");

/// Build date in ISO-8601 UTC (`YYYY-MM-DDTHH:MM:SSZ`).
pub const BUILD_DATE: &str = env!("ANTHILL_VERSION_BUILD_DATE");

/// Assemble the full version line `"<name> <version> (<sha> <date>)"`.
///
/// Prefer the [`version_string!`] macro, which fills `name`/`version` from
/// the calling crate's Cargo metadata. This function is the explicit form
/// for callers that already hold those strings.
pub fn format_version(name: &str, version: &str) -> String {
    format!("{name} {}", format_version_no_name(version))
}

/// The name-less version line `"<version> (<sha> <date>)"`, for front-ends
/// that print the binary name themselves (e.g. clap's `--version`).
pub fn format_version_no_name(version: &str) -> String {
    format!("{version} ({GIT_SHA} {BUILD_DATE})")
}

/// Expand to the *calling crate's* full version line (a `String`).
///
/// `CARGO_PKG_NAME` / `CARGO_PKG_VERSION` are read with `env!` in the
/// caller's compilation, so each binary reports its own name and semver
/// while sharing the build-time SHA/date provenance from this crate.
#[macro_export]
macro_rules! version_string {
    () => {
        $crate::format_version(env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"))
    };
}

/// Expand to the calling crate's name-less version line as a `&'static str`
/// (memoised in a process-lifetime `OnceLock`).
///
/// For clap's `#[command(version = anthill_version::clap_version!())]`:
/// clap requires a `&'static str` (not a runtime `String`) and prints the
/// binary name itself, so the name is omitted to avoid `anthill anthill-cli`.
#[macro_export]
macro_rules! clap_version {
    () => {{
        static VERSION: ::std::sync::OnceLock<::std::string::String> =
            ::std::sync::OnceLock::new();
        VERSION
            .get_or_init(|| $crate::format_version_no_name(env!("CARGO_PKG_VERSION")))
            .as_str()
    }};
}
