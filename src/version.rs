//! Port of `version.hpp` and `version.cpp`.
//!
//! The C++ build generates `build.hpp` with `VERSION`, `IDENTIFIER`,
//! `COMPILER`, `FLAGS` and `DATE`.  Here the version is fixed, the other
//! values can be provided at compile time through the environment
//! variables `CADICAL_RS_IDENTIFIER`, `CADICAL_RS_COMPILER`,
//! `CADICAL_RS_FLAGS` and `CADICAL_RS_DATE` (otherwise they are unknown,
//! i.e., `None`, like the C++ '0' strings).

pub const VERSION: &str = "3.0.1";

const COPYRIGHT: &str = "Copyright (c) 2016-2026";
const AUTHORS: &str = "A. Biere, M. Fleury, N. Froleyks, K. Fazekas, F. Pollitt, T. Faller";
const AFFILIATIONS: &str = "JKU Linz, University of Freiburg, TU Wien";

pub fn version() -> &'static str {
    VERSION
}
pub fn copyright() -> &'static str {
    COPYRIGHT
}
pub fn authors() -> &'static str {
    AUTHORS
}
pub fn affiliations() -> &'static str {
    AFFILIATIONS
}
/// `"cadical-" VERSION SHORTIDSTR` (no short git identifier).
pub fn signature() -> &'static str {
    "cadical-3.0.1"
}
pub fn identifier() -> Option<&'static str> {
    option_env!("CADICAL_RS_IDENTIFIER")
}
pub fn compiler() -> Option<&'static str> {
    Some(option_env!("CADICAL_RS_COMPILER").unwrap_or("rustc"))
}
pub fn date() -> Option<&'static str> {
    option_env!("CADICAL_RS_DATE")
}
pub fn flags() -> Option<&'static str> {
    option_env!("CADICAL_RS_FLAGS")
}
