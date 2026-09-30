//! Port of `stable.cpp`.
//!
//! Only contains code if `PROFILE_MODE` is defined (`propagate_stable`,
//! `analyze_stable`, `decide_stable`), which is not supported by the Rust
//! port (`propagate_wrapper`, `analyze_wrapper` and `decide_wrapper` are
//! plain `propagate`, `analyze` and `decide`).
