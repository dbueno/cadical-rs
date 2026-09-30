//! Port of `config.hpp` and `config.cpp`: pre-defined option
//! configurations.

use crate::options::Options;

struct NameVal {
    name: &'static str,
    val: i32,
}

// Here we have the pre-defined default configurations.

const SAT_CONFIG: &[NameVal] = &[
    NameVal { name: "elimeffort", val: 10 },
    NameVal { name: "stabilizeonly", val: 1 },
    NameVal { name: "subsumeeffort", val: 60 },
];

const UNSAT_CONFIG: &[NameVal] = &[NameVal { name: "stabilize", val: 0 }, NameVal { name: "walk", val: 0 }];

/// `CONFIGS`: (name, description).
const CONFIGS: &[(&str, &str)] = &[
    ("default", "set default advanced internal options"),
    ("plain", "disable all internal preprocessing options"),
    ("sat", "set internal options to target satisfiable instances"),
    ("unsat", "set internal options to target unsatisfiable instances"),
];

const CONFIG_NAMES: &[&str] = &["default", "plain", "sat", "unsat"];

pub struct Config;

impl Config {
    pub fn has(name: &str) -> bool {
        CONFIGS.iter().any(|(n, _)| *n == name)
    }

    pub fn set(opts: &mut Options, name: &str) -> bool {
        if name == "default" {
            opts.reset_default_values();
            return true;
        }
        if name == "plain" {
            opts.disable_preprocessing();
            return true;
        }
        let table: &[NameVal] = match name {
            "sat" => SAT_CONFIG,
            "unsat" => UNSAT_CONFIG,
            _ => return false,
        };
        for p in table {
            debug_assert!(Options::has(p.name).is_some());
            opts.set(p.name, p.val);
        }
        true
    }

    pub fn usage() {
        for (n, d) in CONFIGS {
            cprintf!("  {:<14} {}\n", format!("--{}", n), d);
        }
    }

    /// `Config::begin ()` .. `Config::end ()`: the configuration names.
    pub fn names() -> &'static [&'static str] {
        CONFIG_NAMES
    }
}
