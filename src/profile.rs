//! Port of `profile.hpp` and `profile.cpp`: built in profiling.
//!
//! Profiles are kept in an array indexed by [`ProfileId`] (declaration
//! order of the C++ `PROFILES` list, `PROFILE_MODE` only entries are not
//! included).  Macros (first argument is the `Internal`, usually `self`):
//!
//! * `start!(self, analyze)` / `stop!(self, analyze)`,
//! * `profile_active!(self, analyze)`,
//! * `start_simplifier!(self, probe, PROBE)` / `stop_simplifier!(...)`
//!   (second argument a profile, third a `Mode` constant name),
//! * `start_inner_walk!(self)`, `stop_inner_walk!(self)`,
//!   `start_outer_walk!(self)`, `stop_outer_walk!(self)`.

use crate::internal::Internal;
use crate::terminal::tout;
use crate::util::percent;

macro_rules! define_profiles {
    ($(($name:ident, $level:expr)),* $(,)?) => {
        /// Identifies one of the profiles (C++ member name of `Profiles`).
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        #[repr(usize)]
        pub enum ProfileId {
            $($name,)*
        }

        /// Number of profiles.
        pub const NUMBER_OF_PROFILES: usize = [$(ProfileId::$name),*].len();

        impl ProfileId {
            pub const ALL: [ProfileId; NUMBER_OF_PROFILES] = [$(ProfileId::$name),*];
        }

        impl Profiles {
            pub fn new(internal: *mut Internal) -> Profiles {
                Profiles {
                    internal,
                    profs: [$(Profile::new(stringify!($name), $level)),*],
                }
            }
        }
    };
}

define_profiles! {
    (analyze, 3),
    (backbone, 2),
    (backward, 3),
    (block, 2),
    (bump, 4),
    (checking, 2),
    (cdcl, 1),
    (collect, 3),
    (compact, 3),
    (condition, 2),
    (congruence, 2),
    (congruencemerge, 4),
    (congruencematching, 4),
    (connect, 3),
    (copy, 4),
    (cover, 2),
    (decide, 3),
    (decompose, 3),
    (definition, 2),
    (elim, 2),
    (factor, 2),
    (fastelim, 2),
    (extend, 3),
    (extract, 3),
    (extractands, 4),
    (extractbinaries, 4),
    (extractites, 4),
    (extractxors, 4),
    (instantiate, 2),
    (lucky, 2),
    (lookahead, 2),
    (minimize, 4),
    (shrink, 4),
    (parse, 0), // As 'opts.profile' might change in parsing
    (probe, 2),
    (deduplicate, 3),
    (propagate, 4),
    (reduce, 3),
    (restart, 3),
    (restore, 2),
    (search, 1),
    (solve, 0),
    (stable, 2),
    (sweep, 2),
    (sweepbackbone, 3),
    (sweepequivalences, 3),
    (sweepflip, 4),
    (sweepimplicant, 4),
    (sweepsolve, 4),
    (preprocess, 2),
    (simplify, 1),
    (subsume, 2),
    (ternary, 2),
    (transred, 3),
    (unstable, 2),
    (vivify, 2),
    (walk, 2),
    (walkpick, 3),
    (walkbreak, 4),
    (walkflip, 3),
    (walkflipbroken, 4),
    (walkflipWL, 4),
    (warmup, 3),
}

#[derive(Clone, Copy, Debug)]
pub struct Profile {
    pub active: bool,
    /// Accumulated time.
    pub value: f64,
    /// Started time if active.
    pub started: f64,
    /// Name of the profiled function (or 'phase').
    pub name: &'static str,
    /// Allows to cheaply test if profiling is enabled.
    pub level: i32,
}

impl Profile {
    pub const fn new(n: &'static str, l: i32) -> Profile {
        Profile { active: false, value: 0.0, started: 0.0, name: n, level: l }
    }
}

pub struct Profiles {
    pub internal: *mut Internal,
    pub profs: [Profile; NUMBER_OF_PROFILES],
}

impl std::ops::Index<ProfileId> for Profiles {
    type Output = Profile;
    #[inline(always)]
    fn index(&self, p: ProfileId) -> &Profile {
        &self.profs[p as usize]
    }
}

impl std::ops::IndexMut<ProfileId> for Profiles {
    #[inline(always)]
    fn index_mut(&mut self, p: ProfileId) -> &mut Profile {
        &mut self.profs[p as usize]
    }
}

/*------------------------------------------------------------------------*/

/// `START (P)`.
#[macro_export]
macro_rules! start {
    ($internal:expr, $p:ident) => {{
        let __p = $crate::profile::ProfileId::$p;
        if $internal.profiles[__p].level <= $internal.opts.profile {
            let __t = $internal.time();
            $internal.start_profiling(__p, __t);
        }
    }};
}

/// `STOP (P)`.
#[macro_export]
macro_rules! stop {
    ($internal:expr, $p:ident) => {{
        let __p = $crate::profile::ProfileId::$p;
        if $internal.profiles[__p].level <= $internal.opts.profile {
            let __t = $internal.time();
            $internal.stop_profiling(__p, __t);
        }
    }};
}

/// `PROFILE_ACTIVE (P)`.
#[macro_export]
macro_rules! profile_active {
    ($internal:expr, $p:ident) => {{
        let __p = $crate::profile::ProfileId::$p;
        $internal.profiles[__p].level <= $internal.opts.profile && $internal.profiles[__p].active
    }};
}

/// `START_SIMPLIFIER (S, M)`.
#[macro_export]
macro_rules! start_simplifier {
    ($internal:expr, $s:ident, $m:ident) => {{
        use $crate::profile::ProfileId as __P;
        let __n = $internal.time();
        let __l = $internal.opts.profile;
        if !$internal.preprocessing && !$internal.lookingahead {
            if $internal.stable && $internal.profiles[__P::stable].level <= __l {
                $internal.stop_profiling(__P::stable, __n);
            }
            if !$internal.stable && $internal.profiles[__P::unstable].level <= __l {
                $internal.stop_profiling(__P::unstable, __n);
            }
            if $internal.profiles[__P::search].level <= __l {
                $internal.stop_profiling(__P::search, __n);
            }
            $internal.reset_mode($crate::internal::Mode::SEARCH);
        }
        if $internal.profiles[__P::simplify].level <= __l {
            $internal.start_profiling(__P::simplify, __n);
        }
        if $internal.profiles[__P::$s].level <= __l {
            $internal.start_profiling(__P::$s, __n);
        }
        $internal.set_mode($crate::internal::Mode::SIMPLIFY);
        $internal.set_mode($crate::internal::Mode::$m);
    }};
}

/// `STOP_SIMPLIFIER (S, M)`.
#[macro_export]
macro_rules! stop_simplifier {
    ($internal:expr, $s:ident, $m:ident) => {{
        use $crate::profile::ProfileId as __P;
        let __n = $internal.time();
        let __l = $internal.opts.profile;
        if $internal.profiles[__P::$s].level <= __l {
            $internal.stop_profiling(__P::$s, __n);
        }
        if $internal.profiles[__P::simplify].level <= __l {
            $internal.stop_profiling(__P::simplify, __n);
        }
        $internal.reset_mode($crate::internal::Mode::$m);
        $internal.reset_mode($crate::internal::Mode::SIMPLIFY);
        if !$internal.preprocessing && !$internal.lookingahead {
            if $internal.profiles[__P::search].level <= __l {
                $internal.start_profiling(__P::search, __n);
            }
            if $internal.stable && $internal.profiles[__P::stable].level <= __l {
                $internal.start_profiling(__P::stable, __n);
            }
            if !$internal.stable && $internal.profiles[__P::unstable].level <= __l {
                $internal.start_profiling(__P::unstable, __n);
            }
            $internal.set_mode($crate::internal::Mode::SEARCH);
        }
    }};
}

/// `START_INNER_WALK ()`: used in 'walk' before calling 'walk_round'
/// within the CDCL loop.
#[macro_export]
macro_rules! start_inner_walk {
    ($internal:expr) => {{
        use $crate::profile::ProfileId as __P;
        $internal.require_mode($crate::internal::Mode::SEARCH);
        debug_assert!(!$internal.preprocessing);
        let __n = $internal.time();
        let __l = $internal.opts.profile;
        if $internal.stable && $internal.profiles[__P::stable].level <= __l {
            $internal.stop_profiling(__P::stable, __n);
        }
        if !$internal.stable && $internal.profiles[__P::unstable].level <= __l {
            $internal.stop_profiling(__P::unstable, __n);
        }
        if $internal.profiles[__P::walk].level <= __l {
            $internal.start_profiling(__P::walk, __n);
        }
        $internal.set_mode($crate::internal::Mode::WALK);
    }};
}

/// `STOP_INNER_WALK ()`: used in 'walk' after calling 'walk_round' within
/// the CDCL loop.
#[macro_export]
macro_rules! stop_inner_walk {
    ($internal:expr) => {{
        use $crate::profile::ProfileId as __P;
        $internal.require_mode($crate::internal::Mode::SEARCH);
        debug_assert!(!$internal.preprocessing);
        $internal.reset_mode($crate::internal::Mode::WALK);
        let __n = $internal.time();
        let __l = $internal.opts.profile;
        if $internal.profiles[__P::walk].level <= __l {
            $internal.stop_profiling(__P::walk, __n);
        }
        if $internal.stable && $internal.profiles[__P::stable].level <= __l {
            $internal.start_profiling(__P::stable, __n);
        }
        if !$internal.stable && $internal.profiles[__P::unstable].level <= __l {
            $internal.start_profiling(__P::unstable, __n);
        }
        $internal.profiles[__P::walk].started = __n;
    }};
}

/// `START_OUTER_WALK ()`: used in 'local_search' before 'walk_round'.
#[macro_export]
macro_rules! start_outer_walk {
    ($internal:expr) => {{
        $internal.require_mode($crate::internal::Mode::SEARCH);
        debug_assert!(!$internal.preprocessing);
        start!($internal, walk);
        $internal.set_mode($crate::internal::Mode::WALK);
    }};
}

/// `STOP_OUTER_WALK ()`: used in 'local_search' after 'walk_round'.
#[macro_export]
macro_rules! stop_outer_walk {
    ($internal:expr) => {{
        $internal.require_mode($crate::internal::Mode::SEARCH);
        debug_assert!(!$internal.preprocessing);
        $internal.reset_mode($crate::internal::Mode::WALK);
        stop!($internal, walk);
    }};
}

/*------------------------------------------------------------------------*/

// Port of 'profile.cpp'.

impl Internal {
    /// (C++ takes `Profile &`, the port takes the profile identifier.)
    pub fn start_profiling(&mut self, profile: ProfileId, s: f64) {
        let level = self.opts.profile;
        let p = &mut self.profiles[profile];
        debug_assert!(p.level <= level);
        debug_assert!(!p.active);
        let _ = level;
        p.started = s;
        p.active = true;
    }

    /// (C++ takes `Profile &`, the port takes the profile identifier.)
    pub fn stop_profiling(&mut self, profile: ProfileId, s: f64) {
        let level = self.opts.profile;
        let p = &mut self.profiles[profile];
        debug_assert!(p.level <= level);
        debug_assert!(p.active);
        let _ = level;
        p.value += s - p.started;
        p.active = false;
    }

    /// Returns 'time ()'.
    pub fn update_profiles(&mut self) -> f64 {
        let now = self.time();
        let level = self.opts.profile;
        for profile in self.profiles.profs.iter_mut() {
            if profile.active {
                debug_assert!(profile.level <= level);
                profile.value += now - profile.started;
                profile.started = now;
            }
        }
        let _ = level;
        now
    }

    /// Accumulated time spent in 'solve ()'.
    pub fn solve_time(&mut self) -> f64 {
        let _ = self.update_profiles();
        self.profiles[ProfileId::solve].value
    }

    pub fn print_profile(&mut self) {
        let now = self.update_profiles();
        let time_type = if self.opts.realtime != 0 { "real" } else { "process" };
        section!(self, "run-time profiling");
        msg!(
            self,
            "{}{} time taken by individual solving procedures{}",
            tout().magenta_code(),
            time_type,
            tout().normal_code()
        );
        msg!(
            self,
            "{}(percentage relative to {} time for solving){}",
            tout().magenta_code(),
            time_type,
            tout().normal_code()
        );
        msg!(self);
        let mut profs: Vec<usize> = Vec::with_capacity(NUMBER_OF_PROFILES);
        for (i, p) in self.profiles.profs.iter().enumerate() {
            if p.level > self.opts.profile {
                continue;
            }
            let id = ProfileId::ALL[i];
            if id == ProfileId::solve {
                continue;
            }
            if p.value == 0.0
                && id != ProfileId::parse
                && id != ProfileId::search
                && id != ProfileId::simplify
            {
                continue;
            }
            profs.push(i);
        }

        // Explicit bubble sort (as in C++, which avoids heap allocation).
        let solve = self.profiles[ProfileId::solve].value;
        let n = profs.len();
        for i in 0..n {
            for j in (i + 1)..n {
                if self.profiles.profs[profs[j]].value > self.profiles.profs[profs[i]].value {
                    profs.swap(i, j);
                }
            }
            let p = &self.profiles.profs[profs[i]];
            msg!(
                self,
                "{} {}% {}",
                crate::format::cfmt_f64("%12.2f", p.value),
                crate::format::cfmt_f64("%7.2f", percent(p.value, solve)),
                p.name
            );
        }

        msg!(self, "  =================================");
        msg!(
            self,
            "{} {}% solve",
            crate::format::cfmt_f64("%12.2f", solve),
            crate::format::cfmt_f64("%7.2f", percent(solve, now))
        );

        msg!(self);
        msg!(
            self,
            "{}last line shows {} time for solving{}",
            tout().magenta_code(),
            time_type,
            tout().normal_code()
        );
        msg!(
            self,
            "{}(percentage relative to total {} time){}",
            tout().magenta_code(),
            time_type,
            tout().normal_code()
        );
    }
}
