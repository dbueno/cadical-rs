//! Port of `stats.hpp` and `stats.cpp` (the statistics counters).
//!
//! The anonymous nested C++ structs are named `Stats<Member>` here.  The
//! printing code (`Stats::print` in `stats.cpp`) is a stub to be ported.

use crate::internal::Internal;
use crate::resources::{absolute_process_time, absolute_real_time};

#[derive(Clone, Debug)]
pub struct StatsPropagations {
    pub cover: i64,
    pub instantiate: i64,
    pub probe: i64,
    pub search: i64,
    pub transred: i64,
    pub vivify: i64,
    pub backbone: i64,
}

impl Default for StatsPropagations {
    fn default() -> Self {
        StatsPropagations {
            cover: 0 as i64,
            instantiate: 0 as i64,
            probe: 0 as i64,
            search: 0 as i64,
            transred: 0 as i64,
            vivify: 0 as i64,
            backbone: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsTicks {
    pub search: [i64; 2],
    pub backbone: i64,
    pub factor: i64,
    pub probe: i64,
    pub sweep: i64,
    pub ternary: i64,
    pub vivify: i64,
    pub walk: i64,
    pub walkflip: i64,
    pub walkflipbroken: i64,
    pub walkflipWL: i64,
    pub walkbreak: i64,
    pub walkpick: i64,
}

impl Default for StatsTicks {
    fn default() -> Self {
        StatsTicks {
            search: [0 as i64; 2],
            backbone: 0 as i64,
            factor: 0 as i64,
            probe: 0 as i64,
            sweep: 0 as i64,
            ternary: 0 as i64,
            vivify: 0 as i64,
            walk: 0 as i64,
            walkflip: 0 as i64,
            walkflipbroken: 0 as i64,
            walkflipWL: 0 as i64,
            walkbreak: 0 as i64,
            walkpick: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsExtProp {
    pub ext_cb: i64,
    pub eprop_call: i64,
    pub eprop_prop: i64,
    pub eprop_conf: i64,
    pub eprop_expl: i64,
    pub elearn_call: i64,
    pub elearned: i64,
    pub elearn_prop: i64,
    pub elearn_ooo: i64,
    pub elearn_elevate: i64,
    pub elearn_unit: i64,
    pub elearn_conf: i64,
    pub echeck_call: i64,
}

impl Default for StatsExtProp {
    fn default() -> Self {
        StatsExtProp {
            ext_cb: 0 as i64,
            eprop_call: 0 as i64,
            eprop_prop: 0 as i64,
            eprop_conf: 0 as i64,
            eprop_expl: 0 as i64,
            elearn_call: 0 as i64,
            elearned: 0 as i64,
            elearn_prop: 0 as i64,
            elearn_ooo: 0 as i64,
            elearn_elevate: 0 as i64,
            elearn_unit: 0 as i64,
            elearn_conf: 0 as i64,
            echeck_call: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsMark {
    pub block: i64,
    pub elim: i64,
    pub subsume: i64,
    pub ternary: i64,
    pub factor: i64,
}

impl Default for StatsMark {
    fn default() -> Self {
        StatsMark {
            block: 0 as i64,
            elim: 0 as i64,
            subsume: 0 as i64,
            ternary: 0 as i64,
            factor: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsClauses {
    pub total: i64,
    pub redundant: i64,
    pub irredundant: i64,
}

impl Default for StatsClauses {
    fn default() -> Self {
        StatsClauses {
            total: 0 as i64,
            redundant: 0 as i64,
            irredundant: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsTime {
    pub process: f64,
    pub real: f64,
}

impl Default for StatsTime {
    fn default() -> Self {
        StatsTime {
            process: 0 as f64,
            real: 0 as f64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsCover {
    pub count: i64,
    pub asymmetric: i64,
    pub blocked: i64,
    pub total: i64,
}

impl Default for StatsCover {
    fn default() -> Self {
        StatsCover {
            count: 0 as i64,
            asymmetric: 0 as i64,
            blocked: 0 as i64,
            total: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsLuckyOneZero {
    pub one: i64,
    pub zero: i64,
}

impl Default for StatsLuckyOneZero {
    fn default() -> Self {
        StatsLuckyOneZero {
            one: 0 as i64,
            zero: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsLuckyHorn {
    pub positive: i64,
    pub negative: i64,
}

impl Default for StatsLuckyHorn {
    fn default() -> Self {
        StatsLuckyHorn {
            positive: 0 as i64,
            negative: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsLucky {
    pub tried: i64,
    pub succeeded: i64,
    pub constant: StatsLuckyOneZero,
    pub forward: StatsLuckyOneZero,
    pub backward: StatsLuckyOneZero,
    pub horn: StatsLuckyHorn,
}

impl Default for StatsLucky {
    fn default() -> Self {
        StatsLucky {
            tried: 0 as i64,
            succeeded: 0 as i64,
            constant: StatsLuckyOneZero::default(),
            forward: StatsLuckyOneZero::default(),
            backward: StatsLuckyOneZero::default(),
            horn: StatsLuckyHorn::default(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsRephased {
    pub total: i64,
    pub best: i64,
    pub flipped: i64,
    pub inverted: i64,
    pub original: i64,
    pub random: i64,
    pub walk: i64,
}

impl Default for StatsRephased {
    fn default() -> Self {
        StatsRephased {
            total: 0 as i64,
            best: 0 as i64,
            flipped: 0 as i64,
            inverted: 0 as i64,
            original: 0 as i64,
            random: 0 as i64,
            walk: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsWarmup {
    pub decision: i64,
    pub dummydecision: i64,
    pub conflicts: i64,
    pub propagated: i64,
    pub count: i64,
}

impl Default for StatsWarmup {
    fn default() -> Self {
        StatsWarmup {
            decision: 0 as i64,
            dummydecision: 0 as i64,
            conflicts: 0 as i64,
            propagated: 0 as i64,
            count: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsWalk {
    pub count: i64,
    pub broken: i64,
    pub flips: i64,
    pub minimum: i64,
    pub improved: i64,
}

impl Default for StatsWalk {
    fn default() -> Self {
        StatsWalk {
            count: 0 as i64,
            broken: 0 as i64,
            flips: 0 as i64,
            minimum: 0 as i64,
            improved: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsFlush {
    pub count: i64,
    pub learned: i64,
    pub hyper: i64,
}

impl Default for StatsFlush {
    fn default() -> Self {
        StatsFlush {
            count: 0 as i64,
            learned: 0 as i64,
            hyper: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsLearned {
    pub literals: i64,
    pub clauses: i64,
}

impl Default for StatsLearned {
    fn default() -> Self {
        StatsLearned {
            literals: 0 as i64,
            clauses: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsGarbage {
    pub bytes: i64,
    pub clauses: i64,
    pub literals: i64,
}

impl Default for StatsGarbage {
    fn default() -> Self {
        StatsGarbage {
            bytes: 0 as i64,
            clauses: 0 as i64,
            literals: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsVars {
    pub fixed: i64,
    pub eliminated: i64,
    pub fasteliminated: i64,
    pub substituted: i64,
    pub pure: i64,
}

impl Default for StatsVars {
    fn default() -> Self {
        StatsVars {
            fixed: 0 as i64,
            eliminated: 0 as i64,
            fasteliminated: 0 as i64,
            substituted: 0 as i64,
            pure: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsOtfs {
    pub strengthened: i64,
    pub subsumed: i64,
}

impl Default for StatsOtfs {
    fn default() -> Self {
        StatsOtfs {
            strengthened: 0 as i64,
            subsumed: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsRandec {
    pub random_decisions: i64,
    pub random_decision_phases: i64,
}

impl Default for StatsRandec {
    fn default() -> Self {
        StatsRandec {
            random_decisions: 0 as i64,
            random_decision_phases: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsCongruence {
    pub gates: i64,
    pub and_gates: i64,
    pub ands: i64,
    pub ite_gates: i64,
    pub ites: i64,
    pub xor_gates: i64,
    pub xors: i64,
    pub units: i64,
    pub congruent: i64,
    pub rounds: i64,
    pub unary_and: i64,
    pub unaries: i64,
    pub rewritten_ands: i64,
    pub rewritten_xors: i64,
    pub rewritten_ites: i64,
    pub simplified: i64,
    pub simplified_ands: i64,
    pub simplified_xors: i64,
    pub simplified_ites: i64,
    pub subsumed: i64,
    pub trivial_ite: i64,
    pub unary_ites: i64,
}

impl Default for StatsCongruence {
    fn default() -> Self {
        StatsCongruence {
            gates: 0 as i64,
            and_gates: 0 as i64,
            ands: 0 as i64,
            ite_gates: 0 as i64,
            ites: 0 as i64,
            xor_gates: 0 as i64,
            xors: 0 as i64,
            units: 0 as i64,
            congruent: 0 as i64,
            rounds: 0 as i64,
            unary_and: 0 as i64,
            unaries: 0 as i64,
            rewritten_ands: 0 as i64,
            rewritten_xors: 0 as i64,
            rewritten_ites: 0 as i64,
            simplified: 0 as i64,
            simplified_ands: 0 as i64,
            simplified_xors: 0 as i64,
            simplified_ites: 0 as i64,
            subsumed: 0 as i64,
            trivial_ite: 0 as i64,
            unary_ites: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StatsBackbone {
    pub rounds: i64,
    pub units: i64,
    pub phases: i64,
    pub probes: i64,
}

impl Default for StatsBackbone {
    fn default() -> Self {
        StatsBackbone {
            rounds: 0 as i64,
            units: 0 as i64,
            phases: 0 as i64,
            probes: 0 as i64,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Stats {
    pub internal: *mut Internal,
    pub vars: i64,
    pub conflicts: i64,
    pub decisions: i64,
    pub searches: i64,
    pub propagations: StatsPropagations,
    pub ticks: StatsTicks,
    pub ext_prop: StatsExtProp,
    pub condassinit: i64,
    pub condassirem: i64,
    pub condassrem: i64,
    pub condassvars: i64,
    pub condautinit: i64,
    pub condautrem: i64,
    pub condcands: i64,
    pub condcondinit: i64,
    pub condcondrem: i64,
    pub conditioned: i64,
    pub conditionings: i64,
    pub condprops: i64,
    pub mark: StatsMark,
    pub current: StatsClauses,
    pub added: StatsClauses,
    pub time: StatsTime,
    pub cover: StatsCover,
    pub lucky: StatsLucky,
    pub rephased: StatsRephased,
    pub warmup: StatsWarmup,
    pub walk: StatsWalk,
    pub flush: StatsFlush,
    pub compacts: i64,
    pub shuffled: i64,
    pub restarts: i64,
    pub restartlevels: i64,
    pub restartstable: i64,
    pub stabphases: i64,
    pub stabconflicts: i64,
    pub rescored: i64,
    pub reused: i64,
    pub reusedlevels: i64,
    pub reusedstable: i64,
    pub sections: i64,
    pub chrono: i64,
    pub backtracks: i64,
    pub improvedglue: i64,
    pub promoted1: i64,
    pub promoted2: i64,
    pub bumped: i64,
    pub recomputed: i64,
    pub searched: i64,
    pub reductions: i64,
    pub reduced: i64,
    pub reduced_sqrt: i64,
    pub reduced_prct: i64,
    pub collected: i64,
    pub collections: i64,
    pub hbrs: i64,
    pub hbrsizes: i64,
    pub hbreds: i64,
    pub hbrsubs: i64,
    pub instried: i64,
    pub instantiated: i64,
    pub instrounds: i64,
    pub subsumed: i64,
    pub deduplicated: i64,
    pub deduplicatedinit: i64,
    pub deduplicatedinitrounds: i64,
    pub deduplications: i64,
    pub strengthened: i64,
    pub eliminated_equi: i64,
    pub eliminated_and: i64,
    pub eliminated_ite: i64,
    pub eliminated_xor: i64,
    pub eliminated_def: i64,
    pub definitions_checked: i64,
    pub definitions_extracted: i64,
    pub definition_units: i64,
    pub definition_ticks: i64,
    pub factor: i64,
    pub factored: i64,
    pub factor_added: i64,
    pub variables_extension: i64,
    pub variables_original: i64,
    pub literals_factored: i64,
    pub clauses_unfactored: i64,
    pub literals_unfactored: i64,
    pub elimotfstr: i64,
    pub subirr: i64,
    pub subred: i64,
    pub subtried: i64,
    pub subchecks: i64,
    pub subchecks2: i64,
    pub elimotfsub: i64,
    pub subsumerounds: i64,
    pub subsumephases: i64,
    pub eagertried: i64,
    pub eagersub: i64,
    pub elimres: i64,
    pub elimrestried: i64,
    pub elimfastrounds: i64,
    pub elimrounds: i64,
    pub elimphases: i64,
    pub elimfastphases: i64,
    pub elimcompleted: i64,
    pub elimtried: i64,
    pub elimsubst: i64,
    pub elimgates: i64,
    pub elimequivs: i64,
    pub elimands: i64,
    pub elimites: i64,
    pub elimxors: i64,
    pub elimbwsub: i64,
    pub elimbwstr: i64,
    pub ternary: i64,
    pub ternres: i64,
    pub htrs: i64,
    pub htrs2: i64,
    pub htrs3: i64,
    pub decompositions: i64,
    pub vivifications: i64,
    pub vivifychecks: i64,
    pub vivifiedirred: i64,
    pub vivifiedtier1: i64,
    pub vivifiedtier2: i64,
    pub vivifiedtier3: i64,
    pub vivifydecs: i64,
    pub vivifyflushed: i64,
    pub vivifyreused: i64,
    pub vivifysched: i64,
    pub vivifysubs: i64,
    pub vivifysubred: i64,
    pub vivifysubirr: i64,
    pub vivifystrs: i64,
    pub vivifystrirr: i64,
    pub vivifystred1: i64,
    pub vivifystred2: i64,
    pub vivifystred3: i64,
    pub vivifyunits: i64,
    pub vivifyimplied: i64,
    pub vivifyinst: i64,
    pub vivifydemote: i64,
    pub transreds: i64,
    pub transitive: i64,
    pub learned: StatsLearned,
    pub minimized: i64,
    pub shrunken: i64,
    pub minishrunken: i64,
    pub irrlits: i64,
    pub garbage: StatsGarbage,
    pub sweep_units: i64,
    pub sweep_flip_backbone: i64,
    pub sweep_fixed_backbone: i64,
    pub sweep_flipped_backbone: i64,
    pub sweep_solved_backbone: i64,
    pub sweep_sat_backbone: i64,
    pub sweep_unsat_backbone: i64,
    pub sweep_unknown_backbone: i64,
    pub sweep_flip_equivalences: i64,
    pub sweep_flipped_equivalences: i64,
    pub sweep_sat_equivalences: i64,
    pub sweep_unsat_equivalences: i64,
    pub sweep_unknown_equivalences: i64,
    pub sweep_solved_equivalences: i64,
    pub sweep_equivalences: i64,
    pub sweep_variables: i64,
    pub sweep_completed: i64,
    pub sweep_solved: i64,
    pub sweep_sat: i64,
    pub sweep_unsat: i64,
    pub sweep_depth: i64,
    pub sweep_environment: i64,
    pub sweep_clauses: i64,
    pub sweep: i64,
    pub units: i64,
    pub binaries: i64,
    pub inprobingphases: i64,
    pub probingrounds: i64,
    pub inprobesuccess: i64,
    pub probed: i64,
    pub failed: i64,
    pub hyperunary: i64,
    pub probefailed: i64,
    pub transredunits: i64,
    pub blockings: i64,
    pub blocked: i64,
    pub blockres: i64,
    pub blockcands: i64,
    pub blockpured: i64,
    pub blockpurelits: i64,
    pub extensions: i64,
    pub extended: i64,
    pub weakened: i64,
    pub weakenedlen: i64,
    pub restorations: i64,
    pub restored: i64,
    pub reactivated: i64,
    pub restoredlits: i64,
    pub preprocessings: i64,
    pub ilbtriggers: i64,
    pub ilbsuccess: i64,
    pub levelsreused: i64,
    pub literalsreused: i64,
    pub assumptionsreused: i64,
    pub tierecomputed: i64,
    pub all: StatsVars,
    pub now: StatsVars,
    pub otfs: StatsOtfs,
    pub unused: i64,
    pub active: i64,
    pub inactive: i64,
    pub incremental_decay: i64,
    pub randec: StatsRandec,
    pub bump_used: Vec<u64>,
    pub used: Vec<Vec<u64>>,
    pub congruence: StatsCongruence,
    pub backbone: StatsBackbone,
}

impl Default for Stats {
    fn default() -> Self {
        Stats {
            internal: std::ptr::null_mut(),
            vars: 0 as i64,
            conflicts: 0 as i64,
            decisions: 0 as i64,
            searches: 0 as i64,
            propagations: StatsPropagations::default(),
            ticks: StatsTicks::default(),
            ext_prop: StatsExtProp::default(),
            condassinit: 0 as i64,
            condassirem: 0 as i64,
            condassrem: 0 as i64,
            condassvars: 0 as i64,
            condautinit: 0 as i64,
            condautrem: 0 as i64,
            condcands: 0 as i64,
            condcondinit: 0 as i64,
            condcondrem: 0 as i64,
            conditioned: 0 as i64,
            conditionings: 0 as i64,
            condprops: 0 as i64,
            mark: StatsMark::default(),
            current: StatsClauses::default(),
            added: StatsClauses::default(),
            time: StatsTime::default(),
            cover: StatsCover::default(),
            lucky: StatsLucky::default(),
            rephased: StatsRephased::default(),
            warmup: StatsWarmup::default(),
            walk: StatsWalk::default(),
            flush: StatsFlush::default(),
            compacts: 0 as i64,
            shuffled: 0 as i64,
            restarts: 0 as i64,
            restartlevels: 0 as i64,
            restartstable: 0 as i64,
            stabphases: 0 as i64,
            stabconflicts: 0 as i64,
            rescored: 0 as i64,
            reused: 0 as i64,
            reusedlevels: 0 as i64,
            reusedstable: 0 as i64,
            sections: 0 as i64,
            chrono: 0 as i64,
            backtracks: 0 as i64,
            improvedglue: 0 as i64,
            promoted1: 0 as i64,
            promoted2: 0 as i64,
            bumped: 0 as i64,
            recomputed: 0 as i64,
            searched: 0 as i64,
            reductions: 0 as i64,
            reduced: 0 as i64,
            reduced_sqrt: 0 as i64,
            reduced_prct: 0 as i64,
            collected: 0 as i64,
            collections: 0 as i64,
            hbrs: 0 as i64,
            hbrsizes: 0 as i64,
            hbreds: 0 as i64,
            hbrsubs: 0 as i64,
            instried: 0 as i64,
            instantiated: 0 as i64,
            instrounds: 0 as i64,
            subsumed: 0 as i64,
            deduplicated: 0 as i64,
            deduplicatedinit: 0 as i64,
            deduplicatedinitrounds: 0 as i64,
            deduplications: 0 as i64,
            strengthened: 0 as i64,
            eliminated_equi: 0 as i64,
            eliminated_and: 0 as i64,
            eliminated_ite: 0 as i64,
            eliminated_xor: 0 as i64,
            eliminated_def: 0 as i64,
            definitions_checked: 0 as i64,
            definitions_extracted: 0 as i64,
            definition_units: 0 as i64,
            definition_ticks: 0 as i64,
            factor: 0 as i64,
            factored: 0 as i64,
            factor_added: 0 as i64,
            variables_extension: 0 as i64,
            variables_original: 0 as i64,
            literals_factored: 0 as i64,
            clauses_unfactored: 0 as i64,
            literals_unfactored: 0 as i64,
            elimotfstr: 0 as i64,
            subirr: 0 as i64,
            subred: 0 as i64,
            subtried: 0 as i64,
            subchecks: 0 as i64,
            subchecks2: 0 as i64,
            elimotfsub: 0 as i64,
            subsumerounds: 0 as i64,
            subsumephases: 0 as i64,
            eagertried: 0 as i64,
            eagersub: 0 as i64,
            elimres: 0 as i64,
            elimrestried: 0 as i64,
            elimfastrounds: 0 as i64,
            elimrounds: 0 as i64,
            elimphases: 0 as i64,
            elimfastphases: 0 as i64,
            elimcompleted: 0 as i64,
            elimtried: 0 as i64,
            elimsubst: 0 as i64,
            elimgates: 0 as i64,
            elimequivs: 0 as i64,
            elimands: 0 as i64,
            elimites: 0 as i64,
            elimxors: 0 as i64,
            elimbwsub: 0 as i64,
            elimbwstr: 0 as i64,
            ternary: 0 as i64,
            ternres: 0 as i64,
            htrs: 0 as i64,
            htrs2: 0 as i64,
            htrs3: 0 as i64,
            decompositions: 0 as i64,
            vivifications: 0 as i64,
            vivifychecks: 0 as i64,
            vivifiedirred: 0 as i64,
            vivifiedtier1: 0 as i64,
            vivifiedtier2: 0 as i64,
            vivifiedtier3: 0 as i64,
            vivifydecs: 0 as i64,
            vivifyflushed: 0 as i64,
            vivifyreused: 0 as i64,
            vivifysched: 0 as i64,
            vivifysubs: 0 as i64,
            vivifysubred: 0 as i64,
            vivifysubirr: 0 as i64,
            vivifystrs: 0 as i64,
            vivifystrirr: 0 as i64,
            vivifystred1: 0 as i64,
            vivifystred2: 0 as i64,
            vivifystred3: 0 as i64,
            vivifyunits: 0 as i64,
            vivifyimplied: 0 as i64,
            vivifyinst: 0 as i64,
            vivifydemote: 0 as i64,
            transreds: 0 as i64,
            transitive: 0 as i64,
            learned: StatsLearned::default(),
            minimized: 0 as i64,
            shrunken: 0 as i64,
            minishrunken: 0 as i64,
            irrlits: 0 as i64,
            garbage: StatsGarbage::default(),
            sweep_units: 0 as i64,
            sweep_flip_backbone: 0 as i64,
            sweep_fixed_backbone: 0 as i64,
            sweep_flipped_backbone: 0 as i64,
            sweep_solved_backbone: 0 as i64,
            sweep_sat_backbone: 0 as i64,
            sweep_unsat_backbone: 0 as i64,
            sweep_unknown_backbone: 0 as i64,
            sweep_flip_equivalences: 0 as i64,
            sweep_flipped_equivalences: 0 as i64,
            sweep_sat_equivalences: 0 as i64,
            sweep_unsat_equivalences: 0 as i64,
            sweep_unknown_equivalences: 0 as i64,
            sweep_solved_equivalences: 0 as i64,
            sweep_equivalences: 0 as i64,
            sweep_variables: 0 as i64,
            sweep_completed: 0 as i64,
            sweep_solved: 0 as i64,
            sweep_sat: 0 as i64,
            sweep_unsat: 0 as i64,
            sweep_depth: 0 as i64,
            sweep_environment: 0 as i64,
            sweep_clauses: 0 as i64,
            sweep: 0 as i64,
            units: 0 as i64,
            binaries: 0 as i64,
            inprobingphases: 0 as i64,
            probingrounds: 0 as i64,
            inprobesuccess: 0 as i64,
            probed: 0 as i64,
            failed: 0 as i64,
            hyperunary: 0 as i64,
            probefailed: 0 as i64,
            transredunits: 0 as i64,
            blockings: 0 as i64,
            blocked: 0 as i64,
            blockres: 0 as i64,
            blockcands: 0 as i64,
            blockpured: 0 as i64,
            blockpurelits: 0 as i64,
            extensions: 0 as i64,
            extended: 0 as i64,
            weakened: 0 as i64,
            weakenedlen: 0 as i64,
            restorations: 0 as i64,
            restored: 0 as i64,
            reactivated: 0 as i64,
            restoredlits: 0 as i64,
            preprocessings: 0 as i64,
            ilbtriggers: 0 as i64,
            ilbsuccess: 0 as i64,
            levelsreused: 0 as i64,
            literalsreused: 0 as i64,
            assumptionsreused: 0 as i64,
            tierecomputed: 0 as i64,
            all: StatsVars::default(),
            now: StatsVars::default(),
            otfs: StatsOtfs::default(),
            unused: 0 as i64,
            active: 0 as i64,
            inactive: 0 as i64,
            incremental_decay: 0 as i64,
            randec: StatsRandec::default(),
            bump_used: vec![0, 0],
            used: Vec::new(),
            congruence: StatsCongruence::default(),
            backbone: StatsBackbone::default(),
        }
    }
}

impl Stats {
    /// `Stats ()`.
    pub fn new() -> Stats {
        let mut s = Stats::default();
        s.time.real = absolute_real_time();
        s.time.process = absolute_process_time();
        s.walk.minimum = i64::MAX; // LONG_MAX
        s.used.resize(2, Vec::new());
        s.used[0].resize(127, 0);
        s.used[1].resize(127, 0);
        s
    }
}


/*------------------------------------------------------------------------*/
// Port of the functions defined in 'stats.cpp' ('Checker::print_stats' and
// 'LratChecker::print_stats' live in 'checker.rs' / 'lratchecker.rs').

#[allow(unused_imports)]
use crate::prelude::*;
use crate::format::cfmt_f64;
use crate::resources::maximum_resident_set_size;
use crate::terminal::tout;

impl Stats {
    /// C++ `void Stats::print (Internal *)` is a member function but only
    /// uses `internal->stats`; an associated function avoids aliasing.
    /// (`factored` in the C++ code is the member `this->factored`, i.e.,
    /// `internal->stats.factored`.)
    #[rustfmt::skip]
    pub fn print(internal: &mut Internal) {
        #[allow(unused_mut)]
        let mut all = internal.opts.verbose > 0 || internal.opts.stats != 0;
        #[cfg(feature = "logging")]
        if internal.opts.log != 0 {
            all = true;
        }

        if internal.opts.profile != 0 {
            internal.print_profile();
        }

        let t = internal.solve_time();

        let stats = &internal.stats;

        let mut propagations: i64 = 0;
        propagations += stats.propagations.cover;
        propagations += stats.propagations.probe;
        propagations += stats.propagations.search;
        propagations += stats.propagations.transred;
        propagations += stats.propagations.vivify;

        let vivified: i64 = stats.vivifysubs + stats.vivifystrs;
        let searchticks: i64 = stats.ticks.search[0] + stats.ticks.search[1];
        let inprobeticks: i64 = stats.ticks.vivify + stats.ticks.probe
            + stats.ticks.factor + stats.ticks.ternary
            + stats.ticks.sweep + stats.ticks.backbone;
        let totalticks: i64 = searchticks + inprobeticks;

        let mut extendbytes: usize = internal.external().extension.len();
        extendbytes *= std::mem::size_of::<i32>();

        section!(internal, "statistics");

        let stats = &internal.stats;

        macro_rules! prt {
            ($fmt:literal $(, $arg:expr)* $(,)?) => {
                if !($fmt.as_bytes()[0] == b' ' && !all) {
                    msg!(internal, $fmt $(, $arg)*);
                }
            };
        }

      if all || stats.blocked != 0 {
        prt!("blocked:         {:15}   {} %  of irredundant clauses", stats.blocked, cfmt_f64("%10.2f", percent((stats.blocked) as f64, (stats.added.irredundant) as f64)));
        prt!("  blockings:     {:15}   {}    internal", stats.blockings, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.blockings) as f64)));
        prt!("  candidates:    {:15}   {}    per blocking ", stats.blockcands, cfmt_f64("%10.2f", relative((stats.blockcands) as f64, (stats.blockings) as f64)));
        prt!("  blockres:      {:15}   {}    per candidate", stats.blockres, cfmt_f64("%10.2f", relative((stats.blockres) as f64, (stats.blockcands) as f64)));
        prt!("  pure:          {:15}   {} %  of all variables", stats.all.pure, cfmt_f64("%10.2f", percent((stats.all.pure) as f64, (stats.vars) as f64)));
        prt!("  pureclauses:   {:15}   {}    per pure literal", stats.blockpured, cfmt_f64("%10.2f", relative((stats.blockpured) as f64, (stats.all.pure) as f64)));
      }
      if all || stats.chrono != 0 {
        prt!("chronological:   {:15}   {} %  of conflicts", stats.chrono, cfmt_f64("%10.2f", percent((stats.chrono) as f64, (stats.conflicts) as f64)));
      }
      if all {
        prt!("compacts:        {:15}   {}    interval", stats.compacts, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.compacts) as f64)));
      }
      if all || stats.conflicts != 0 {
        prt!("conflicts:       {:15}   {}    per second", stats.conflicts, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (t) as f64)));
        prt!("  backtracked:   {:15}   {} %  of conflicts", stats.backtracks, cfmt_f64("%10.2f", percent((stats.backtracks) as f64, (stats.conflicts) as f64)));
      }
      if all || stats.incremental_decay != 0 {
        prt!("inc-decay:       {:15}   {} %   per search", stats.incremental_decay, cfmt_f64("%10.2f", percent((stats.incremental_decay) as f64, (stats.searches) as f64)));
      }
      if all || stats.backbone.rounds != 0 {
        prt!("backbone:        {:15}   {} %  of vars", stats.backbone.probes, cfmt_f64("%10.2f", percent((stats.backbone.probes) as f64, (stats.vars) as f64)));
        prt!("   rounds:       {:15}   {}    per phase", stats.backbone.rounds, cfmt_f64("%10.2f", relative((stats.backbone.rounds) as f64, (stats.backbone.phases) as f64)));
        prt!("   phases:       {:15}   {}    interval", stats.backbone.phases, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.backbone.phases) as f64)));
        prt!("   units:        {:15}   {}    per phase", stats.backbone.units, cfmt_f64("%10.2f", percent((stats.backbone.units) as f64, (stats.backbone.phases) as f64)));
      }
      if all || stats.deduplicatedinit != 0 {
        prt!("dedup-init-rnds:  {:15}   {} %  of interval", stats.deduplicatedinitrounds, cfmt_f64("%10.2f", percent((stats.deduplicatedinitrounds) as f64, (stats.conflicts) as f64)));
        prt!("dedup-init:       {:15}   {} %  of subsumed", stats.deduplicatedinit, cfmt_f64("%10.2f", percent((stats.deduplicatedinit) as f64, (stats.deduplicatedinit) as f64)));
      }
      if all || stats.conditioned != 0 {
        prt!("conditioned:     {:15}   {} %  of irredundant clauses", stats.conditioned, cfmt_f64("%10.2f", percent((stats.conditioned) as f64, (stats.added.irredundant) as f64)));
        prt!("  conditionings: {:15}   {}    interval", stats.conditionings, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.conditionings) as f64)));
        prt!("  condcands:     {:15}   {}    candidate clauses", stats.condcands, cfmt_f64("%10.2f", relative((stats.condcands) as f64, (stats.conditionings) as f64)));
        prt!("  condassinit:   {}  {} %  initial assigned", cfmt_f64("%17.1f", relative((stats.condassinit) as f64, (stats.conditionings) as f64)), cfmt_f64("%9.2f", percent((stats.condassinit) as f64, (stats.condassvars) as f64)));
        prt!("  condcondinit:  {}  {} %  initial condition", cfmt_f64("%17.1f", relative((stats.condcondinit) as f64, (stats.conditionings) as f64)), cfmt_f64("%9.2f", percent((stats.condcondinit) as f64, (stats.condassinit) as f64)));
        prt!("  condautinit:   {}  {} %  initial autarky", cfmt_f64("%17.1f", relative((stats.condautinit) as f64, (stats.conditionings) as f64)), cfmt_f64("%9.2f", percent((stats.condautinit) as f64, (stats.condassinit) as f64)));
        prt!("  condassrem:    {}  {} %  final assigned", cfmt_f64("%17.1f", relative((stats.condassrem) as f64, (stats.conditioned) as f64)), cfmt_f64("%9.2f", percent((stats.condassrem) as f64, (stats.condassirem) as f64)));
        prt!("  condcondrem:   {}  {} %  final conditional", cfmt_f64("%19.3f", relative((stats.condcondrem) as f64, (stats.conditioned) as f64)), cfmt_f64("%7.2f", percent((stats.condcondrem) as f64, (stats.condassrem) as f64)));
        prt!("  condautrem:    {}  {} %  final autarky", cfmt_f64("%19.3f", relative((stats.condautrem) as f64, (stats.conditioned) as f64)), cfmt_f64("%7.2f", percent((stats.condautrem) as f64, (stats.condassrem) as f64)));
        prt!("  condprops:     {:15}   {}    per candidate", stats.condprops, cfmt_f64("%10.2f", relative((stats.condprops) as f64, (stats.condcands) as f64)));
      }
      if all || stats.cover.total != 0 {
        prt!("covered:         {:15}   {} %  of irredundant clauses", stats.cover.total, cfmt_f64("%10.2f", percent((stats.cover.total) as f64, (stats.added.irredundant) as f64)));
        prt!("  coverings:     {:15}   {}    interval", stats.cover.count, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.cover.count) as f64)));
        prt!("  asymmetric:    {:15}   {} %  of covered clauses", stats.cover.asymmetric, cfmt_f64("%10.2f", percent((stats.cover.asymmetric) as f64, (stats.cover.total) as f64)));
        prt!("  blocked:       {:15}   {} %  of covered clauses", stats.cover.blocked, cfmt_f64("%10.2f", percent((stats.cover.blocked) as f64, (stats.cover.total) as f64)));
      }
      if all || stats.decisions != 0 {
        prt!("decisions:       {:15}   {}    per second", stats.decisions, cfmt_f64("%10.2f", relative((stats.decisions) as f64, (t) as f64)));
        prt!("  searched:      {:15}   {}    per decision", stats.searched, cfmt_f64("%10.2f", relative((stats.searched) as f64, (stats.decisions) as f64)));
      }
      if all || stats.randec.random_decisions != 0 {
        prt!("rand. dec phase: {:15}   {}    per interval", stats.randec.random_decision_phases, cfmt_f64("%10.2f", relative((stats.randec.random_decision_phases) as f64, (stats.decisions) as f64)));
        prt!("random decs:     {:15}   {}    per phase", stats.randec.random_decisions, cfmt_f64("%10.2f", relative((stats.randec.random_decisions) as f64, (stats.randec.random_decision_phases) as f64)));
      }
      if all || stats.all.eliminated != 0 {
        prt!("eliminated:      {:15}   {} %  of all variables", stats.all.eliminated, cfmt_f64("%10.2f", percent((stats.all.eliminated) as f64, (stats.vars) as f64)));
        prt!("  fastelim:      {:15}   {} %  of eliminated", stats.all.fasteliminated, cfmt_f64("%10.2f", percent((stats.all.fasteliminated) as f64, (stats.all.eliminated) as f64)));
        prt!("  elimphases:    {:15}   {}    interval", stats.elimphases, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.elimphases) as f64)));
        prt!("  elimrounds:    {:15}   {}    per phase", stats.elimrounds, cfmt_f64("%10.2f", relative((stats.elimrounds) as f64, (stats.elimphases) as f64)));
        prt!("  elimtried:     {:15}   {} %  eliminated", stats.elimtried, cfmt_f64("%10.2f", percent((stats.all.eliminated) as f64, (stats.elimtried) as f64)));
        prt!("  elimgates:     {:15}   {} %  gates per tried", stats.elimgates, cfmt_f64("%10.2f", percent((stats.elimgates) as f64, (stats.elimtried) as f64)));
        prt!("  elimequivs:    {:15}   {} %  equivalence gates", stats.elimequivs, cfmt_f64("%10.2f", percent((stats.elimequivs) as f64, (stats.elimgates) as f64)));
        prt!("  elimands:      {:15}   {} %  and gates", stats.elimands, cfmt_f64("%10.2f", percent((stats.elimands) as f64, (stats.elimgates) as f64)));
        prt!("  elimites:      {:15}   {} %  if-then-else gates", stats.elimites, cfmt_f64("%10.2f", percent((stats.elimites) as f64, (stats.elimgates) as f64)));
        prt!("  elimxors:      {:15}   {} %  xor gates", stats.elimxors, cfmt_f64("%10.2f", percent((stats.elimxors) as f64, (stats.elimgates) as f64)));
        prt!("  elimdefs:      {:15}   {} %  definitions", stats.definitions_extracted, cfmt_f64("%10.2f", percent((stats.definitions_extracted) as f64, (stats.elimgates) as f64)));
        prt!("  elimsubst:     {:15}   {} %  substituted", stats.elimsubst, cfmt_f64("%10.2f", percent((stats.elimsubst) as f64, (stats.all.eliminated) as f64)));
        prt!("  elimsubstequi: {:15}   {} %  equivalence gates", stats.eliminated_equi, cfmt_f64("%10.2f", percent((stats.eliminated_equi) as f64, (stats.elimsubst) as f64)));
        prt!("  elimsubstands: {:15}   {} %  and gates", stats.eliminated_and, cfmt_f64("%10.2f", percent((stats.eliminated_and) as f64, (stats.elimsubst) as f64)));
        prt!("  elimsubstites: {:15}   {} %  if-then-else gates", stats.eliminated_ite, cfmt_f64("%10.2f", percent((stats.eliminated_ite) as f64, (stats.elimsubst) as f64)));
        prt!("  elimsubstxors: {:15}   {} %  xor gates", stats.eliminated_xor, cfmt_f64("%10.2f", percent((stats.eliminated_xor) as f64, (stats.elimsubst) as f64)));
        prt!("  elimsubstdefs: {:15}   {} %  definitions", stats.eliminated_def, cfmt_f64("%10.2f", percent((stats.eliminated_def) as f64, (stats.elimsubst) as f64)));
        prt!("  elimres:       {:15}   {}    per eliminated", stats.elimres, cfmt_f64("%10.2f", relative((stats.elimres) as f64, (stats.all.eliminated) as f64)));
        prt!("  elimrestried:  {:15}   {} %  per resolution", stats.elimrestried, cfmt_f64("%10.2f", percent((stats.elimrestried) as f64, (stats.elimres) as f64)));
        prt!("  def checked:   {:15}   {}    per phase", stats.definitions_checked, cfmt_f64("%10.2f", relative((stats.definitions_checked) as f64, (stats.elimphases) as f64)));
        prt!("  def extracted: {:15}   {} %  per checked", stats.definitions_extracted, cfmt_f64("%10.2f", percent((stats.definitions_extracted) as f64, (stats.definitions_checked) as f64)));
        prt!("  def units:     {:15}   {} %  per checked", stats.definition_units, cfmt_f64("%10.2f", percent((stats.definition_units) as f64, (stats.definitions_checked) as f64)));
      }
      if all || stats.ext_prop.ext_cb != 0 {
        prt!("ext.prop. calls: {:15}   {} %  of queries", stats.ext_prop.eprop_call, cfmt_f64("%10.2f", percent((stats.ext_prop.eprop_call) as f64, (stats.ext_prop.ext_cb) as f64)));
        prt!("  propagating:   {:15}   {} %  per eprop-call", stats.ext_prop.eprop_prop, cfmt_f64("%10.2f", percent((stats.ext_prop.eprop_prop) as f64, (stats.ext_prop.eprop_call) as f64)));
        prt!("  explained:     {:15}   {} %  per eprop-call", stats.ext_prop.eprop_expl, cfmt_f64("%10.2f", percent((stats.ext_prop.eprop_expl) as f64, (stats.ext_prop.eprop_call) as f64)));
        prt!("  falsified:     {:15}   {} %  per eprop-call", stats.ext_prop.eprop_conf, cfmt_f64("%10.2f", percent((stats.ext_prop.eprop_conf) as f64, (stats.ext_prop.eprop_call) as f64)));
        prt!("ext.clause calls:{:15}   {} %  of queries", stats.ext_prop.elearn_call, cfmt_f64("%10.2f", percent((stats.ext_prop.elearn_call) as f64, (stats.ext_prop.ext_cb) as f64)));
        prt!("  learned:       {:15}   {} %  per called", stats.ext_prop.elearned, cfmt_f64("%10.2f", percent((stats.ext_prop.elearned) as f64, (stats.ext_prop.elearn_call) as f64)));
        prt!("  conflicting:   {:15}   {} %  per learned", stats.ext_prop.elearn_conf, cfmt_f64("%10.2f", percent((stats.ext_prop.elearn_conf) as f64, (stats.ext_prop.elearned) as f64)));
        prt!("  propagating:   {:15}   {} %  per learned", stats.ext_prop.elearn_prop, cfmt_f64("%10.2f", percent((stats.ext_prop.elearn_prop) as f64, (stats.ext_prop.elearned) as f64)));
        prt!("ext.final check: {:15}   {} %  of queries", stats.ext_prop.echeck_call, cfmt_f64("%10.2f", percent((stats.ext_prop.echeck_call) as f64, (stats.ext_prop.ext_cb) as f64)));
      }
      if all || stats.factored != 0 {
        prt!("factored:        {:15}   {} %  of variables", stats.factored, cfmt_f64("%10.2f", percent((stats.factored) as f64, (internal.max_var) as f64)));
        prt!("  factor:        {:15}   {}    conflict interval", stats.factor, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.factor) as f64)));
        prt!("  cls factored:  {:15}   {}    per factored", stats.factor_added, cfmt_f64("%10.2f", relative((stats.factor_added) as f64, (stats.factored) as f64)));
        prt!("  lits factored: {:15}   {}    per factored", stats.literals_factored, cfmt_f64("%10.2f", relative((stats.literals_factored) as f64, (stats.factored) as f64)));
        prt!("  cls unfactored:{:15}   {}    per factored", stats.clauses_unfactored, cfmt_f64("%10.2f", relative((stats.clauses_unfactored) as f64, (stats.factored) as f64)));
        prt!("  lits unfactored:{:14}   {}    per factored", stats.literals_unfactored, cfmt_f64("%10.2f", relative((stats.literals_unfactored) as f64, (stats.factored) as f64)));
      }
      if all || stats.all.fixed != 0 {
        prt!("fixed:           {:15}   {} %  of all variables", stats.all.fixed, cfmt_f64("%10.2f", percent((stats.all.fixed) as f64, (stats.vars) as f64)));
        prt!("  failed:        {:15}   {} %  of all variables", stats.failed, cfmt_f64("%10.2f", percent((stats.failed) as f64, (stats.vars) as f64)));
        prt!("  probefailed:   {:15}   {} %  per failed", stats.probefailed, cfmt_f64("%10.2f", percent((stats.probefailed) as f64, (stats.failed) as f64)));
        prt!("  transredunits: {:15}   {} %  per failed", stats.transredunits, cfmt_f64("%10.2f", percent((stats.transredunits) as f64, (stats.failed) as f64)));
        prt!("  inprobephases: {:15}   {}    interval", stats.inprobingphases, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.inprobingphases) as f64)));
        prt!("  inprobesuccess:{:15}   {} %  phases", stats.inprobesuccess, cfmt_f64("%10.2f", percent((stats.inprobesuccess) as f64, (stats.inprobingphases) as f64)));
        prt!("  probingrounds: {:15}   {}    per phase", stats.probingrounds, cfmt_f64("%10.2f", relative((stats.probingrounds) as f64, (stats.inprobingphases) as f64)));
        prt!("  probed:        {:15}   {}    per failed", stats.probed, cfmt_f64("%10.2f", relative((stats.probed) as f64, (stats.failed) as f64)));
        prt!("  hbrs:          {:15}   {}    per probed", stats.hbrs, cfmt_f64("%10.2f", relative((stats.hbrs) as f64, (stats.probed) as f64)));
        prt!("  hbrsizes:      {:15}   {}    per hbr", stats.hbrsizes, cfmt_f64("%10.2f", relative((stats.hbrsizes) as f64, (stats.hbrs) as f64)));
        prt!("  hbreds:        {:15}   {} %  per hbr", stats.hbreds, cfmt_f64("%10.2f", percent((stats.hbreds) as f64, (stats.hbrs) as f64)));
        prt!("  hbrsubs:       {:15}   {} %  per hbr", stats.hbrsubs, cfmt_f64("%10.2f", percent((stats.hbrsubs) as f64, (stats.hbrs) as f64)));
      }
      prt!("  units:         {:15}   {}    interval", stats.units, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.units) as f64)));
      prt!("  binaries:      {:15}   {}    interval", stats.binaries, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.binaries) as f64)));
      if all || stats.flush.learned != 0 {
        prt!("flushed:         {:15}   {} %  per conflict", stats.flush.learned, cfmt_f64("%10.2f", percent((stats.flush.learned) as f64, (stats.conflicts) as f64)));
        prt!("  hyper:         {:15}   {} %  per conflict", stats.flush.hyper, cfmt_f64("%10.2f", relative((stats.flush.hyper) as f64, (stats.conflicts) as f64)));
        prt!("  flushings:     {:15}   {}    interval", stats.flush.count, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.flush.count) as f64)));
      }
      if all || stats.instantiated != 0 {
        prt!("instantiated:    {:15}   {} %  of tried", stats.instantiated, cfmt_f64("%10.2f", percent((stats.instantiated) as f64, (stats.instried) as f64)));
        prt!("  instrounds:    {:15}   {} %  of elimrounds", stats.instrounds, cfmt_f64("%10.2f", percent((stats.instrounds) as f64, (stats.elimrounds) as f64)));
      }
      if all || stats.conflicts != 0 {
        prt!("learned:         {:15}   {} %  per conflict", stats.learned.clauses, cfmt_f64("%10.2f", percent((stats.learned.clauses) as f64, (stats.conflicts) as f64)));
        prt!("  bumped:        {:15}   {}    per learned", stats.bumped, cfmt_f64("%10.2f", relative((stats.bumped) as f64, (stats.learned.clauses) as f64)));
        prt!("  recomputed:    {:15}   {} %  per learned", stats.recomputed, cfmt_f64("%10.2f", percent((stats.recomputed) as f64, (stats.learned.clauses) as f64)));
        prt!("  promoted1:     {:15}   {} %  per learned", stats.promoted1, cfmt_f64("%10.2f", percent((stats.promoted1) as f64, (stats.learned.clauses) as f64)));
        prt!("  promoted2:     {:15}   {} %  per learned", stats.promoted2, cfmt_f64("%10.2f", percent((stats.promoted2) as f64, (stats.learned.clauses) as f64)));
        prt!("  improvedglue:  {:15}   {} %  per learned", stats.improvedglue, cfmt_f64("%10.2f", percent((stats.improvedglue) as f64, (stats.learned.clauses) as f64)));
      }
      if all || stats.lucky.succeeded != 0 {
        prt!("lucky:           {:15}   {} %  of tried", stats.lucky.succeeded, cfmt_f64("%10.2f", percent((stats.lucky.succeeded) as f64, (stats.lucky.tried) as f64)));
        prt!("  constantzero   {:15}   {} %  of tried", stats.lucky.constant.zero, cfmt_f64("%10.2f", percent((stats.lucky.constant.zero) as f64, (stats.lucky.tried) as f64)));
        prt!("  constantone    {:15}   {} %  of tried", stats.lucky.constant.one, cfmt_f64("%10.2f", percent((stats.lucky.constant.one) as f64, (stats.lucky.tried) as f64)));
        prt!("  backwardone    {:15}   {} %  of tried", stats.lucky.backward.one, cfmt_f64("%10.2f", percent((stats.lucky.backward.one) as f64, (stats.lucky.tried) as f64)));
        prt!("  backwardzero   {:15}   {} %  of tried", stats.lucky.backward.zero, cfmt_f64("%10.2f", percent((stats.lucky.backward.zero) as f64, (stats.lucky.tried) as f64)));
        prt!("  forwardone     {:15}   {} %  of tried", stats.lucky.forward.one, cfmt_f64("%10.2f", percent((stats.lucky.forward.one) as f64, (stats.lucky.tried) as f64)));
        prt!("  forwardzero    {:15}   {} %  of tried", stats.lucky.forward.zero, cfmt_f64("%10.2f", percent((stats.lucky.forward.zero) as f64, (stats.lucky.tried) as f64)));
        prt!("  positivehorn   {:15}   {} %  of tried", stats.lucky.horn.positive, cfmt_f64("%10.2f", percent((stats.lucky.horn.positive) as f64, (stats.lucky.tried) as f64)));
        prt!("  negativehorn   {:15}   {} %  of tried", stats.lucky.horn.negative, cfmt_f64("%10.2f", percent((stats.lucky.horn.negative) as f64, (stats.lucky.tried) as f64)));
      }
      prt!("  extendbytes:   {:15}   {}    bytes and MB", extendbytes, cfmt_f64("%10.2f", extendbytes as f64 / (1i64 << 20) as f64));
      if all || stats.learned.clauses != 0 {
        prt!("learned_lits:    {:15}   {} %  learned literals", stats.learned.literals, cfmt_f64("%10.2f", percent((stats.learned.literals) as f64, (stats.learned.literals) as f64)));
      }
      prt!("minimized:       {:15}   {} %  learned literals", stats.minimized, cfmt_f64("%10.2f", percent((stats.minimized) as f64, (stats.learned.literals) as f64)));
      prt!("shrunken:        {:15}   {} %  learned literals", stats.shrunken, cfmt_f64("%10.2f", percent((stats.shrunken) as f64, (stats.learned.literals) as f64)));
      prt!("minishrunken:    {:15}   {} %  learned literals", stats.minishrunken, cfmt_f64("%10.2f", percent((stats.minishrunken) as f64, (stats.learned.literals) as f64)));
    
      if all || stats.conflicts != 0 {
        prt!("otfs:            {:15}   {} %  of conflict", stats.otfs.subsumed + stats.otfs.strengthened, cfmt_f64("%10.2f", percent((stats.otfs.subsumed + stats.otfs.strengthened) as f64, (stats.conflicts) as f64)));
        prt!("  subsumed       {:15}   {} %  of conflict", stats.otfs.subsumed, cfmt_f64("%10.2f", percent((stats.otfs.subsumed) as f64, (stats.conflicts) as f64)));
        prt!("  strengthened   {:15}   {} %  of conflict", stats.otfs.strengthened, cfmt_f64("%10.2f", percent((stats.otfs.strengthened) as f64, (stats.conflicts) as f64)));
      }
    
      prt!("propagations:    {:15}   {} M  per second", propagations, cfmt_f64("%10.2f", relative(propagations as f64 / 1e6, t)));
      prt!("  coverprops:    {:15}   {} %  of propagations", stats.propagations.cover, cfmt_f64("%10.2f", percent((stats.propagations.cover) as f64, (propagations) as f64)));
      prt!("  probeprops:    {:15}   {} %  of propagations", stats.propagations.probe, cfmt_f64("%10.2f", percent((stats.propagations.probe) as f64, (propagations) as f64)));
      prt!("  searchprops:   {:15}   {} %  of propagations", stats.propagations.search, cfmt_f64("%10.2f", percent((stats.propagations.search) as f64, (propagations) as f64)));
      prt!("  transredprops: {:15}   {} %  of propagations", stats.propagations.transred, cfmt_f64("%10.2f", percent((stats.propagations.transred) as f64, (propagations) as f64)));
      prt!("  vivifyprops:   {:15}   {} %  of propagations", stats.propagations.vivify, cfmt_f64("%10.2f", percent((stats.propagations.vivify) as f64, (propagations) as f64)));
      if all || stats.reactivated != 0 {
        prt!("reactivated:     {:15}   {} %  of all variables", stats.reactivated, cfmt_f64("%10.2f", percent((stats.reactivated) as f64, (stats.vars) as f64)));
      }
      if all || stats.reduced != 0 {
        prt!("reduced:         {:15}   {} %  per conflict", stats.reduced, cfmt_f64("%10.2f", percent((stats.reduced) as f64, (stats.conflicts) as f64)));
        prt!("  reductions:    {:15}   {}    interval", stats.reductions, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.reductions) as f64)));
        prt!("  sqrt scheme:   {:15}   {} %  reductions", stats.reduced_sqrt, cfmt_f64("%10.2f", relative((stats.reduced_sqrt) as f64, (stats.reductions) as f64)));
        prt!("  prct scheme:   {:15}   {} %  reductions", stats.reduced_prct, cfmt_f64("%10.2f", relative((stats.reduced_prct) as f64, (stats.reductions) as f64)));
        prt!("  collections:   {:15}   {}    interval", stats.collections, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.collections) as f64)));
      }
      if all || stats.rephased.total != 0 {
        prt!("rephased:        {:15}   {}    interval", stats.rephased.total, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.rephased.total) as f64)));
        prt!("  rephasedbest:  {:15}   {} %  rephased best", stats.rephased.best, cfmt_f64("%10.2f", percent((stats.rephased.best) as f64, (stats.rephased.total) as f64)));
        prt!("  rephasedflip:  {:15}   {} %  rephased flipping", stats.rephased.flipped, cfmt_f64("%10.2f", percent((stats.rephased.flipped) as f64, (stats.rephased.total) as f64)));
        prt!("  rephasedinv:   {:15}   {} %  rephased inverted", stats.rephased.inverted, cfmt_f64("%10.2f", percent((stats.rephased.inverted) as f64, (stats.rephased.total) as f64)));
        prt!("  rephasedorig:  {:15}   {} %  rephased original", stats.rephased.original, cfmt_f64("%10.2f", percent((stats.rephased.original) as f64, (stats.rephased.total) as f64)));
        prt!("  rephasedrand:  {:15}   {} %  rephased random", stats.rephased.random, cfmt_f64("%10.2f", percent((stats.rephased.random) as f64, (stats.rephased.total) as f64)));
        prt!("  rephasedwalk:  {:15}   {} %  rephased walk", stats.rephased.walk, cfmt_f64("%10.2f", percent((stats.rephased.walk) as f64, (stats.rephased.total) as f64)));
      }
      if all {
        prt!("rescored:        {:15}   {}    interval", stats.rescored, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.rescored) as f64)));
      }
      if all || stats.restarts != 0 {
        prt!("restarts:        {:15}   {}    interval", stats.restarts, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.restarts) as f64)));
        prt!("  reused:        {:15}   {} %  per restart", stats.reused, cfmt_f64("%10.2f", percent((stats.reused) as f64, (stats.restarts) as f64)));
        prt!("  reusedlevels:  {:15}   {} %  per restart levels", stats.reusedlevels, cfmt_f64("%10.2f", percent((stats.reusedlevels) as f64, (stats.restartlevels) as f64)));
      }
      if all || stats.restored != 0 {
        prt!("restored:        {:15}   {} %  per weakened", stats.restored, cfmt_f64("%10.2f", percent((stats.restored) as f64, (stats.weakened) as f64)));
        prt!("  restorations:  {:15}   {} %  per extension", stats.restorations, cfmt_f64("%10.2f", percent((stats.restorations) as f64, (stats.extensions) as f64)));
        prt!("  literals:      {:15}   {}    per restored clause", stats.restoredlits, cfmt_f64("%10.2f", relative((stats.restoredlits) as f64, (stats.restored) as f64)));
      }
      if all || stats.stabphases != 0 {
        prt!("stabilizing:     {:15}   {} %  of conflicts", stats.stabphases, cfmt_f64("%10.2f", percent((stats.stabconflicts) as f64, (stats.conflicts) as f64)));
        prt!("  restartstab:   {:15}   {} %  of all restarts", stats.restartstable, cfmt_f64("%10.2f", percent((stats.restartstable) as f64, (stats.restarts) as f64)));
        prt!("  reusedstab:    {:15}   {} %  per stable restarts", stats.reusedstable, cfmt_f64("%10.2f", percent((stats.reusedstable) as f64, (stats.restartstable) as f64)));
      }
      if all || stats.all.substituted != 0 {
        prt!("substituted:     {:15}   {} %  of all variables", stats.all.substituted, cfmt_f64("%10.2f", percent((stats.all.substituted) as f64, (stats.vars) as f64)));
        prt!("  decompositions:{:15}   {}    per phase", stats.decompositions, cfmt_f64("%10.2f", relative((stats.decompositions) as f64, (stats.inprobingphases) as f64)));
      }
      if all || stats.sweep_equivalences != 0 {
        prt!("sweep equivs:    {:15}   {} %  of swept variables", stats.sweep_equivalences, cfmt_f64("%10.2f", percent((stats.sweep_equivalences) as f64, (stats.sweep_variables) as f64)));
        prt!("  sweepings:     {:15}   {}    vars per sweeping", stats.sweep, cfmt_f64("%10.2f", relative((stats.sweep_variables) as f64, (stats.sweep) as f64)));
        prt!("  swept vars:    {:15}   {} %  of all variables", stats.sweep_variables, cfmt_f64("%10.2f", percent((stats.sweep_variables) as f64, (stats.vars) as f64)));
        prt!("  sweep units:   {:15}   {} %  of all variables", stats.sweep_units, cfmt_f64("%10.2f", percent((stats.sweep_units) as f64, (stats.vars) as f64)));
        prt!("  solved:        {:15}   {}    per swept variable", stats.sweep_solved, cfmt_f64("%10.2f", relative((stats.sweep_solved) as f64, (stats.sweep_variables) as f64)));
        prt!("  sat:           {:15}   {} %  solved", stats.sweep_sat, cfmt_f64("%10.2f", percent((stats.sweep_sat) as f64, (stats.sweep_solved) as f64)));
        prt!("  unsat:         {:15}   {} %  solved", stats.sweep_unsat, cfmt_f64("%10.2f", percent((stats.sweep_unsat) as f64, (stats.sweep_solved) as f64)));
        prt!("  backbone solved:{:14}   {} %  solved", stats.sweep_solved_backbone, cfmt_f64("%10.2f", percent((stats.sweep_solved_backbone) as f64, (stats.sweep_solved) as f64)));
        prt!("    sat:         {:15}   {} %  backbone solved", stats.sweep_sat_backbone, cfmt_f64("%10.2f", percent((stats.sweep_sat_backbone) as f64, (stats.sweep_solved_backbone) as f64)));
        prt!("    unsat:       {:15}   {} %  backbone solved", stats.sweep_unsat_backbone, cfmt_f64("%10.2f", percent((stats.sweep_unsat_backbone) as f64, (stats.sweep_solved_backbone) as f64)));
        prt!("    unknown:     {:15}   {} %  backbone solved", stats.sweep_unknown_backbone, cfmt_f64("%10.2f", percent((stats.sweep_unknown_backbone) as f64, (stats.sweep_solved_backbone) as f64)));
        prt!("    fixed:       {:15}   {}   per swept variable", stats.sweep_fixed_backbone, cfmt_f64("%10.2f", relative((stats.sweep_fixed_backbone) as f64, (stats.sweep_variables) as f64)));
        prt!("    flip:        {:15}   {}   per swept variable", stats.sweep_flip_backbone, cfmt_f64("%10.2f", relative((stats.sweep_flip_backbone) as f64, (stats.sweep_variables) as f64)));
        prt!("    flipped:     {:15}   {} %  of backbone flip", stats.sweep_flipped_backbone, cfmt_f64("%10.2f", percent((stats.sweep_flipped_backbone) as f64, (stats.sweep_flip_backbone) as f64)));
        prt!("  equiv solved:  {:15}   {} %  solved", stats.sweep_solved_equivalences, cfmt_f64("%10.2f", percent((stats.sweep_solved_equivalences) as f64, (stats.sweep_solved) as f64)));
        prt!("    sat:         {:15}   {} %  equiv solved", stats.sweep_sat_equivalences, cfmt_f64("%10.2f", percent((stats.sweep_sat_equivalences) as f64, (stats.sweep_solved_equivalences) as f64)));
        prt!("    unsat:       {:15}   {} %  equiv solved", stats.sweep_unsat_equivalences, cfmt_f64("%10.2f", percent((stats.sweep_unsat_equivalences) as f64, (stats.sweep_solved_equivalences) as f64)));
        prt!("    unknown:     {:15}   {} %  equiv solved", stats.sweep_unknown_equivalences, cfmt_f64("%10.2f", percent((stats.sweep_unknown_equivalences) as f64, (stats.sweep_solved_equivalences) as f64)));
        prt!("    flip:        {:15}   {}    per swept variable", stats.sweep_flip_equivalences, cfmt_f64("%10.2f", relative((stats.sweep_flip_equivalences) as f64, (stats.sweep_variables) as f64)));
        prt!("    flipped:     {:15}   {} %  of equiv flip", stats.sweep_flipped_equivalences, cfmt_f64("%10.2f", percent((stats.sweep_flipped_equivalences) as f64, (stats.sweep_flip_equivalences) as f64)));
        prt!("  depth:         {:15}   {}    per swept variable", stats.sweep_depth, cfmt_f64("%10.2f", relative((stats.sweep_depth) as f64, (stats.sweep_variables) as f64)));
        prt!("  environment:   {:15}   {}    per swept variable", stats.sweep_environment, cfmt_f64("%10.2f", relative((stats.sweep_environment) as f64, (stats.sweep_variables) as f64)));
        prt!("  clauses:       {:15}   {}    per swept variable", stats.sweep_clauses, cfmt_f64("%10.2f", relative((stats.sweep_clauses) as f64, (stats.sweep_variables) as f64)));
        prt!("  completed:     {:15}   {}    sweeps to complete", stats.sweep_completed, cfmt_f64("%10.2f", relative((stats.sweep) as f64, (stats.sweep_completed) as f64)));
      }
      if all || stats.subsumed != 0 {
        prt!("subsumed:        {:15}   {} %  of all clauses", stats.subsumed, cfmt_f64("%10.2f", percent((stats.subsumed) as f64, (stats.added.total) as f64)));
        prt!("  subsumephases: {:15}   {}    interval", stats.subsumephases, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.subsumephases) as f64)));
        prt!("  subsumerounds: {:15}   {}    per phase", stats.subsumerounds, cfmt_f64("%10.2f", relative((stats.subsumerounds) as f64, (stats.subsumephases) as f64)));
        prt!("  deduplicated:  {:15}   {} %  per subsumed", stats.deduplicated, cfmt_f64("%10.2f", percent((stats.deduplicated) as f64, (stats.subsumed) as f64)));
        prt!("  transreds:     {:15}   {}    interval", stats.transreds, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.transreds) as f64)));
        prt!("  transitive:    {:15}   {} %  per subsumed", stats.transitive, cfmt_f64("%10.2f", percent((stats.transitive) as f64, (stats.subsumed) as f64)));
        prt!("  subirr:        {:15}   {} %  of subsumed", stats.subirr, cfmt_f64("%10.2f", percent((stats.subirr) as f64, (stats.subsumed) as f64)));
        prt!("  subred:        {:15}   {} %  of subsumed", stats.subred, cfmt_f64("%10.2f", percent((stats.subred) as f64, (stats.subsumed) as f64)));
        prt!("  subtried:      {:15}   {}    tried per subsumed", stats.subtried, cfmt_f64("%10.2f", relative((stats.subtried) as f64, (stats.subsumed) as f64)));
        prt!("  subchecks:     {:15}   {}    per tried", stats.subchecks, cfmt_f64("%10.2f", relative((stats.subchecks) as f64, (stats.subtried) as f64)));
        prt!("  subchecks2:    {:15}   {} %  per subcheck", stats.subchecks2, cfmt_f64("%10.2f", percent((stats.subchecks2) as f64, (stats.subchecks) as f64)));
        prt!("  elimotfsub:    {:15}   {} %  of subsumed", stats.elimotfsub, cfmt_f64("%10.2f", percent((stats.elimotfsub) as f64, (stats.subsumed) as f64)));
        prt!("  elimbwsub:     {:15}   {} %  of subsumed", stats.elimbwsub, cfmt_f64("%10.2f", percent((stats.elimbwsub) as f64, (stats.subsumed) as f64)));
        prt!("  eagersub:      {:15}   {} %  of subsumed", stats.eagersub, cfmt_f64("%10.2f", percent((stats.eagersub) as f64, (stats.subsumed) as f64)));
        prt!("  eagertried:    {:15}   {}    tried per eagersub", stats.eagertried, cfmt_f64("%10.2f", relative((stats.eagertried) as f64, (stats.eagersub) as f64)));
      }
      if all || stats.strengthened != 0 {
        prt!("strengthened:    {:15}   {} %  of all clauses", stats.strengthened, cfmt_f64("%10.2f", percent((stats.strengthened) as f64, (stats.added.total) as f64)));
        prt!("  elimotfstr:    {:15}   {} %  of strengthened", stats.elimotfstr, cfmt_f64("%10.2f", percent((stats.elimotfstr) as f64, (stats.strengthened) as f64)));
        prt!("  elimbwstr:     {:15}   {} %  of strengthened", stats.elimbwstr, cfmt_f64("%10.2f", percent((stats.elimbwstr) as f64, (stats.strengthened) as f64)));
      }
      if all || stats.htrs != 0 {
        prt!("ternary:         {:15}   {} %  of resolved", stats.htrs, cfmt_f64("%10.2f", percent((stats.htrs) as f64, (stats.ternres) as f64)));
        prt!("  phases:        {:15}   {}    interval", stats.ternary, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.ternary) as f64)));
        prt!("  htr3:          {:15}   {} %  ternary hyper ternres", stats.htrs3, cfmt_f64("%10.2f", percent((stats.htrs3) as f64, (stats.htrs) as f64)));
        prt!("  htr2:          {:15}   {} %  binary hyper ternres", stats.htrs2, cfmt_f64("%10.2f", percent((stats.htrs2) as f64, (stats.htrs) as f64)));
      }
      prt!("ticks:           {:15}   {}    propagation", totalticks, cfmt_f64("%10.2f", relative((totalticks) as f64, (stats.propagations.search) as f64)));
      prt!(" searchticks:    {:15}   {} %  totalticks", searchticks, cfmt_f64("%10.2f", percent((searchticks) as f64, (totalticks) as f64)));
      prt!("   stableticks:  {:15}   {} %  searchticks", stats.ticks.search[1], cfmt_f64("%10.2f", percent((stats.ticks.search[1]) as f64, (searchticks) as f64)));
      prt!("   unstableticks:{:15}   {} %  searchticks", stats.ticks.search[0], cfmt_f64("%10.2f", percent((stats.ticks.search[0]) as f64, (searchticks) as f64)));
      prt!(" inprobeticks:   {:15}   {} %  totalticks", inprobeticks, cfmt_f64("%10.2f", percent((inprobeticks) as f64, (totalticks) as f64)));
      prt!("   backboneticks:{:15}   {} %  searchticks", stats.ticks.backbone, cfmt_f64("%10.2f", percent((stats.ticks.backbone) as f64, (searchticks) as f64)));
      prt!("   factorticks:  {:15}   {} %  searchticks", stats.ticks.factor, cfmt_f64("%10.2f", percent((stats.ticks.factor) as f64, (searchticks) as f64)));
      prt!("   probeticks:   {:15}   {} %  searchticks", stats.ticks.probe, cfmt_f64("%10.2f", percent((stats.ticks.probe) as f64, (searchticks) as f64)));
      prt!("   sweepticks:   {:15}   {} %  searchticks", stats.ticks.sweep, cfmt_f64("%10.2f", percent((stats.ticks.sweep) as f64, (searchticks) as f64)));
      prt!("   ternaryticks: {:15}   {} %  searchticks", stats.ticks.ternary, cfmt_f64("%10.2f", percent((stats.ticks.ternary) as f64, (searchticks) as f64)));
      prt!("   vivifyticks:  {:15}   {} %  searchticks", stats.ticks.vivify, cfmt_f64("%10.2f", percent((stats.ticks.vivify) as f64, (searchticks) as f64)));
      prt!("   walkticks:    {:15}   {} %  searchticks", stats.ticks.walk, cfmt_f64("%10.2f", percent((stats.ticks.walk) as f64, (searchticks) as f64)));
      prt!("   walkflipticks:{:15}   {} %  searchticks", stats.ticks.walkflip, cfmt_f64("%10.2f", percent((stats.ticks.walkflip) as f64, (searchticks) as f64)));
      prt!("   walkflipbrk:  {:15}   {} %  searchticks", stats.ticks.walkflipbroken, cfmt_f64("%10.2f", percent((stats.ticks.walkflipbroken) as f64, (searchticks) as f64)));
      prt!("   walkflipWL:   {:15}   {} %  searchticks", stats.ticks.walkflipWL, cfmt_f64("%10.2f", percent((stats.ticks.walkflipWL) as f64, (searchticks) as f64)));
      prt!("   walkpickticks:{:15}   {} %  searchticks", stats.ticks.walkpick, cfmt_f64("%10.2f", percent((stats.ticks.walkpick) as f64, (searchticks) as f64)));
      prt!("   walkbreak:    {:15}   {} %  searchticks", stats.ticks.walkbreak, cfmt_f64("%10.2f", percent((stats.ticks.walkbreak) as f64, (searchticks) as f64)));
      if all {
        prt!("tier recomputed: {:15}   {}    interval", stats.tierecomputed, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.tierecomputed) as f64)));
      }
      if all || stats.ilbtriggers != 0 {
        prt!("trail reuses:    {:15}   {} %  of incremental calls", stats.ilbsuccess, cfmt_f64("%10.2f", percent((stats.ilbsuccess) as f64, (stats.ilbtriggers) as f64)));
        prt!("  levels:        {:15}   {}    per reuse", stats.levelsreused, cfmt_f64("%10.2f", relative((stats.levelsreused) as f64, (stats.ilbsuccess) as f64)));
        prt!("  literals:      {:15}   {}    per reuse", stats.literalsreused, cfmt_f64("%10.2f", relative((stats.literalsreused) as f64, (stats.ilbsuccess) as f64)));
        prt!("  assumptions:   {:15}   {}    per reuse", stats.assumptionsreused, cfmt_f64("%10.2f", relative((stats.assumptionsreused) as f64, (stats.ilbsuccess) as f64)));
      }
      if all || vivified != 0 {
        prt!("vivified:        {:15}   {} %  of all clauses", vivified, cfmt_f64("%10.2f", percent((vivified) as f64, (stats.added.total) as f64)));
        prt!("  vivifications: {:15}   {}    interval", stats.vivifications, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.vivifications) as f64)));
        prt!("  vivifychecks:  {:15}   {} %  per conflict", stats.vivifychecks, cfmt_f64("%10.2f", percent((stats.vivifychecks) as f64, (stats.conflicts) as f64)));
        let vivified = stats.vivifiedtier1 + stats.vivifiedtier2 +
                                 stats.vivifiedtier3 + stats.vivifiedirred;
        prt!("  vivified:      {:15}   {} %  per check", vivified, cfmt_f64("%10.2f", percent((vivified) as f64, (stats.vivifychecks) as f64)));
        prt!("  vified-irred:  {:15}   {} %  per vivified", stats.vivifiedirred, cfmt_f64("%10.2f", percent((stats.vivifiedirred) as f64, (vivified) as f64)));
        prt!("  vified-tier1:  {:15}   {} %  per vivified", stats.vivifiedtier1, cfmt_f64("%10.2f", percent((stats.vivifiedtier1) as f64, (vivified) as f64)));
        prt!("  vified-tier2:  {:15}   {} %  per vivified", stats.vivifiedtier2, cfmt_f64("%10.2f", percent((stats.vivifiedtier2) as f64, (vivified) as f64)));
        prt!("  vified-tier3:  {:15}   {} %  per vivified", stats.vivifiedtier3, cfmt_f64("%10.2f", percent((stats.vivifiedtier3) as f64, (vivified) as f64)));
        prt!("  vivifysched:   {:15}   {} %  checks per scheduled", stats.vivifysched, cfmt_f64("%10.2f", percent((stats.vivifychecks) as f64, (stats.vivifysched) as f64)));
        prt!("  vivifyunits:   {:15}   {} %  per vivify check", stats.vivifyunits, cfmt_f64("%10.2f", percent((stats.vivifyunits) as f64, (stats.vivifychecks) as f64)));
        prt!("  vivifyinst:    {:15}   {} %  per vivify check", stats.vivifyinst, cfmt_f64("%10.2f", percent((stats.vivifyinst) as f64, (stats.vivifychecks) as f64)));
        prt!("  vivifysubs:    {:15}   {} %  per subsumed", stats.vivifysubs, cfmt_f64("%10.2f", percent((stats.vivifysubs) as f64, (stats.subsumed) as f64)));
        prt!("  vivifyflushed: {:15}   {} %  per subsumed", stats.vivifyflushed, cfmt_f64("%10.2f", percent((stats.vivifyflushed) as f64, (stats.subsumed) as f64)));
        prt!("  vivifysubred:  {:15}   {} %  per subs", stats.vivifysubred, cfmt_f64("%10.2f", percent((stats.vivifysubred) as f64, (stats.vivifysubs) as f64)));
        prt!("  vivifysubirr:  {:15}   {} %  per subs", stats.vivifysubirr, cfmt_f64("%10.2f", percent((stats.vivifysubirr) as f64, (stats.vivifysubs) as f64)));
        prt!("  vivifystrs:    {:15}   {} %  per strengthened", stats.vivifystrs, cfmt_f64("%10.2f", percent((stats.vivifystrs) as f64, (stats.strengthened) as f64)));
        prt!("  vivifystrirr:  {:15}   {} %  per vivifystrs", stats.vivifystrirr, cfmt_f64("%10.2f", percent((stats.vivifystrirr) as f64, (stats.vivifystrs) as f64)));
        prt!("  vivifystred1:  {:15}   {} %  per vivifystrs", stats.vivifystred1, cfmt_f64("%10.2f", percent((stats.vivifystred1) as f64, (stats.vivifystrs) as f64)));
        prt!("  vivifystred2:  {:15}   {} %  per viviyfstrs", stats.vivifystred2, cfmt_f64("%10.2f", percent((stats.vivifystred2) as f64, (stats.vivifystrs) as f64)));
        prt!("  vivifystred3:  {:15}   {} %  per vivifystrs", stats.vivifystred3, cfmt_f64("%10.2f", percent((stats.vivifystred3) as f64, (stats.vivifystrs) as f64)));
        prt!("  vivifydemote:  {:15}   {} %  per vivifystrs", stats.vivifydemote, cfmt_f64("%10.2f", percent((stats.vivifydemote) as f64, (stats.vivifystrs) as f64)));
        prt!("  vivifydecs:    {:15}   {}    per checks", stats.vivifydecs, cfmt_f64("%10.2f", relative((stats.vivifydecs) as f64, (stats.vivifychecks) as f64)));
        prt!("  vivifyreused:  {:15}   {} %  per non-reused decision", stats.vivifyreused, cfmt_f64("%10.2f", percent((stats.vivifyreused) as f64, (stats.vivifydecs) as f64)));
      }
      if all || stats.walk.count != 0 {
        prt!("walked:          {:15}   {}    interval", stats.walk.count, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.walk.count) as f64)));
        if all || stats.warmup.count != 0 {
          prt!("  prop-warmup:   {:15}   {}    per warmup", stats.warmup.propagated, cfmt_f64("%10.2f", relative((stats.warmup.propagated) as f64, (stats.warmup.count) as f64)));
          prt!("  dec-warmup:    {:15}   {}    per warmup", stats.warmup.decision, cfmt_f64("%10.2f", relative((stats.warmup.decision) as f64, (stats.warmup.count) as f64)));
          prt!("  dummydec-w:    {:15}   {}    per warmup", stats.warmup.dummydecision, cfmt_f64("%10.2f", relative((stats.warmup.dummydecision) as f64, (stats.warmup.count) as f64)));
          prt!("  conflicts:     {:15}   {}    per warmup", stats.warmup.conflicts, cfmt_f64("%10.2f", relative((stats.warmup.conflicts) as f64, (stats.warmup.count) as f64)));
          prt!("  warmup:        {:15}   {}    per walk", stats.warmup.count, cfmt_f64("%10.2f", relative((stats.warmup.count) as f64, (stats.walk.count) as f64)));
        }
        if internal.profiles[ProfileId::walk].value > 0.0 {
          prt!("  flips:         {:15}   {} M  per second", stats.walk.flips, cfmt_f64("%10.2f", relative(1e-6 * stats.walk.flips as f64, internal.profiles[ProfileId::walk].value)));
        } else {
          prt!("  flips:         {:15}   {}    per walk", stats.walk.flips, cfmt_f64("%10.2f", relative((stats.walk.flips) as f64, (stats.walk.count) as f64)));
        }
        if stats.walk.minimum < i64::MAX {
          prt!("  minimum:       {:15}   {} %  clauses", stats.walk.minimum, cfmt_f64("%10.2f", percent((stats.walk.minimum) as f64, (stats.added.irredundant) as f64)));
        }
        prt!("  broken:        {:15}   {}    per flip", stats.walk.broken, cfmt_f64("%10.2f", relative((stats.walk.broken) as f64, (stats.walk.flips) as f64)));
        prt!("  improved:      {:15}   {}    per walk", stats.walk.improved, cfmt_f64("%10.2f", relative((stats.walk.improved) as f64, (stats.walk.count) as f64)));
      }
      if all || stats.weakened != 0 {
        prt!("weakened:        {:15}   {}    average size", stats.weakened, cfmt_f64("%10.2f", relative((stats.weakenedlen) as f64, (stats.weakened) as f64)));
        prt!("  extensions:    {:15}   {}    interval", stats.extensions, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.extensions) as f64)));
        prt!("  flipped:       {:15}   {}    per weakened", stats.extended, cfmt_f64("%10.2f", relative((stats.extended) as f64, (stats.weakened) as f64)));
      }
    
      if all || stats.congruence.gates != 0 {
        prt!("congruence:      {:15}   {}    interval", stats.congruence.rounds, cfmt_f64("%10.2f", relative((stats.conflicts) as f64, (stats.congruence.rounds) as f64)));
        prt!("   units:        {:15}   {}    per congruent", stats.congruence.units, cfmt_f64("%10.2f", relative((stats.congruence.units) as f64, (stats.congruence.congruent) as f64)));
        prt!("   cong-and:     {:15}   {}    per found gates", stats.congruence.ands, cfmt_f64("%10.2f", relative((stats.congruence.ands) as f64, (stats.congruence.gates) as f64)));
        prt!("   cong-ite:     {:15}   {}    per found gates", stats.congruence.ites, cfmt_f64("%10.2f", relative((stats.congruence.ites) as f64, (stats.congruence.gates) as f64)));
        prt!("   cong-xor:     {:15}   {}    per found gates", stats.congruence.xors, cfmt_f64("%10.2f", relative((stats.congruence.xors) as f64, (stats.congruence.gates) as f64)));
        prt!("   congruent:    {:15}   {}    per round", stats.congruence.congruent, cfmt_f64("%10.2f", relative((stats.congruence.rounds) as f64, (stats.congruence.congruent) as f64)));
        prt!("   unaries:      {:15}   {}    per round", stats.congruence.unaries, cfmt_f64("%10.2f", relative((stats.congruence.rounds) as f64, (stats.congruence.unaries) as f64)));
        let rewritten = stats.congruence.rewritten_ands +
                            stats.congruence.rewritten_xors +
                            stats.congruence.rewritten_ites;
        prt!("   rewritten:    {:15}   {}    per round", rewritten, cfmt_f64("%10.2f", percent((rewritten) as f64, (stats.congruence.rounds) as f64)));
        prt!("   rewri.-ands:  {:15}   {}    per rewritten", stats.congruence.rewritten_ands, cfmt_f64("%10.2f", percent((stats.congruence.rewritten_ands) as f64, (rewritten) as f64)));
        prt!("   rewri.-xors:  {:15}   {}%  per rewritten", stats.congruence.rewritten_xors, cfmt_f64("%10.2f", percent((stats.congruence.rewritten_xors) as f64, (rewritten) as f64)));
        prt!("   rewri.-ites:  {:15}   {}%  per rewritten", stats.congruence.rewritten_ites, cfmt_f64("%10.2f", percent((stats.congruence.rewritten_ites) as f64, (rewritten) as f64)));
        prt!("   subsumed:     {:15}   {}%  per round", stats.congruence.subsumed, cfmt_f64("%10.2f", relative((stats.congruence.subsumed) as f64, (stats.congruence.rounds) as f64)));
      }

        msg!(internal);
        msg!(
            internal,
            "{}seconds are measured in {} time for solving{}",
            tout().magenta_code(),
            if internal.opts.realtime != 0 { "real" } else { "process" },
            tout().normal_code()
        );

        section!(internal, "glue usage");

        internal.print_tier_usage_statistics();
    }
}

impl Internal {
    pub fn print_resource_usage(&mut self) {
        section!(self, "resources");
        let m: u64 = maximum_resident_set_size();
        msg!(
            self,
            "total process time since initialization: {}    seconds",
            cfmt_f64("%12.2f", self.process_time())
        );
        msg!(
            self,
            "total real time since initialization:    {}    seconds",
            cfmt_f64("%12.2f", self.real_time())
        );
        msg!(
            self,
            "maximum resident set size of process:    {}    MB",
            cfmt_f64("%12.2f", m as f64 / (1i64 << 20) as f64)
        );
    }
}
