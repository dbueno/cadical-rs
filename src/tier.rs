//! Port of `tier.cpp`.

#[allow(unused_imports)]
use crate::prelude::*;

/// `std::to_string (double)` (which is `"%f"`) followed by `.substr (0, 5)`.
fn to_string_substr5(x: f64) -> String {
    let s = crate::format::fmt_f(x, 6);
    s.chars().take(5).collect()
}

impl Internal {
    pub fn recompute_tier(&mut self) {
        if self.opts.recomputetier == 0 {
            return;
        }

        self.stats.tierecomputed += 1;
        let delta: i64 = if self.stats.tierecomputed >= 16 {
            (1u32 << 16) as i64
        } else {
            (1u32 << self.stats.tierecomputed) as i64
        };
        self.lim.recompute_tier = self.stats.conflicts + delta;
        log!(
            self,
            "rescheduling in {} at {} (conflicts at {})",
            delta,
            self.lim.recompute_tier,
            self.stats.conflicts
        );
        let stable = self.stable as usize;
        #[cfg(debug_assertions)]
        {
            let mut total_used: u64 = 0;
            for &u in &self.stats.used[stable] {
                total_used = total_used.wrapping_add(u);
            }
            debug_assert!(total_used == self.stats.bump_used[stable]);
        }

        if self.stats.bump_used[stable] == 0 {
            self.tier1[stable] = self.opts.reducetier1glue;
            self.tier2[stable] = self.opts.reducetier2glue;
            log!(self, "tier1 limit = {}", self.tier1[stable]);
            log!(self, "tier2 limit = {}", self.tier2[stable]);
            return;
        } else {
            let accumulated_tier1_limit =
                self.stats.bump_used[stable].wrapping_mul(self.opts.tier1limit as u64) / 100;
            let accumulated_tier2_limit =
                self.stats.bump_used[stable].wrapping_mul(self.opts.tier2limit as u64) / 100;
            self.tier1[stable] = 1;
            self.tier2[stable] = 1;
            let used = &self.stats.used[stable];
            let mut accumulated_used: u64 = used[0];
            let mut glue: usize = 1;
            while glue < used.len() {
                let u = used[glue];
                accumulated_used = accumulated_used.wrapping_add(u);
                if accumulated_used >= accumulated_tier1_limit {
                    self.tier1[stable] = glue as i32;
                    break;
                }
                glue += 1;
            }
            while glue < used.len() {
                let u = used[glue];
                accumulated_used = accumulated_used.wrapping_add(u);
                if accumulated_used >= accumulated_tier2_limit {
                    self.tier2[stable] = glue as i32;
                    break;
                }
                glue += 1;
            }
        }

        debug_assert!(self.tier1[stable] > 0);

        debug_assert!(self.tier1[stable] != 0);
        debug_assert!(self.tier2[stable] != 0);

        if self.tier1[stable] < self.opts.tier1minglue {
            log!(
                self,
                "tier1 limit of {} is too low, setting {} instead",
                self.tier1[stable],
                self.opts.tier1minglue
            );
            self.tier1[stable] = self.opts.tier1minglue;
        }
        if self.tier2[stable] < self.opts.tier2minglue {
            log!(
                self,
                "tier2 limit of {} is too low, setting {} instead",
                self.tier2[stable],
                self.opts.tier2minglue
            );
            self.tier2[stable] = self.opts.tier2minglue;
        }
        if self.tier1[stable] >= self.tier2[stable] {
            self.tier2[stable] = self.tier1[stable] + 1;
        }
        debug_assert!(self.tier2[stable] > self.tier1[stable]);

        let mode = if self.stable { "stable" } else { "focused" };
        phase!(
            self,
            "retiered",
            self.stats.tierecomputed,
            "tier1 limit = {} in {} mode, tier2 limit = {} in {} mode",
            self.tier1[stable],
            mode,
            self.tier2[stable],
            mode
        );
    }

    pub fn print_tier_usage_statistics(&mut self) {
        self.recompute_tier();

        for stable in [false, true] {
            let s = stable as usize;
            // Reading beyond the end of 'used' is undefined behaviour in
            // C++ (only possible for 'tier2 >= 127'); we read zero instead.
            let used_at = |this: &Internal, glue: usize| -> u64 {
                this.stats.used[s].get(glue).copied().unwrap_or(0)
            };
            let used_len = self.stats.used[s].len();
            let mut total_used: u32 = 0;
            for glue in 0..used_len {
                total_used = total_used.wrapping_add(self.stats.used[s][glue] as u32);
            }

            let mode: &str = if stable { "stable" } else { "focused" };
            let tier1 = self.tier1[s] as usize;
            let tier2 = self.tier2[s] as usize;
            if tier1 > tier2 && self.opts.reducetier1glue > self.opts.reducetier2glue {
                msg!(self, "tier1 > tier 2 due to the options, giving up");
                break;
            }
            debug_assert!(tier1 <= tier2);
            let prefix: u32;
            let suffix: u32;
            let span: u32 = (tier2 - tier1 + 1) as u32;
            const MAX_PRINTED: u32 = 5;
            if span > MAX_PRINTED {
                prefix = (tier1 + (MAX_PRINTED / 2) as usize - 1) as u32;
                suffix = (tier2 - (MAX_PRINTED / 2) as usize + 1) as u32;
            } else {
                prefix = u32::MAX;
                suffix = 0;
            }

            let mut accumulated_middle: u64 = 0;
            let mut glue_digits: i32 = 1;
            let mut clauses_digits: i32 = 1;
            let mut glue: u32 = 0;
            while glue as usize <= used_len {
                if (glue as usize) < tier1 {
                    glue += 1;
                    continue;
                }
                let used = used_at(self, glue as usize);
                let mut tmp_glue: i32 = 0;
                let mut tmp_clauses: i32 = 0;
                if glue <= prefix || suffix <= glue {
                    tmp_glue = glue as i32;
                    tmp_clauses = used as i32;
                } else {
                    accumulated_middle = accumulated_middle.wrapping_add(used);
                    if glue.wrapping_add(1) == suffix {
                        tmp_glue = (prefix.wrapping_add(1).wrapping_add(glue).wrapping_add(1)) as i32;
                        tmp_clauses = accumulated_middle as i32;
                    }
                }
                if tmp_glue > glue_digits {
                    glue_digits = tmp_glue;
                }
                if tmp_clauses > clauses_digits {
                    clauses_digits = tmp_clauses;
                }
                if glue as usize == tier2 {
                    break;
                }
                glue += 1;
            }
            let _ = (glue_digits, clauses_digits);

            accumulated_middle = 0;
            let mut accumulated: u64 = 0;
            let mut output = String::new();
            let mut glue: u32 = 0;
            while glue as usize <= used_len {
                let used = used_at(self, glue as usize);
                accumulated = accumulated.wrapping_add(used);
                if (glue as usize) < tier1 {
                    glue += 1;
                    continue;
                }
                if glue <= prefix || suffix <= glue.wrapping_add(1) {
                    output += mode;
                    output += " glue ";
                }
                if glue <= prefix || suffix <= glue {
                    output += &glue.to_string();
                    output += &format!(" used {}", used);
                    output += " clauses ";
                    output += &to_string_substr5(percent(used as f64, total_used as f64));
                    output += "%";
                    output += " accumulated ";
                    output += &to_string_substr5(percent(accumulated as f64, total_used as f64));
                    output += "%";
                    if glue as usize == tier1 {
                        output += " tier1";
                    }
                    if glue as usize == tier2 {
                        output += " tier2";
                    }
                    msg!(self, "{}", output);
                    output.clear();
                } else {
                    accumulated_middle = accumulated_middle.wrapping_add(used);
                    if glue.wrapping_add(1) == suffix {
                        let glue_str = format!("{}-{}", prefix.wrapping_add(1), suffix.wrapping_sub(1));
                        output += &glue_str;
                        output += &format!(" used {}", accumulated_middle);
                        output += " clauses ";
                        output += &to_string_substr5(percent(accumulated_middle as f64, total_used as f64));
                        output += "%";
                        output += " accumulated ";
                        output += &to_string_substr5(percent(accumulated as f64, total_used as f64));
                        output += "%";
                        msg!(self, "{}", output);
                        output.clear();
                    }
                }
                if glue as usize == tier2 {
                    break;
                }
                glue += 1;
            }

            msg!(self);
        }
    }
}
