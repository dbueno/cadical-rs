//! Port of `report.cpp`.
//!
//! Provide nicely formatted progress report messages while running through
//! the 'report' function below.  The code is so complex, because it should
//! be easy to add and remove reporting of certain statistics, while still
//! providing a nicely looking format with automatically aligned headers.
//!
//! The 'reports' are shown as `c <char> ...` (see the table in the C++
//! source 'report.cpp' for the meaning of `<char>`).

#[allow(unused_imports)]
use crate::prelude::*;
use crate::format::cfmt_f64;
use crate::message::{c_stdout, fflush, fputc, fputs};
use crate::resources::current_resident_set_size;
use crate::terminal::tout;

/*------------------------------------------------------------------------*/

struct Report {
    header: &'static str,
    /// C++ `char buffer[32]`.
    buffer: String,
    pos: i32,
}

impl Report {
    fn print_header(&self, line: &mut [u8]) {
        let header = self.header.as_bytes();
        let len = header.len() as i32;
        let mut i: i32 = -1;
        let mut j: i32 = self.pos - (len + 1) / 2 - 3;
        while i < len {
            debug_assert!(j >= 0);
            line[j as usize] = if i < 0 { b' ' } else { header[i as usize] };
            i += 1;
            j += 1;
        }
    }

    fn new(h: &'static str, precision: i32, min: i32, value: f64) -> Report {
        let fmt = if precision < 0 {
            format!("%.{}f", -precision - 1)
        } else {
            format!("%.{}f", precision)
        };
        let mut buffer = truncate31(cfmt_f64(&fmt, value));
        let width = buffer.len() as i32;
        if precision < 0 {
            // 'strcat (buffer, "%")'.
            buffer.push('%');
            buffer = truncate31(buffer);
        }
        if width >= min {
            return Report { header: h, buffer, pos: 0 };
        }
        let fmt = if precision < 0 {
            format!("%{}.{}f%%", min, -precision - 1)
        } else {
            format!("%{}.{}f", min, precision)
        };
        let buffer = truncate31(cfmt_f64(&fmt, value));
        Report { header: h, buffer, pos: 0 }
    }
}

/// 'snprintf' into 'char buffer[32]' keeps at most 31 characters.
fn truncate31(mut s: String) -> String {
    if s.len() > 31 {
        s.truncate(31);
    }
    s
}

/*------------------------------------------------------------------------*/

impl Internal {
    /// `verbose_level` defaults to `0` in C++ (`type_` is the C++ `char`).
    pub fn report(&mut self, type_: u8, verbose_level: i32) {
        if self.opts.report == 0 {
            return;
        }
        #[cfg(feature = "logging")]
        let logging = self.opts.log != 0;
        #[cfg(not(feature = "logging"))]
        let logging = false;
        if !logging && (self.opts.quiet != 0 || (verbose_level > self.opts.verbose)) {
            return;
        }
        if !self.reported {
            debug_assert!(self.lim.report == 0);
            self.reported = true;
            msg!(
                self,
                "{}time measured in {} time {}{}",
                tout().magenta_code(),
                if self.opts.realtime != 0 { "real" } else { "process" },
                if self.opts.reportsolve != 0 { "in solving" } else { "since initialization" },
                tout().normal_code()
            );
        }

        // The 'REPORTS' table:  HEADER, PRECISION, MIN, VALUE.
        let mut reports: Vec<Report> = Vec::with_capacity(17);
        let time = if self.opts.reportsolve != 0 { self.solve_time() } else { self.time() };
        reports.push(Report::new("seconds", 2, 5, time));
        let mb = current_resident_set_size() as f64 / (1i64 << 20) as f64;
        reports.push(Report::new("MB", 0, 2, mb));
        reports.push(Report::new("level", 0, 2, self.averages.current.level.value()));
        reports.push(Report::new("reductions", 0, 1, self.stats.reductions as f64));
        reports.push(Report::new("restarts", 0, 3, self.stats.restarts as f64));
        reports.push(Report::new("rate", 0, 2, self.averages.current.decisions.value()));
        reports.push(Report::new("conflicts", 0, 4, self.stats.conflicts as f64));
        reports.push(Report::new("redundant", 0, 4, self.stats.current.redundant as f64));
        reports.push(Report::new(
            "size/glue",
            1,
            2,
            relative(self.averages.current.size.value(), self.averages.current.glue.slow.value()),
        ));
        reports.push(Report::new("size", 0, 1, self.averages.current.size.value()));
        reports.push(Report::new("glue", 0, 1, self.averages.current.glue.slow.value()));
        let stable = self.stable as usize;
        reports.push(Report::new("tier1", 0, 1, self.tier1[stable] as f64));
        reports.push(Report::new("tier2", 0, 1, self.tier2[stable] as f64));
        let trail = percent(self.averages.current.trail.slow.value(), self.max_var as f64);
        reports.push(Report::new("trail", -1, 2, trail));
        reports.push(Report::new("irredundant", 0, 4, self.stats.current.irredundant as f64));
        reports.push(Report::new("variables", 0, 3, self.active_count() as f64));
        let remaining = percent(self.active_count() as f64, self.stats.variables_original as f64);
        reports.push(Report::new("remaining", -1, 2, remaining));
        let n = reports.len();

        let out = c_stdout();
        if self.lim.report == 0 {
            self.print_prefix();
            fputc(b'\n' as i32, out);
            let mut pos: i32 = 4;
            for r in reports.iter_mut() {
                let len = r.buffer.len() as i32;
                r.pos = pos + (len + 1) / 2;
                pos += len + 1;
            }
            let max_line = (pos + 20) as usize;
            let nrows = 3;
            let mut line = vec![b' '; max_line];
            for start in 0..nrows {
                for c in line.iter_mut() {
                    *c = b' ';
                }
                let mut i = start;
                while i < n {
                    reports[i].print_header(&mut line);
                    i += nrows;
                }
                let mut i = max_line - 1;
                while line[i - 1] == b' ' {
                    i -= 1;
                }
                self.print_prefix();
                tout().yellow(false);
                fputs(std::str::from_utf8(&line[..i]).unwrap_or(""), out);
                tout().normal();
                fputc(b'\n' as i32, out);
            }
            self.print_prefix();
            fputc(b'\n' as i32, out);
            self.lim.report = 19;
        } else {
            self.lim.report -= 1;
        }
        self.print_prefix();
        match type_ {
            b'[' | b']' => tout().magenta(true),
            b's' | b'b' | b'c' => tout().green(false),
            b'e' => tout().green(true),
            b'p' | b'2' | b'3' | b'u' | b'v' | b'w' | b'x' | b'f' | b'=' => tout().blue(false),
            b't' => tout().cyan(false),
            b'd' => tout().blue(true),
            b'z' | b'!' => tout().cyan(true),
            b'-' => tout().normal(),
            b'/' => tout().yellow(true),
            b'a' | b'n' => tout().red(false),
            b'0' | b'1' | b'?' | b'i' => tout().bold(),
            b'L' | b'P' => {
                tout().bold();
                tout().underline();
            }
            b'(' | b')' => {
                tout().bold();
                tout().yellow(false);
            }
            b'{' | b'}' => tout().normal(),
            _ => {}
        }
        fputc(type_ as i32, out);
        if self.stable || type_ == b']' {
            tout().magenta(false);
        } else if self.preprocessing || type_ == b')' {
            tout().bold();
            tout().yellow(false);
        } else if type_ != b'L' && type_ != b'P' {
            tout().normal();
        }
        for r in reports.iter() {
            fputc(b' ' as i32, out);
            fputs(&r.buffer, out);
        }
        if self.stable || type_ == b'L' || type_ == b'P' || type_ == b']' {
            tout().normal();
        }
        fputc(b'\n' as i32, out);
        fflush(out);
    }
}
