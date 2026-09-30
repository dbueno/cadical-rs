//! Port of `parse.hpp` and `parse.cpp`: parsing of DIMACS and solution
//! files.

use crate::external::External;
use crate::file::File;
use crate::internal::Internal;
use crate::solver::Solver;

/// Force reading even if header is broken.
pub const FORCED: i32 = 0;
/// Relaxed white space treatment in header.
pub const RELAXED: i32 = 1;
/// Strict white space and header compliance.
pub const STRICT: i32 = 2;

pub struct Parser {
    pub solver: *mut Solver,
    pub internal: *mut Internal,
    pub external: *mut External,
    pub file: *mut File,
    /// `bool *parse_inccnf_too` (may be null).
    pub parse_inccnf_too: *mut bool,
    /// `vector<int> *cubes` (may be null).
    pub cubes: *mut Vec<i32>,
}

impl Parser {
    /// `Parser (Solver *s, File *f, bool *i, vector<int> *c)`.
    pub fn new(s: *mut Solver, f: *mut File, i: *mut bool, c: *mut Vec<i32>) -> Parser {
        // SAFETY: 's' is a live solver.
        let (internal, external) = unsafe { ((*s).internal, (*s).external) };
        Parser { solver: s, internal, external, file: f, parse_inccnf_too: i, cubes: c }
    }
}

/*------------------------------------------------------------------------*/
// Port of the functions defined in 'parse.cpp'.

#[allow(unused_imports)]
use crate::prelude::*;
use crate::format::cfmt_f64;
use crate::terminal::tout;

const EOF: i32 = libc::EOF;

#[inline]
fn isdigit(ch: i32) -> bool {
    (b'0' as i32..=b'9' as i32).contains(&ch)
}

/// C 'isspace' in the "C" locale.
#[inline]
fn isspace(ch: i32) -> bool {
    ch == b' ' as i32 || (b'\t' as i32..=b'\r' as i32).contains(&ch)
}

/// Returned by 'parse_lit' if an 'a' is found (compared by content, the
/// C++ code compares the pointer).
static CUBE_TOKEN: &str = "unexpected 'a' in CNF";

// Parse error.

macro_rules! per {
    ($self:ident, $($arg:tt)+) => {{
        return Some($self.parse_error(format_args!($($arg)+)));
    }};
}

impl Parser {
    #[inline]
    fn file(&self) -> &mut File {
        // SAFETY: the file is alive during parsing.
        unsafe { &mut *self.file }
    }

    #[inline]
    fn internal(&self) -> &mut Internal {
        // SAFETY: the solver (and its internal) is alive during parsing.
        unsafe { &mut *self.internal }
    }

    #[inline]
    fn external(&self) -> &mut External {
        // SAFETY: the solver (and its external) is alive during parsing.
        unsafe { &mut *self.external }
    }

    #[inline]
    fn solver(&self) -> &mut Solver {
        // SAFETY: the solver is alive during parsing.
        unsafe { &mut *self.solver }
    }

    /// The 'PER' macro: initialize 'internal->error_message' with the
    /// position prefix and append the actual message.
    fn parse_error(&mut self, args: std::fmt::Arguments<'_>) -> String {
        let name = self.file().name().to_string();
        let lineno = self.file().lineno();
        let internal = self.internal();
        internal.error_message.init(format_args!("{}:{}: parse error: ", name, lineno));
        internal.error_message.append(args).to_string()
    }

    /*--------------------------------------------------------------------*/

    // Parsing utilities.

    #[inline]
    pub fn parse_char(&mut self) -> i32 {
        self.file().get()
    }

    /// Return an non zero error string if a parse error occurred.
    pub fn parse_string(&mut self, str: &str, mut prev: u8) -> Option<String> {
        for &p in str.as_bytes() {
            if self.parse_char() == p as i32 {
                prev = p;
            } else if p == b' ' {
                per!(self, "expected space after '{}'", prev as char);
            } else {
                per!(self, "expected '{}' after '{}'", p as char, prev as char);
            }
        }
        None
    }

    pub fn parse_positive_int(&mut self, ch: &mut i32, res: &mut i32, name: &str) -> Option<String> {
        debug_assert!(isdigit(*ch));
        *res = *ch - b'0' as i32;
        loop {
            *ch = self.parse_char();
            if !isdigit(*ch) {
                break;
            }
            let digit = *ch - b'0' as i32;
            if i32::MAX / 10 < *res || i32::MAX - digit < 10 * *res {
                per!(self, "too large '{}' in header", name);
            }
            *res = 10 * *res + digit;
        }
        None
    }

    pub fn parse_positive_uint64_t(&mut self, ch: &mut i32, res: &mut u64, name: &str) -> Option<String> {
        debug_assert!(isdigit(*ch));
        *res = (*ch - b'0' as i32) as u64;
        loop {
            *ch = self.parse_char();
            if !isdigit(*ch) {
                break;
            }
            let digit = (*ch - b'0' as i32) as u64;
            if u64::MAX / 10 < *res || u64::MAX - digit < 10 * *res {
                per!(self, "too large '{}' in header", name);
            }
            *res = 10 * *res + digit;
        }
        None
    }

    pub fn parse_lit(&mut self, ch: &mut i32, lit: &mut i32, vars: &mut i32, strict: i32) -> Option<String> {
        if *ch == b'a' as i32 {
            return Some(CUBE_TOKEN.to_string());
        }
        let sign: i32;
        if *ch == b'-' as i32 {
            *ch = self.parse_char();
            if !isdigit(*ch) {
                per!(self, "expected digit after '-'");
            }
            sign = -1;
        } else if !isdigit(*ch) {
            per!(self, "expected digit or '-'");
        } else {
            sign = 1;
        }
        *lit = *ch - b'0' as i32;
        loop {
            *ch = self.parse_char();
            if !isdigit(*ch) {
                break;
            }
            let digit = *ch - b'0' as i32;
            if i32::MAX / 10 < *lit || i32::MAX - digit < 10 * *lit {
                per!(self, "literal too large");
            }
            *lit = 10 * *lit + digit;
        }
        if *ch == b'\r' as i32 {
            *ch = self.parse_char();
        }
        if *ch != b'c' as i32
            && *ch != b' ' as i32
            && *ch != b'\t' as i32
            && *ch != b'\n' as i32
            && *ch != EOF
        {
            per!(self, "expected white space after '{}'", sign * *lit);
        }
        if *lit > *vars {
            if strict != FORCED {
                per!(self, "literal {} exceeds maximum variable {}", sign * *lit, *vars);
            } else {
                *vars = *lit;
            }
        }
        *lit *= sign;
        None
    }

    /*--------------------------------------------------------------------*/

    // Parsing CNF in DIMACS format.

    pub fn parse_dimacs_non_profiled(&mut self, vars: &mut i32, mut strict: i32) -> Option<String> {
        let mut start = self.internal().time();

        let mut found_inccnf_header = false;
        let mut ch: i32;
        let mut declared: i32 = 0;
        let mut clauses: u64 = 0;

        *vars = 0;

        // First read comments before header with possibly embedded options.
        //
        loop {
            ch = self.parse_char();
            if strict != STRICT
                && (ch == b' ' as i32 || ch == b'\n' as i32 || ch == b'\t' as i32 || ch == b'\r' as i32)
            {
                continue;
            }
            if ch != b'c' as i32 {
                break;
            }
            let mut buf: Vec<u8> = Vec::new();
            loop {
                ch = self.parse_char();
                if ch == b'\n' as i32 {
                    break;
                }
                if ch == EOF {
                    per!(self, "unexpected end-of-file in header comment");
                } else if ch != b'\r' as i32 {
                    buf.push(ch as u8);
                }
            }
            // C++ uses 'buf.c_str ()' which stops at the first zero byte.
            if let Some(z) = buf.iter().position(|&b| b == 0) {
                buf.truncate(z);
            }
            let o = match buf.iter().position(|&b| b == b'-') {
                Some(pos) => String::from_utf8_lossy(&buf[pos..]).into_owned(),
                None => continue,
            };
            phase!(self.internal, "parse-dimacs", "found option '{}'", o);
            if !o.is_empty() {
                self.solver().set_long_option(&o);
            }
        }

        if ch != b'p' as i32 {
            per!(self, "expected 'c' or 'p'");
        }

        ch = self.parse_char();
        if strict == STRICT {
            if ch != b' ' as i32 {
                per!(self, "expected space after 'p'");
            }
            ch = self.parse_char();
        } else if ch != b' ' as i32 && ch != b'\t' as i32 {
            per!(self, "expected white space after 'p'");
        } else {
            loop {
                ch = self.parse_char();
                if !(ch == b' ' as i32 || ch == b'\t' as i32) {
                    break;
                }
            }
        }

        // Now read 'p cnf <var> <clauses>' header of DIMACS file
        // or 'p inccnf' of incremental 'INCCNF' file.
        //
        if ch == b'c' as i32 {
            debug_assert!(!found_inccnf_header);
            if strict == STRICT {
                let err = self.parse_string("nf ", b'c');
                if err.is_some() {
                    return err;
                }
                ch = self.parse_char();
                if !isdigit(ch) {
                    per!(self, "expected digit after 'p cnf '");
                }
                let err = self.parse_positive_int(&mut ch, vars, "<max-var>");
                if err.is_some() {
                    return err;
                }
                if ch != b' ' as i32 {
                    per!(self, "expected ' ' after 'p cnf {}'", *vars);
                }
                ch = self.parse_char();
                if !isdigit(ch) {
                    per!(self, "expected digit after 'p cnf {} '", *vars);
                }
                let err = self.parse_positive_uint64_t(&mut ch, &mut clauses, "<num-clauses>");
                if err.is_some() {
                    return err;
                }
                if ch != b'\n' as i32 {
                    per!(self, "expected new-line after 'p cnf {} {}'", *vars, clauses);
                }
            } else {
                if self.parse_char() != b'n' as i32 {
                    per!(self, "expected 'n' after 'p c'");
                }
                if self.parse_char() != b'f' as i32 {
                    per!(self, "expected 'f' after 'p cn'");
                }
                ch = self.parse_char();
                if !isspace(ch) {
                    per!(self, "expected space after 'p cnf'");
                }
                loop {
                    ch = self.parse_char();
                    if !isspace(ch) {
                        break;
                    }
                }
                if !isdigit(ch) {
                    per!(self, "expected digit after 'p cnf '");
                }
                let err = self.parse_positive_int(&mut ch, vars, "<max-var>");
                if err.is_some() {
                    return err;
                }
                if !isspace(ch) {
                    per!(self, "expected space after 'p cnf {}'", *vars);
                }
                loop {
                    ch = self.parse_char();
                    if !isspace(ch) {
                        break;
                    }
                }
                if !isdigit(ch) {
                    per!(self, "expected digit after 'p cnf {} '", *vars);
                }
                let err = self.parse_positive_uint64_t(&mut ch, &mut clauses, "<num-clauses>");
                if err.is_some() {
                    return err;
                }
                while ch != b'\n' as i32 {
                    if ch != b'\r' as i32 && !isspace(ch) {
                        per!(self, "expected new-line after 'p cnf {} {}'", *vars, clauses);
                    }
                    ch = self.parse_char();
                }
            }

            msg!(
                self.internal,
                "found {}'p cnf {} {}'{} header",
                tout().green_code(),
                *vars,
                clauses,
                tout().normal_code()
            );

            if *vars != 0 {
                debug_assert!(*vars > 0);
                self.solver().resize(*vars);
                declared = *vars;
            }

            // 'reserve_ids (int)' takes an 'int' (truncating conversion).
            self.internal().reserve_ids(clauses as i32);
        } else if self.parse_inccnf_too.is_null() {
            per!(self, "expected 'c' after 'p '");
        } else if ch == b'i' as i32 {
            found_inccnf_header = true;
            let err = self.parse_string("nccnf", b'i');
            if err.is_some() {
                return err;
            }
            ch = self.parse_char();
            if strict == STRICT {
                if ch != b'\n' as i32 {
                    per!(self, "expected new-line after 'p inccnf'");
                }
            } else {
                while ch != b'\n' as i32 {
                    if ch != b'\r' as i32 && !isspace(ch) {
                        per!(self, "expected new-line after 'p inccnf'");
                    }
                    ch = self.parse_char();
                }
            }

            msg!(self.internal, "found {}'p inccnf'{} header", tout().green_code(), tout().normal_code());

            // Cube & Conquer 'inccnf' format is not compatible with factor:
            self.internal().opts.factor = 0;

            strict = FORCED;
        } else {
            per!(self, "expected 'c' or 'i' after 'p '");
        }

        if !self.parse_inccnf_too.is_null() {
            // SAFETY: non-null pointer to caller owned flag.
            unsafe { *self.parse_inccnf_too = false };
        }

        // Now read body of DIMACS part.
        //
        let mut lit: i32 = 0;
        let mut parsed: u64 = 0;
        loop {
            ch = self.parse_char();
            if ch == EOF {
                break;
            }
            if ch == b' ' as i32 || ch == b'\n' as i32 || ch == b'\t' as i32 || ch == b'\r' as i32 {
                continue;
            }
            if ch == b'c' as i32 {
                loop {
                    ch = self.parse_char();
                    if ch == b'\n' as i32 || ch == EOF {
                        break;
                    }
                }
                if ch == EOF {
                    break;
                }
                continue;
            }
            if self.internal().terminated_asynchronously(1) {
                return Some("parsing interrupted by signal".to_string());
            }
            if ch == b'a' as i32 && found_inccnf_header {
                break;
            }
            let err = self.parse_lit(&mut ch, &mut lit, vars, strict);
            if err.is_some() {
                return err;
            }
            if ch == b'c' as i32 {
                loop {
                    ch = self.parse_char();
                    if ch == b'\n' as i32 {
                        break;
                    }
                    if ch == EOF {
                        per!(self, "unexpected end-of-file in comment");
                    }
                }
            }
            if *vars > declared {
                debug_assert!(strict == FORCED);
                let more_vars = *vars - declared;
                debug_assert!(more_vars > 0);
                let start = self.solver().declare_more_variables(more_vars);
                debug_assert!(*vars == start + more_vars - 1);
                let _ = start;
                declared = *vars;
            }
            self.solver().add(lit);
            if !found_inccnf_header && lit == 0 && {
                let p = parsed;
                parsed += 1;
                p >= clauses
            } && strict != FORCED
            {
                per!(self, "too many clauses");
            }
        }

        if lit != 0 {
            per!(self, "last clause without terminating '0'");
        }

        if !found_inccnf_header && parsed < clauses && strict != FORCED {
            per!(self, "clause missing");
        }

        let end = self.internal().time();
        msg!(
            self.internal,
            "parsed {} clauses in {} seconds {} time",
            parsed,
            cfmt_f64("%.2f", end - start),
            if self.internal().opts.realtime != 0 { "real" } else { "process" }
        );

        start = end;
        let mut num_cubes: usize = 0;
        if ch == b'a' as i32 {
            debug_assert!(!self.parse_inccnf_too.is_null());
            debug_assert!(found_inccnf_header);
            // SAFETY: non-null pointer to caller owned flag.
            unsafe {
                if !*self.parse_inccnf_too {
                    *self.parse_inccnf_too = true;
                }
            }
            loop {
                ch = self.parse_char();
                if ch == b' ' as i32 || ch == b'\n' as i32 || ch == b'\t' as i32 || ch == b'\r' as i32 {
                    continue;
                }
                if ch == b'c' as i32 {
                    loop {
                        ch = self.parse_char();
                        if ch == b'\n' as i32 || ch == EOF {
                            break;
                        }
                    }
                    if ch == EOF {
                        break;
                    }
                    continue;
                }
                if self.internal().terminated_asynchronously(1) {
                    return Some("parsing interrupted by signal".to_string());
                }
                let err = self.parse_lit(&mut ch, &mut lit, vars, strict);
                if err.as_deref() == Some(CUBE_TOKEN) {
                    per!(self, "two 'a' in a row");
                } else if err.is_some() {
                    return err;
                }
                if ch == b'c' as i32 {
                    loop {
                        ch = self.parse_char();
                        if ch == b'\n' as i32 {
                            break;
                        }
                        if ch == EOF {
                            per!(self, "unexpected end-of-file in comment");
                        }
                    }
                }
                if !self.cubes.is_null() {
                    // SAFETY: non-null pointer to caller owned vector.
                    unsafe { (*self.cubes).push(lit) };
                }
                if lit == 0 {
                    num_cubes += 1;
                    loop {
                        ch = self.parse_char();
                        if ch == b' ' as i32 || ch == b'\n' as i32 || ch == b'\t' as i32 || ch == b'\r' as i32 {
                            continue;
                        }
                        if ch == b'c' as i32 {
                            loop {
                                ch = self.parse_char();
                                if ch == b'\n' as i32 || ch == EOF {
                                    break;
                                }
                            }
                            if ch == EOF {
                                break;
                            }
                        }
                        if ch == EOF {
                            break;
                        }
                        if ch != b'a' as i32 {
                            per!(self, "expected 'a' or end-of-file after zero");
                        }
                        lit = i32::MIN;
                        break;
                    }
                    if ch == EOF {
                        break;
                    }
                }
            }
            if lit != 0 {
                per!(self, "last cube without terminating '0'");
            }
        }
        if found_inccnf_header {
            let end = self.internal().time();
            msg!(
                self.internal,
                "parsed {} cubes in {} seconds {} time",
                num_cubes as isize,
                cfmt_f64("%.2f", end - start),
                if self.internal().opts.realtime != 0 { "real" } else { "process" }
            );
        }
        None
    }

    /*--------------------------------------------------------------------*/

    // Parsing solution in competition output format.

    pub fn parse_solution_non_profiled(&mut self) -> Option<String> {
        {
            let external = self.external();
            let n = (external.max_var as u32).wrapping_add(1) as usize;
            external.solution = Some(vec![0i8; n]);
            external.solution_size = external.max_var;
        }
        let mut ch: i32;
        loop {
            if self.internal().terminated_asynchronously(1) {
                return Some("parsing solution interrupted by signal".to_string());
            }
            ch = self.parse_char();
            if ch == EOF {
                per!(self, "missing 's' line");
            } else if ch == b'c' as i32 {
                loop {
                    ch = self.parse_char();
                    if ch == b'\n' as i32 {
                        break;
                    }
                    if ch == EOF {
                        per!(self, "unexpected end-of-file in comment");
                    }
                }
            } else if ch == b's' as i32 {
                break;
            } else {
                per!(self, "expected 'c' or 's'");
            }
        }
        let err = self.parse_string(" SATISFIABLE", b's');
        if err.is_some() {
            return err;
        }
        ch = self.parse_char();
        if ch == b'\r' as i32 {
            ch = self.parse_char();
        }
        if ch != b'\n' as i32 {
            per!(self, "expected new-line after 's SATISFIABLE'");
        }
        let mut count: i32 = 0;
        loop {
            ch = self.parse_char();
            if ch != b'v' as i32 {
                per!(self, "expected 'v' at start-of-line");
            }
            ch = self.parse_char();
            if ch != b' ' as i32 {
                per!(self, "expected ' ' after 'v'");
            }
            let mut lit: i32 = 0;
            ch = self.parse_char();
            loop {
                if ch == b' ' as i32 || ch == b'\t' as i32 {
                    ch = self.parse_char();
                    if ch != b'\n' as i32 {
                        continue;
                    } else {
                        break;
                    }
                }
                // 'parse_lit (ch, lit, external->max_var, false)'.
                let external = self.external;
                // SAFETY: 'external' outlives the parser; 'max_var' is not
                // otherwise accessed during 'parse_lit'.
                let err = self.parse_lit(&mut ch, &mut lit, unsafe { &mut (*external).max_var }, 0);
                if err.is_some() {
                    return err;
                }
                if ch == b'c' as i32 {
                    per!(self, "unexpected comment");
                }
                if lit == 0 {
                    break;
                }
                let idx = lit.abs() as usize;
                if self.external().solution.as_ref().unwrap()[idx] != 0 {
                    per!(self, "variable {} occurs twice", lit.abs());
                }
                log!(self.internal, "solution {}", lit);
                self.external().solution.as_mut().unwrap()[idx] = sign(lit) as i8;
                count += 1;
                if ch == b'\r' as i32 {
                    ch = self.parse_char();
                }
                if ch == b'\n' as i32 {
                    break;
                }
            }
            if lit == 0 {
                break;
            }
        }
        let max_var = self.external().max_var;
        msg!(
            self.internal,
            "parsed {} values {}%",
            count,
            cfmt_f64("%.2f", percent(count as f64, max_var as f64))
        );
        None
    }

    /*--------------------------------------------------------------------*/

    // Wrappers to profile parsing and at the same time use the convenient
    // implicit 'return' in PER in the non-profiled versions.

    pub fn parse_dimacs(&mut self, vars: &mut i32, strict: i32) -> Option<String> {
        debug_assert!(strict == FORCED || strict == RELAXED || strict == STRICT);
        start!(self.internal(), parse);
        let err = self.parse_dimacs_non_profiled(vars, strict);
        stop!(self.internal(), parse);
        err
    }

    pub fn parse_solution(&mut self) -> Option<String> {
        start!(self.internal(), parse);
        let err = self.parse_solution_non_profiled();
        stop!(self.internal(), parse);
        err
    }
}
