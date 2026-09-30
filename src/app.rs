//! Port of `cadical.cpp`: the stand-alone solver application (`App`).
//!
//! A wrapper app which makes up the CaDiCaL stand alone solver.  It in
//! essence only consists of the 'App::main' function.  So this class
//! contains code, which is not required if only the library interface in
//! the class 'Solver' is used (defined in 'cadical.hpp').  It further uses
//! static data structures in order to have a signal handler catch signals.
//!
//! It is thus neither thread-safe nor reentrant.  If you want to use
//! multiple instances of the solver use the 'Solver' interface directly
//! which is thread-safe and reentrant among different solver instances.
//!
//! In C++ `App` is both the signal `Handler` and the `Terminator`
//! connected to its own solver.  Since the solver owns connected
//! terminators, the port shares the `timesup` flag (an `Arc<AtomicBool>`)
//! with a small terminator object (`AppTerminator`).

use std::sync::atomic::{AtomicBool, AtomicI32, Ordering::Relaxed};
use std::sync::Arc;

use crate::file::File;
use crate::format::cfmt_f64;
use crate::message::{c_stdin, c_stdout, fflush, fputc, fputs};
use crate::options::Options;
use crate::resources::absolute_process_time;
use crate::signal::{Handler, Signal};
use crate::solver::{Solver, Terminator};
use crate::terminal::{terr, tout};
use crate::util::{has_prefix, has_suffix, is_color_option, is_no_color_option, parse_int_str, percent, relative};
use crate::version::{affiliations, authors, copyright, version};

pub struct App {
    /// Global solver.
    pub solver: Option<Box<Solver>>,

    /// Command line option `-t <sec>`.
    pub time_limit: i32,

    /// Strictness of (DIMACS) parsing:
    ///
    ///  0 = force parsing and completely ignore header
    ///  1 = relaxed header handling (default)
    ///  2 = strict header handling
    ///
    /// To use '0' use '-f' of '--force'.
    /// To use '2' use '--strict'.
    pub force_strict_parsing: i32,

    pub force_writing: bool,

    /// Set after parsing.
    pub max_var: i32,
    /// Asynchronous termination (`volatile bool timesup`).
    pub timesup: Arc<AtomicBool>,
    /// Caught signal (`volatile sig_atomic_t signal_value`).
    pub signal_value: AtomicI32,
    /// `solver->internal->termination_forced` (shared flag, cloned in
    /// 'init' so that the signal handler does not need to go through the
    /// solver).
    termination_forced: Option<Arc<AtomicBool>>,
}

/// The `Terminator` part of the C++ `App` (`bool terminate () { return
/// timesup; }`), connected to the solver when a time limit is given.
struct AppTerminator {
    timesup: Arc<AtomicBool>,
}

impl Terminator for AppTerminator {
    fn terminate(&mut self) -> bool {
        self.timesup.load(Relaxed)
    }
}

/*------------------------------------------------------------------------*/

impl App {
    /// `App ()`: only partially initialize the app.
    pub fn new() -> App {
        App {
            solver: None,
            time_limit: 0,
            force_strict_parsing: 0,
            force_writing: false,
            max_var: 0,
            timesup: Arc::new(AtomicBool::new(false)),
            signal_value: AtomicI32::new(0),
            termination_forced: None,
        }
    }

    #[inline]
    fn solver(&mut self) -> &mut Solver {
        self.solver.as_mut().expect("solver initialized")
    }

    /// `print_usage (bool all = false)`.
    pub fn print_usage(&mut self, all: bool) {
        let out = c_stdout();
        fputs(
            "usage: cadical [ <option> ... ] [ <input> [ <proof> ] ]\n\
             \n\
             where '<option>' is one of the following common options:\n\
             \n",
            out,
        );

        if !all {
            // Print only a short list of common options.
            fputs(
                "  -h             print this short list of common options\n\
                 \x20 --help         print complete list of all options\n\
                 \x20 --version      print version\n\
                 \n\
                 \x20 -n             do not print witness\n\
                 \x20 -v             increase verbosity\n\
                 \x20 -q             be quiet\n\
                 \n\
                 \x20 -t <sec>       set wall clock time limit\n",
                out,
            );
        } else {
            // Print complete list of all options.
            fputs(
                "  -h             print alternatively only a list of common options\n\
                 \x20 --help         print this complete list of all options\n\
                 \x20 --version      print version\n\
                 \n\
                 \x20 -n             do not print witness (same as '--no-witness')\n\
                 \x20 -v             increase verbosity (see also '--verbose' below)\n\
                 \x20 -q             be quiet (same as '--quiet')\n\
                 \x20 -t <sec>       set wall clock time limit\n\
                 \n\
                 Or '<option>' is one of the less common options\n\
                 \n\
                 \x20 -L<rounds>     run local search initially (default '0' rounds)\n\
                 \x20 -O<level>      increase limits by '2^<level>' or '10^<level>'\n\
                 \x20 -P<rounds>     initial preprocessing (default '0' rounds)\n\
                 \n\
                 Note there is no separating space for the options above while the\n\
                 following options require a space after the option name:\n\
                 \n\
                 \x20 -c <limit>     limit the number of conflicts (default unlimited)\n\
                 \x20 -d <limit>     limit the number of decisions (default unlimited)\n\
                 \n\
                 \x20 -o <output>    write simplified CNF in DIMACS format to file\n\
                 \x20 -e <extend>    write reconstruction/extension stack to file\n",
                out,
            );
            #[cfg(feature = "logging")]
            fputs("  -l             enable logging messages (same as '--log')\n", out);
            fputs(
                "\n\
                 \x20 --force | -f   parsing broken DIMACS header and writing proofs\n\
                 \x20 --strict       strict parsing (no white space in header)\n\
                 \n\
                 \x20 -r <sol>       read solution in competition output format\n\
                 \x20                to check consistency of learned clauses\n\
                 \x20                during testing and debugging\n\
                 \n\
                 \x20 -w <sol>       write result including a potential witness\n\
                 \x20                solution in competition format to the given file\n\
                 \n\
                 \x20 --colors       force colored output\n\
                 \x20 --no-colors    disable colored output to terminal\n\
                 \x20 --no-witness   do not print witness (see also '-n' above)\n\
                 \n\
                 \x20 --build        print build configuration\n\
                 \x20 --copyright    print copyright information\n",
                out,
            );

            fputs(
                "\n\
                 There are pre-defined configurations of advanced internal options:\n\
                 \n",
                out,
            );

            Solver::configurations();

            fputs(
                "\n\
                 Or '<option>' is one of the following advanced internal options:\n\
                 \n",
                out,
            );

            Solver::usage();

            fputs(
                "\n\
                 The internal options have their default value printed in brackets\n\
                 after their description.  They can also be used in the form\n\
                 '--<name>' which is equivalent to '--<name>=1' and in the form\n\
                 '--no-<name>' which is equivalent to '--<name>=0'.  One can also\n\
                 use 'true' instead of '1', 'false' instead of '0', as well as\n\
                 numbers with positive exponent such as '1e3' instead of '1000'.\n\
                 \n\
                 Alternatively option values can also be specified in the header\n\
                 of the DIMACS file, e.g., 'c --elim=false', or through environment\n\
                 variables, such as 'CADICAL_ELIM=false'.  The embedded options in\n\
                 the DIMACS file have highest priority, followed by command line\n\
                 options and then values specified through environment variables.\n",
                out,
            );
        }

        //--------------------------------------------------------------------
        // Common to both complete and common option usage.

        fputs(
            "\n\
             The input is read from '<input>' assumed to be in DIMACS format.\n\
             Incremental 'p inccnf' files are supported too with cubes at the end.\n\
             If '<proof>' is given then a DRAT proof is written to that file.\n",
            out,
        );

        //--------------------------------------------------------------------
        // More explanations for complete option usage.

        if all {
            fputs(
                "\n\
                 If '<input>' is missing then the solver reads from '<stdin>',\n\
                 also if '-' is used as input path name '<input>'.  Similarly,\n\
                 \n\
                 For incremental files each cube is solved in turn. The solver\n\
                 stops at the first satisfied cube if there is one and uses that\n\
                 one for the witness to print.  Conflict and decision limits are\n\
                 applied to each individual cube solving call while '-P', '-L' and\n\
                 '-t' remain global.  Only if all cubes were unsatisfiable the solver\n\
                 prints the standard unsatisfiable solution line ('s UNSATISFIABLE').\n\
                 \n\
                 By default the proof is stored in the binary DRAT format unless\n\
                 the option '--no-binary' is specified or the proof is written\n\
                 to '<stdout>' and '<stdout>' is connected to a terminal.\n\
                 \n\
                 The input is assumed to be compressed if it is given explicitly\n\
                 and has a '.gz', '.bz2', '.xz' or '.7z' suffix.  The same applies\n\
                 to the output file.  In order to use compression and decompression\n\
                 the corresponding utilities 'gzip', 'bzip', 'xz', and '7z' (depending\n\
                 on the format) are required and need to be installed on the system.\n\
                 The solver checks file type signatures though and falls back to\n\
                 non-compressed file reading if the signature does not match.\n",
                out,
            );
        }
    }

    /*----------------------------------------------------------------------*/

    /// Pretty print competition format witness with 'v' lines.
    pub fn print_witness(&mut self, file: *mut libc::FILE) {
        let max_var = self.max_var;
        let mut c = 0;
        let mut i = 0;
        // Uninitialized in C++ (only read after 'continue' in the very
        // first iteration, where any non-zero value is the sensible one).
        let mut tmp: i32 = 1;
        loop {
            if c == 0 {
                fputc(b'v' as i32, file);
                c = 1;
            }
            let skip;
            if {
                let old = i;
                i += 1;
                old == max_var
            } {
                tmp = 0;
                skip = false;
            } else if self.solver().external().ervars.get(i as usize).copied().unwrap_or(false) {
                skip = true;
            } else {
                tmp = if self.solver().val(i) < 0 { -i } else { i };
                skip = false;
            }
            if !skip {
                if self.signal_value.load(Relaxed) != 0 {
                    break;
                }
                let str = format!(" {}", tmp);
                let l = str.len() as i32;
                if c + l > 78 {
                    fputs("\nv", file);
                    c = 1;
                }
                fputs(&str, file);
                c += l;
            }
            if tmp == 0 {
                break;
            }
        }
        if c != 0 {
            fputc(b'\n' as i32, file);
        }
    }

    /*----------------------------------------------------------------------*/

    pub fn signal_message(&mut self, msg: &str, sig: i32) {
        self.solver().message(format_args!(
            "{}{} {}signal {}{} ({}){}",
            tout().red_code(),
            msg,
            tout().bright_red_code(),
            sig,
            tout().red_code(),
            Signal::name(sig),
            tout().normal_code()
        ));
    }

    /*----------------------------------------------------------------------*/

    // Wrapper around option setting.

    /// C++ overload `bool set (const char *)` (long option).
    pub fn set_long_option(&mut self, arg: &str) -> bool {
        self.solver().set_long_option(arg)
    }

    /// C++ overload `bool set (const char *, int)`.
    pub fn set(&mut self, name: &str, val: i32) -> bool {
        self.solver().set(name, val)
    }

    pub fn get(&mut self, name: &str) -> i32 {
        self.solver().get(name)
    }

    /// `bool verbose () { return get ("verbose") && !get ("quiet"); }`
    pub fn verbose(&mut self) -> bool {
        self.get("verbose") != 0 && self.get("quiet") == 0
    }

    /*----------------------------------------------------------------------*/

    /// The real initialization is delayed.
    pub fn init(&mut self) {
        debug_assert!(self.solver.is_none());

        self.time_limit = -1;
        self.force_strict_parsing = 1;
        self.force_writing = false;
        self.max_var = 0;
        self.timesup.store(false, Relaxed);

        // Call 'new Solver' only after setting 'reportdefault' and do not
        // add this call to the member initialization above. This is because
        // for stand-alone usage the default report default value is 'true'
        // while for library usage it should remain 'false'.  See the
        // explanation in 'options.hpp' related to 'reportdefault' for
        // details.

        Options::set_reportdefault(1);
        self.solver = Some(Box::new(Solver::new()));
        self.termination_forced = Some(self.solver().internal().termination_forced.clone());
        Signal::set(self as *mut App as *mut dyn Handler);
    }

    /// Terminator interface: `bool terminate () { return timesup; }`.
    pub fn terminate(&self) -> bool {
        self.timesup.load(Relaxed)
    }

    /*----------------------------------------------------------------------*/

    pub fn most_likely_existing_cnf_file(path: &str) -> bool {
        if !File::exists(path) {
            return false;
        }

        if has_suffix(path, ".dimacs") {
            return true;
        }
        if has_suffix(path, ".dimacs.gz") {
            return true;
        }
        if has_suffix(path, ".dimacs.xz") {
            return true;
        }
        if has_suffix(path, ".dimacs.bz2") {
            return true;
        }
        if has_suffix(path, ".dimacs.7z") {
            return true;
        }
        if has_suffix(path, ".dimacs.lzma") {
            return true;
        }

        if has_suffix(path, ".cnf") {
            return true;
        }
        if has_suffix(path, ".cnf.gz") {
            return true;
        }
        if has_suffix(path, ".cnf.xz") {
            return true;
        }
        if has_suffix(path, ".cnf.bz2") {
            return true;
        }
        if has_suffix(path, ".cnf.7z") {
            return true;
        }
        if has_suffix(path, ".cnf.lzma") {
            return true;
        }

        false
    }

    /*----------------------------------------------------------------------*/

    /// Parse the arguments (including `argv[0]`) and run the solver.
    pub fn main(&mut self, argv: &[String]) -> i32 {
        let argc = argv.len();

        // Short-cut for errors to avoid a hard 'exit' ('APPERR').
        macro_rules! apperr {
            ($($arg:tt)+) => {
                self.solver().error(format_args!($($arg)+))
            };
        }

        // Handle options which lead to immediate exit first.

        if argc == 2 {
            let arg = argv[1].as_str();
            if arg == "-h" {
                self.print_usage(false);
                return 0;
            } else if arg == "--help" {
                self.print_usage(true);
                return 0;
            } else if arg == "--version" {
                cprintf!("{}\n", version());
                return 0;
            } else if arg == "--build" {
                tout().disable();
                Solver::build(c_stdout(), "");
                return 0;
            } else if arg == "--copyright" {
                cprintf!("{}\n", copyright());
                cprintf!("{}\n", authors());
                cprintf!("{}\n", affiliations());
                return 0;
            }
        }

        // Now initialize solver.

        self.init();

        // Set all argument option values to not used yet.

        let mut preprocessing_specified: Option<&str> = None;
        let mut optimization_specified: Option<&str> = None;
        let mut read_solution_path: Option<&str> = None;
        let mut write_result_path: Option<&str> = None;
        let mut dimacs_path: Option<&str> = None;
        let mut proof_path: Option<&str> = None;
        let mut proof_specified = false;
        let mut dimacs_specified = false;
        let mut optimize: i32 = 0;
        let mut preprocessing: i32 = 0;
        let mut localsearch: i32 = 0;
        let mut output_path: Option<&str> = None;
        let mut extension_path: Option<&str> = None;
        let mut conflict_limit: i32 = -1;
        let mut decision_limit: i32 = -1;
        let mut conflict_limit_specified: Option<&str> = None;
        let mut decision_limit_specified: Option<&str> = None;
        let mut localsearch_specified: Option<&str> = None;
        let mut time_limit_specified: Option<&str> = None;
        let mut witness = true;
        let mut less = false;
        let mut status = true;

        let mut i = 1;
        while i < argc {
            let a = argv[i].as_str();
            if a == "-h" || a == "--help" || a == "--build" || a == "--version" || a == "--copyright" {
                apperr!("can only use '{}' as single first option", a);
            } else if a == "-" {
                if proof_specified {
                    apperr!("too many arguments");
                } else if !dimacs_specified {
                    dimacs_specified = true;
                } else {
                    proof_specified = true;
                }
            } else if a == "-r" {
                i += 1;
                if i == argc {
                    apperr!("argument to '-r' missing");
                } else if let Some(p) = read_solution_path {
                    apperr!("multiple read solution file options '-r {}' and '-r {}'", p, argv[i]);
                } else {
                    read_solution_path = Some(argv[i].as_str());
                }
            } else if a == "-w" {
                i += 1;
                if i == argc {
                    apperr!("argument to '-w' missing");
                } else if let Some(p) = write_result_path {
                    apperr!("multiple solution file options '-w {}' and '-w {}'", p, argv[i]);
                } else {
                    write_result_path = Some(argv[i].as_str());
                }
            } else if a == "-o" {
                i += 1;
                if i == argc {
                    apperr!("argument to '-o' missing");
                } else if let Some(p) = output_path {
                    apperr!("multiple output file options '-o {}' and '-o {}'", p, argv[i]);
                } else if !self.force_writing && App::most_likely_existing_cnf_file(&argv[i]) {
                    apperr!("output file '{}' most likely existing CNF (use '-f')", argv[i]);
                } else if !File::writable(&argv[i]) {
                    apperr!("output file '{}' not writable", argv[i]);
                } else {
                    output_path = Some(argv[i].as_str());
                }
            } else if a == "-e" {
                i += 1;
                if i == argc {
                    apperr!("argument to '-e' missing");
                } else if let Some(p) = extension_path {
                    apperr!("multiple extension file options '-e {}' and '-e {}'", p, argv[i]);
                } else if !self.force_writing && App::most_likely_existing_cnf_file(&argv[i]) {
                    apperr!("extension file '{}' most likely existing CNF (use '-f')", argv[i]);
                } else if !File::writable(&argv[i]) {
                    apperr!("extension file '{}' not writable", argv[i]);
                } else {
                    extension_path = Some(argv[i].as_str());
                }
            } else if is_color_option(a) {
                tout().force_colors();
                terr().force_colors();
            } else if is_no_color_option(a) {
                tout().force_no_colors();
                terr().force_no_colors();
            } else if a == "--witness" || a == "--witness=true" || a == "--witness=1" {
                witness = true;
            } else if a == "-n" || a == "--no-witness" || a == "--witness=false" || a == "--witness=0" {
                witness = false;
            } else if a == "--status" || a == "--status=true" || a == "--status=1" {
                status = true;
            } else if a == "-n" || a == "--no-status" || a == "--status=false" || a == "--status=0" {
                status = false;
            } else if a == "--less" {
                // EXPERIMENTAL!
                // SAFETY: 'isatty'.
                if less {
                    apperr!("multiple '--less' options");
                } else if unsafe { libc::isatty(1) } == 0 {
                    apperr!("'--less' without '<stdout>' connected to terminal");
                } else {
                    less = true;
                }
            } else if a == "-c" {
                i += 1;
                if i == argc {
                    apperr!("argument to '-c' missing");
                } else if let Some(p) = conflict_limit_specified {
                    apperr!("multiple conflict limits '-c {}' and '-c {}'", p, argv[i]);
                } else if !parse_int_str(&argv[i], &mut conflict_limit) {
                    apperr!("invalid argument in '-c {}'", argv[i]);
                } else if conflict_limit < 0 {
                    apperr!("invalid conflict limit");
                } else {
                    conflict_limit_specified = Some(argv[i].as_str());
                }
            } else if a == "-d" {
                i += 1;
                if i == argc {
                    apperr!("argument to '-d' missing");
                } else if let Some(p) = decision_limit_specified {
                    apperr!("multiple decision limits '-d {}' and '-d {}'", p, argv[i]);
                } else if !parse_int_str(&argv[i], &mut decision_limit) {
                    apperr!("invalid argument in '-d {}'", argv[i]);
                } else if decision_limit < 0 {
                    apperr!("invalid decision limit");
                } else {
                    decision_limit_specified = Some(argv[i].as_str());
                }
            } else if a == "-t" {
                i += 1;
                if i == argc {
                    apperr!("argument to '-t' missing");
                } else if let Some(p) = time_limit_specified {
                    apperr!("multiple time limit '-t {}' and '-t {}'", p, argv[i]);
                } else if !parse_int_str(&argv[i], &mut self.time_limit) {
                    apperr!("invalid argument in '-d {}'", argv[i]);
                } else if self.time_limit < 0 {
                    apperr!("invalid time limit");
                } else {
                    time_limit_specified = Some(argv[i].as_str());
                }
            } else if a == "-q" {
                self.set_long_option("--quiet");
            } else if a == "-v" {
                let v = self.get("verbose") + 1;
                self.set("verbose", v);
            } else if cfg!(feature = "logging") && a == "-l" {
                self.set_long_option("--log");
            } else if a == "-f" || a == "--force" || a == "--force=1" || a == "--force=true" {
                self.force_strict_parsing = 0;
                self.force_writing = true;
            } else if a == "--strict" || a == "--strict=1" || a == "--strict=true" {
                self.force_strict_parsing = 2;
            } else if has_prefix(a, "-O") {
                if let Some(p) = optimization_specified {
                    apperr!("multiple optimization options '{}' and '{}'", p, a);
                }
                optimization_specified = Some(a);
                if !parse_int_str(&a[2..], &mut optimize) {
                    apperr!("invalid optimization option '{}'", a);
                }
                if !(0..=31).contains(&optimize) {
                    apperr!("invalid argument in '{}' (expected '0..31')", a);
                }
            } else if has_prefix(a, "-P") {
                if let Some(p) = preprocessing_specified {
                    apperr!("multiple preprocessing options '{}' and '{}'", p, a);
                }
                preprocessing_specified = Some(a);
                if !parse_int_str(&a[2..], &mut preprocessing) {
                    apperr!("invalid preprocessing option '{}'", a);
                }
                if preprocessing < 0 {
                    apperr!("invalid argument in '{}' (expected non-negative number)", a);
                }
            } else if has_prefix(a, "-L") {
                if let Some(p) = localsearch_specified {
                    apperr!("multiple local search options '{}' and '{}'", p, a);
                }
                localsearch_specified = Some(a);
                if !parse_int_str(&a[2..], &mut localsearch) {
                    apperr!("invalid local search option '{}'", a);
                }
                if localsearch < 0 {
                    apperr!("invalid argument in '{}' (expected non-negative number)", a);
                }
            } else if has_prefix(a, "--") && Solver::is_valid_configuration(&a[2..]) {
                self.solver().configure(&a[2..]);
            } else if self.set_long_option(a) {
                /* nothing do be done */
            } else if a.as_bytes().first() == Some(&b'-') {
                apperr!("invalid option '{}'", a);
            } else if proof_specified {
                apperr!("too many arguments");
            } else if dimacs_specified {
                proof_path = Some(a);
                proof_specified = true;
                if !self.force_writing && App::most_likely_existing_cnf_file(a) {
                    apperr!("DRAT proof file '{}' most likely existing CNF (use '-f')", a);
                } else if !File::writable(a) {
                    apperr!("DRAT proof file '{}' not writable", a);
                }
            } else {
                dimacs_specified = true;
                dimacs_path = Some(a);
            }
            i += 1;
        }

        /*--------------------------------------------------------------------*/

        if dimacs_specified {
            if let Some(d) = dimacs_path {
                if !File::exists(d) {
                    apperr!("DIMACS input file '{}' does not exist", d);
                }
            }
        }
        if let Some(r) = read_solution_path {
            if !File::exists(r) {
                apperr!("solution file '{}' does not exist", r);
            }
        }
        if dimacs_specified && proof_specified {
            if let (Some(d), Some(p)) = (dimacs_path, proof_path) {
                if d == p && d != "-" {
                    apperr!("DIMACS input file '{}' also specified as DRAT proof file", d);
                }
            }
        }

        /*--------------------------------------------------------------------*/
        // The '--less' option is not fully functional yet (it is also not
        // mentioned in the 'usage' message yet).  It only works as expected
        // if you let the solver run until it exits.  The goal is to have a
        // similar experience as with 'git diff' if the terminal is too small
        // for the printed messages, but this needs substantial hacking.
        //
        // TODO: add proper forking, waiting, signal catching & propagating ...
        //
        let less_pipe: *mut libc::FILE;
        if less {
            // SAFETY: plain POSIX calls.
            unsafe {
                debug_assert!(libc::isatty(1) != 0);
                less_pipe = libc::popen(b"less -r\0".as_ptr() as *const libc::c_char, b"w\0".as_ptr() as *const libc::c_char);
                if less_pipe.is_null() {
                    apperr!("could not execute and open pipe to 'less -r' command");
                }
                libc::dup2(libc::fileno(less_pipe), 1);
            }
        } else {
            less_pipe = std::ptr::null_mut();
        }

        /*--------------------------------------------------------------------*/

        if read_solution_path.is_some() && self.get("check") == 0 {
            self.set_long_option("--check");
        }
        if self.get("quiet") == 0 {
            let solver = self.solver();
            solver.section("banner");
            solver.message(format_args!(
                "{}CaDiCaL SAT Solver{}",
                tout().bright_magenta_code(),
                tout().normal_code()
            ));
            solver.message(format_args!("{}{}{}", tout().bright_magenta_code(), copyright(), tout().normal_code()));
            solver.message(format_args!("{}{}{}", tout().bright_magenta_code(), authors(), tout().normal_code()));
            solver.message(format_args!(
                "{}{}{}",
                tout().bright_magenta_code(),
                affiliations(),
                tout().normal_code()
            ));
            solver.message_empty();
            Solver::build(c_stdout(), "c ");
        }
        if preprocessing > 0
            || localsearch > 0
            || self.time_limit >= 0
            || conflict_limit >= 0
            || decision_limit >= 0
        {
            self.solver().section("limit");
            if preprocessing > 0 {
                self.solver().message(format_args!(
                    "enabling {} initial rounds of preprocessing (due to '{}')",
                    preprocessing,
                    preprocessing_specified.unwrap_or("")
                ));
                self.solver().limit("preprocessing", preprocessing);
            }
            if localsearch > 0 {
                self.solver().message(format_args!(
                    "enabling {} initial rounds of local search (due to '{}')",
                    localsearch,
                    localsearch_specified.unwrap_or("")
                ));
                self.solver().limit("localsearch", localsearch);
            }
            if self.time_limit >= 0 {
                let time_limit = self.time_limit;
                self.solver().message(format_args!(
                    "setting time limit to {} seconds real time (due to '-t {}')",
                    time_limit,
                    time_limit_specified.unwrap_or("")
                ));
                Signal::alarm(time_limit);
                let terminator = AppTerminator { timesup: self.timesup.clone() };
                self.solver().connect_terminator(Box::new(terminator));
            }
            if conflict_limit >= 0 {
                self.solver().message(format_args!(
                    "setting conflict limit to {} conflicts (due to '{}')",
                    conflict_limit,
                    conflict_limit_specified.unwrap_or("")
                ));
                let succeeded = self.solver().limit("conflicts", conflict_limit);
                debug_assert!(succeeded);
                let _ = succeeded;
            }
            if decision_limit >= 0 {
                self.solver().message(format_args!(
                    "setting decision limit to {} decisions (due to '{}')",
                    decision_limit,
                    decision_limit_specified.unwrap_or("")
                ));
                let succeeded = self.solver().limit("decisions", decision_limit);
                debug_assert!(succeeded);
                let _ = succeeded;
            }
        }
        if self.verbose() || proof_specified {
            self.solver().section("proof tracing");
        }
        if proof_specified {
            match proof_path {
                None => {
                    // SAFETY: 'isatty'.
                    let force_binary = unsafe { libc::isatty(1) } != 0 && self.get("binary") != 0;
                    if force_binary {
                        self.set_long_option("--no-binary");
                    }
                    let binary = self.get("binary") != 0;
                    self.solver().message(format_args!(
                        "writing {} proof trace to {}'<stdout>'{}",
                        if binary { "binary" } else { "non-binary" },
                        tout().green_code(),
                        tout().normal_code()
                    ));
                    if force_binary {
                        self.solver()
                            .message(format_args!("connected to terminal thus non-binary proof forced"));
                    }
                    self.solver().trace_proof_file(c_stdout(), "<stdout>");
                }
                Some(p) => {
                    if !self.solver().trace_proof(p) {
                        apperr!("can not open and write proof trace to '{}'", p);
                    } else {
                        let binary = self.get("binary") != 0;
                        self.solver().message(format_args!(
                            "writing {} proof trace to {}'{}'{}",
                            if binary { "binary" } else { "non-binary" },
                            tout().green_code(),
                            p,
                            tout().normal_code()
                        ));
                    }
                }
            }
        } else {
            self.solver().verbose(1, format_args!("will not generate nor write DRAT proof"));
        }
        self.solver().section("parsing input");
        let dimacs_name = dimacs_path.unwrap_or("<stdin>");
        let mut help = String::new();
        if dimacs_path.is_none() {
            help += " ";
            help += tout().magenta_code();
            help += "(use '-h' for a list of common options)";
            help += tout().normal_code();
        }
        self.solver().message(format_args!(
            "reading DIMACS file from {}'{}'{}{}",
            tout().green_code(),
            dimacs_name,
            tout().normal_code(),
            help
        ));
        let mut incremental = false;
        let mut cube_literals: Vec<i32> = Vec::new();
        let mut max_var = self.max_var;
        let strict = self.force_strict_parsing;
        let err = if let Some(d) = dimacs_path {
            self.solver().read_dimacs_inccnf(d, &mut max_var, strict, &mut incremental, &mut cube_literals)
        } else {
            Signal::reset();
            let err = self.solver().read_dimacs_file_inccnf(
                c_stdin(),
                dimacs_name,
                &mut max_var,
                strict,
                &mut incremental,
                &mut cube_literals,
            );
            Signal::set(self as *mut App as *mut dyn Handler);
            err
        };
        self.max_var = max_var;
        if let Some(e) = err {
            apperr!("{}", e);
        }
        if let Some(r) = read_solution_path {
            self.solver().section("parsing solution");
            self.solver().message(format_args!("reading solution file from '{}'", r));
            if let Some(e) = self.solver().read_solution(r) {
                apperr!("{}", e);
            }
        }

        self.solver().section("options");
        if optimize > 0 {
            self.solver().optimize(optimize);
            self.solver().message_empty();
        }
        self.solver().options();

        let mut res: i32 = 0;

        if incremental {
            let reporting = self.get("report") > 1 || self.get("verbose") > 0;
            if !reporting {
                self.set("report", 0);
            }
            if !reporting {
                self.solver().section("incremental solving");
            }
            let mut cubes: usize = 0;
            let mut solved: usize = 0;
            let mut satisfiable: usize = 0;
            let mut unsatisfiable: usize = 0;
            let mut inconclusive: usize = 0;
            let quiet = self.get("quiet") != 0;
            // 'struct { double start, delta, sum; } time'.
            let mut time_start: f64 = 0.0;
            let mut time_delta: f64;
            let mut time_sum: f64 = 0.0;
            for &lit in &cube_literals {
                if lit == 0 {
                    cubes += 1;
                }
            }
            if !reporting {
                if cubes != 0 {
                    self.solver().message(format_args!("starting to solve {} cubes", cubes));
                    self.solver().message_empty();
                } else {
                    self.solver().message(format_args!("no cube to solve"));
                }
            }
            let mut cube: Vec<i32> = Vec::new();
            let mut failed: Vec<i32> = Vec::new();
            for &lit in &cube_literals {
                if lit != 0 {
                    cube.push(lit);
                } else {
                    cube.reverse();
                    for &other in &cube {
                        self.solver().assume(other);
                    }
                    let old = solved;
                    solved += 1;
                    if old != 0 {
                        if conflict_limit >= 0 {
                            let _ = self.solver().limit("conflicts", conflict_limit);
                        }
                        if decision_limit >= 0 {
                            let _ = self.solver().limit("decisions", decision_limit);
                        }
                    }
                    if !quiet {
                        if reporting {
                            let buffer = truncate255(format!(
                                "solving cube {} / {} {}%",
                                solved,
                                cubes,
                                cfmt_f64("%.0f", percent(solved as f64, cubes as f64))
                            ));
                            self.solver().section(&buffer);
                        }
                        time_start = absolute_process_time();
                    }
                    res = self.solver().solve();
                    if !quiet {
                        time_delta = absolute_process_time() - time_start;
                        time_sum += time_delta;
                        let buffer = truncate255(format!(
                            "{}in {} sec ({}% after {} sec at {} ms/cube){}",
                            tout().magenta_code(),
                            cfmt_f64("%.3f", time_delta),
                            cfmt_f64("%.0f", percent(solved as f64, cubes as f64)),
                            cfmt_f64("%.2f", time_sum),
                            cfmt_f64("%.0f", relative(1e3 * time_sum, solved as f64)),
                            tout().normal_code()
                        ));
                        if reporting {
                            self.solver().message_empty();
                        }
                        let (cube_str, status_str, color_code) = if res == 10 {
                            ("CUBE", "SATISFIABLE", tout().green_code())
                        } else if res == 20 {
                            ("CUBE", "UNSATISFIABLE", tout().cyan_code())
                        } else {
                            ("cube", "inconclusive", tout().magenta_code())
                        };
                        if reporting {
                            self.solver().message(format_args!(
                                "{}{} {} {}{} {}",
                                color_code,
                                cube_str,
                                solved,
                                status_str,
                                tout().normal_code(),
                                buffer
                            ));
                        } else {
                            self.solver().message(format_args!(
                                "{}{} {} {:<13}{} {}",
                                color_code,
                                cube_str,
                                solved,
                                status_str,
                                tout().normal_code(),
                                buffer
                            ));
                        }
                    }
                    if res == 10 {
                        satisfiable += 1;
                        self.solver().conclude();
                        break;
                    } else if res == 20 {
                        unsatisfiable += 1;
                        self.solver().conclude();
                        for &other in &cube {
                            if self.solver().failed(other) {
                                failed.push(other);
                            }
                        }
                        for &other in &failed {
                            self.solver().add(-other);
                        }
                        self.solver().add(0);
                        failed.clear();
                    } else {
                        debug_assert!(res == 0);
                        inconclusive += 1;
                        if self.timesup.load(Relaxed) {
                            break;
                        }
                    }
                    cube.clear();
                }
            }
            self.solver().section("incremental summary");
            self.solver().message(format_args!(
                "{} cubes solved {}%",
                solved,
                cfmt_f64("%.0f", percent(solved as f64, cubes as f64))
            ));
            self.solver().message(format_args!(
                "{} cubes inconclusive {}%",
                inconclusive,
                cfmt_f64("%.0f", percent(inconclusive as f64, solved as f64))
            ));
            self.solver().message(format_args!(
                "{} cubes unsatisfiable {}%",
                unsatisfiable,
                cfmt_f64("%.0f", percent(unsatisfiable as f64, solved as f64))
            ));
            self.solver().message(format_args!(
                "{} cubes satisfiable {}%",
                satisfiable,
                cfmt_f64("%.0f", percent(satisfiable as f64, solved as f64))
            ));

            if inconclusive != 0 && res == 20 {
                res = 0;
            }
        } else {
            self.solver().section("solving");
            res = self.solver().solve();
        }

        if proof_specified {
            self.solver().section("closing proof");
            let print = self.get("quiet") == 0;
            self.solver().close_proof_trace(print);
        }

        if let Some(o) = output_path {
            self.solver().section("writing output");
            self.solver().message(format_args!(
                "writing simplified CNF to DIMACS file {}'{}'{}",
                tout().green_code(),
                o,
                tout().normal_code()
            ));
            let max_var = self.max_var;
            if let Some(e) = self.solver().write_dimacs(o, max_var) {
                apperr!("{}", e);
            }
        }

        if let Some(e) = extension_path {
            self.solver().section("writing extension");
            self.solver().message(format_args!(
                "writing extension stack to {}'{}'{}",
                tout().green_code(),
                e,
                tout().normal_code()
            ));
            if let Some(err) = self.solver().write_extension(e) {
                apperr!("{}", err);
            }
        }

        self.solver().section("result");

        let mut write_result_file: *mut libc::FILE = c_stdout();
        if let Some(w) = write_result_path {
            let c = std::ffi::CString::new(w).unwrap_or_default();
            // SAFETY: valid C strings.
            write_result_file = unsafe { libc::fopen(c.as_ptr(), b"w\0".as_ptr() as *const libc::c_char) };
            if write_result_file.is_null() {
                apperr!("could not write solution to '{}'", w);
            }
            self.solver().message(format_args!("writing result to '{}'", w));
        }

        if res == 10 {
            if status {
                fputs("s SATISFIABLE\n", write_result_file);
            }
            if witness {
                self.print_witness(write_result_file);
            }
        } else if res == 20 && status {
            fputs("s UNSATISFIABLE\n", write_result_file);
        } else if status {
            fputs("c UNKNOWN\n", write_result_file);
        }
        fflush(write_result_file);
        if write_result_path.is_some() {
            // SAFETY: stream opened above.
            unsafe {
                libc::fclose(write_result_file);
            }
        }
        self.solver().statistics();
        self.solver().resources();
        self.solver().section("shutting down");
        self.solver().message(format_args!("exit {}", res));
        if res == 0 && self.timesup.load(Relaxed) && self.solver().get("quiet") == 0 {
            fputs(
                "c Timeout reached! 😅 This instance is a real thinker.\n\
                 c 🚧 🚧 🚧 Please consider contributing it to the page\n\
                 c https://mysolvertimesout.org/#sat in order to improve\n\
                 c automated reasoning. 🚧 🚧 🚧\n",
                write_result_file,
            );
        }
        if !less_pipe.is_null() {
            // SAFETY: plain POSIX calls.
            unsafe {
                libc::close(1);
                libc::pclose(less_pipe);
            }
        }
        if self.time_limit > 0 {
            // SAFETY: 'alarm'.
            unsafe {
                libc::alarm(0);
            }
        }

        let signal_value = self.signal_value.load(Relaxed);
        if signal_value != 0 {
            Signal::reset();
            self.signal_message("raising", signal_value);
            // SAFETY: 'raise'.
            unsafe {
                libc::raise(signal_value);
            }
        }

        res
    }
}

/// `snprintf (buffer, sizeof buffer, ...)` with `char buffer[256]`.
fn truncate255(mut s: String) -> String {
    if s.len() > 255 {
        let mut n = 255;
        while !s.is_char_boundary(n) {
            n -= 1;
        }
        s.truncate(n);
    }
    s
}

/*------------------------------------------------------------------------*/

impl Handler for App {
    fn catch_signal(&mut self, sig: i32) {
        self.signal_value.store(sig, Relaxed);
        if let Some(t) = &self.termination_forced {
            t.store(true, Relaxed);
        }
        Signal::reset(); // Send signal again -> instant termination but no stats
    }

    fn catch_alarm(&mut self) {
        // Both approaches work (the C++ code keeps the alternative
        // 'solver->terminate ()' for illustration purposes).
        if let Some(t) = &self.termination_forced {
            t.store(true, Relaxed);
        }
        // timesup = true; // Wait for solver to call 'App::terminate ()'.
    }
}

impl Drop for App {
    fn drop(&mut self) {
        if self.solver.is_none() {
            return; // Only partially initialized.
        }
        Signal::reset();
        self.solver = None;
    }
}

/*------------------------------------------------------------------------*/

// The actual app is allocated on the stack and then its 'main' function is
// called.  This looks like that there are no static variables, which is not
// completely true, since both the signal handler connected to the app as
// well as the terminal have statically allocated components as well as the
// options table 'Options::table'.  All are shared among solvers.

/// `int main (int argc, char **argv)` of 'cadical.cpp'.
pub fn main() {
    let args: Vec<String> = std::env::args_os().map(|a| a.to_string_lossy().into_owned()).collect();
    let res = {
        let mut app = App::new();
        app.main(&args)
    };
    std::process::exit(res);
}
