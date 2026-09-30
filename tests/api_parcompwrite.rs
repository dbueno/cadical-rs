//! Port of `cadical/test/api/parcompwrite.cpp`: writes and reads back
//! (compressed) files in parallel from 100 threads, both with C `stdio`
//! and with the (internal) CaDiCaL `File` class.
//!
//! Files are written to the test output directory (see
//! `common::build_dir`) instead of `/tmp`.  Threads use `std::thread`
//! instead of `pthread` directly.

mod common;

use cadical::file::File;
use cadical::internal::Internal;
use std::ffi::CString;
use std::sync::Mutex;

static SUFFIX: Mutex<&'static str> = Mutex::new(".gz");

fn prefix(tester: &str) -> String {
    format!("{}/cadical-api-test-parcompwrite-{}-{}", common::build_dir(), tester, common::pid())
}

fn path(tester: &str, i: u32) -> String {
    format!("{}-{}{}", prefix(tester), i, *SUFFIX.lock().unwrap())
}

static SERIALIZE_MUTEX: Mutex<()> = Mutex::new(());

fn perror(msg: &str) {
    let c = CString::new(msg).unwrap();
    // SAFETY: valid C string.
    unsafe { libc::perror(c.as_ptr()) };
}

fn eprint_c(msg: &str) {
    cadical::cfprintf!(cadical::message::c_stderr(), "{}", msg);
}

fn exit(code: i32) -> ! {
    // SAFETY: 'exit' as in C++ (flushes C streams).
    unsafe { libc::exit(code) }
}

trait Tester {
    fn base(&mut self) -> &mut TesterBase;
    fn name(&self) -> &'static str;
    fn writing(&mut self);
    fn reading(&mut self);
    fn write(&mut self);
    fn read(&mut self, j: &mut u32) -> bool;
    fn close(&mut self);

    fn path(&mut self) -> String {
        let name = self.name();
        let base = self.base();
        if base.spath.is_none() {
            base.spath = Some(path(name, base.i));
        }
        base.spath.clone().unwrap()
    }

    fn message(&mut self, what: &str) {
        let path = self.path();
        let _guard = SERIALIZE_MUTEX.lock().unwrap();
        cadical::cprintf!("{:<17} {}\n", what, path);
        common::flush();
    }

    fn run(&mut self) {
        self.message("opening-to-write");
        self.writing();
        self.message("writing");
        self.write();
        self.message("closing");
        self.close();
        self.message("reading");
        self.reading();
        let mut j = 0;
        let i = self.base().i;
        if self.read(&mut j) && i == j {
            self.message("checked");
        } else {
            let path = self.path();
            let _guard = SERIALIZE_MUTEX.lock().unwrap();
            eprint_c(&format!("error: writing and reading back '{}' from '{}' failed\n", i, path));
            cadical::message::fflush(cadical::message::c_stderr());
            exit(1);
        }
        self.message("closing");
        self.close();
        self.unlink();
    }

    fn unlink(&mut self) {
        self.message("deleting");
        let p = CString::new(self.path()).unwrap();
        // SAFETY: valid C string.
        if unsafe { libc::unlink(p.as_ptr()) } != 0 {
            perror("error: unlink failed");
        }
    }
}

struct TesterBase {
    spath: Option<String>,
    i: u32,
}

struct StdioTester {
    base: TesterBase,
    file: *mut libc::FILE,
}

impl StdioTester {
    fn new(j: u32) -> StdioTester {
        StdioTester { base: TesterBase { spath: None, i: j }, file: std::ptr::null_mut() }
    }
    fn open(&mut self, mode: &[u8]) {
        let p = CString::new(self.path()).unwrap();
        // SAFETY: valid C strings.
        self.file = unsafe { libc::fopen(p.as_ptr(), mode.as_ptr() as *const libc::c_char) };
    }
}

impl Tester for StdioTester {
    fn base(&mut self) -> &mut TesterBase {
        &mut self.base
    }
    fn name(&self) -> &'static str {
        "stdio"
    }
    fn writing(&mut self) {
        self.open(b"w\0");
        if self.file.is_null() {
            perror("error: fopen to write failed");
            exit(1);
        }
    }
    fn reading(&mut self) {
        self.open(b"r\0");
        if self.file.is_null() {
            perror("error: fopen to read failed");
            exit(1);
        }
    }
    fn write(&mut self) {
        assert!(!self.file.is_null());
        let s = CString::new(format!("{}\n", self.base.i)).unwrap();
        // SAFETY: valid stream and C string.
        if unsafe { libc::fputs(s.as_ptr(), self.file) } < 0 {
            eprint_c("error: fprintf failed\n");
        }
    }
    fn read(&mut self, j: &mut u32) -> bool {
        assert!(!self.file.is_null());
        let mut tmp: libc::c_uint = 0;
        // SAFETY: valid stream, format and out pointer.
        if unsafe { libc::fscanf(self.file, b"%u\0".as_ptr() as *const libc::c_char, &mut tmp) } <= 0 {
            eprint_c("error: fscanf failed\n");
            return false;
        }
        *j = tmp;
        true
    }
    fn close(&mut self) {
        // SAFETY: opened with 'fopen'.
        if unsafe { libc::fclose(self.file) } != 0 {
            perror("error: fclose written failed");
        }
    }
}

struct CadicalFileTester {
    base: TesterBase,
    file: Option<Box<File>>,
    internal: Box<Internal>,
}

impl CadicalFileTester {
    fn new(j: u32) -> CadicalFileTester {
        let mut internal = Internal::new();
        internal.opts.verbose = 0;
        internal.opts.quiet = 1;
        CadicalFileTester { base: TesterBase { spath: None, i: j }, file: None, internal }
    }
    fn internal_ptr(&mut self) -> *mut Internal {
        &mut *self.internal
    }
}

impl Drop for CadicalFileTester {
    fn drop(&mut self) {
        // C++: 'delete internal; if (file) delete file;'
        self.file = None;
    }
}

impl Tester for CadicalFileTester {
    fn base(&mut self) -> &mut TesterBase {
        &mut self.base
    }
    fn name(&self) -> &'static str {
        "cadical-file"
    }
    fn writing(&mut self) {
        let path = self.path();
        let f = File::write(self.internal_ptr(), &path);
        if f.is_null() {
            eprint_c("error: 'File::write' failed\n");
            exit(1);
        }
        // SAFETY: 'File::write' returns a 'Box::into_raw' pointer.
        self.file = Some(unsafe { Box::from_raw(f) });
    }
    fn reading(&mut self) {
        let path = self.path();
        let f = File::read(self.internal_ptr(), &path);
        if f.is_null() {
            eprint_c("error: File::read failed\n");
            exit(1);
        }
        // SAFETY: 'File::read' returns a 'Box::into_raw' pointer.
        self.file = Some(unsafe { Box::from_raw(f) });
    }
    fn write(&mut self) {
        let i = self.base.i;
        let file = self.file.as_mut().expect("file");
        if !file.put_u64(i as u64) || !file.endl() {
            eprint_c("error: File::put failed\n");
        }
    }
    fn read(&mut self, j: &mut u32) -> bool {
        let file = self.file.as_mut().expect("file");
        let is_digit = |ch: i32| (b'0' as i32..=b'9' as i32).contains(&ch);
        let invalid = || {
            eprint_c("error: invalid number in 'cadical_file_tester::read'\n");
            false
        };
        let mut ch = file.get();
        if !is_digit(ch) {
            return invalid();
        }
        let mut tmp: u32 = (ch - b'0' as i32) as u32;
        loop {
            ch = file.get();
            if !is_digit(ch) {
                break;
            }
            if u32::MAX / 10 < tmp {
                return invalid();
            }
            tmp *= 10;
            let digit = (ch - b'0' as i32) as u32;
            if u32::MAX - digit < tmp {
                return invalid();
            }
            tmp += digit;
        }
        if ch != b'\n' as i32 {
            eprint_c("error: expected new-line after number");
            return false;
        }
        if file.get() != libc::EOF {
            eprint_c("error: expected end-of-file after line with number");
            return false;
        }
        *j = tmp;
        true
    }
    fn close(&mut self) {
        let mut file = self.file.take().expect("file");
        file.close(false);
        drop(file);
    }
}

/// A tester moved to its own thread (C++ passes 'this' to
/// 'pthread_create').
struct SendTester(Box<dyn Tester>);
// SAFETY: each tester (including its private 'Internal') is only used by
// the one thread running it, then handed back through 'join'.
unsafe impl Send for SendTester {}

extern "C" fn catch_alarm(sig: libc::c_int) {
    assert!(sig == libc::SIGALRM);
    let msg = b"error: unexpected alarm (file I/O hanging?)\n";
    // SAFETY: async-signal-safe 'write' and '_exit'-like 'exit' as in C++.
    unsafe {
        if libc::write(2, msg.as_ptr() as *const libc::c_void, msg.len()) != 0 {
            libc::exit(2);
        }
        libc::exit(1);
    }
}

fn main() {
    // Like 'test/api/run.sh' skip this test on Darwin (there the one second
    // alarm is regularly hit on a loaded machine, by the C++ test too),
    // unless 'CADICAL_APITEST_PARCOMPWRITE' is set.
    if cfg!(target_os = "macos") && std::env::var_os("CADICAL_APITEST_PARCOMPWRITE").is_none() {
        eprintln!("skipping API test 'parcompwrite' on 'Darwin' (set CADICAL_APITEST_PARCOMPWRITE=1 to run it)");
        return;
    }
    let suffixes = ["", ".gz"];
    // SAFETY: installing a signal handler and arming the alarm.
    unsafe {
        libc::signal(libc::SIGALRM, catch_alarm as extern "C" fn(libc::c_int) as libc::sighandler_t);
        libc::alarm(1);
    }
    for s in suffixes {
        *SUFFIX.lock().unwrap() = s;
        for c in 0..2u32 {
            if c == 0 && !s.is_empty() {
                continue;
            }
            let mut testers: Vec<SendTester> = Vec::new();
            for i in 0..100u32 {
                let t: Box<dyn Tester> =
                    if c != 0 { Box::new(CadicalFileTester::new(i)) } else { Box::new(StdioTester::new(i)) };
                testers.push(SendTester(t));
            }
            let handles: Vec<_> = testers
                .into_iter()
                .map(|t| {
                    std::thread::spawn(move || {
                        let mut t = t;
                        t.0.run();
                        t
                    })
                })
                .collect();
            for h in handles {
                let t = h.join().expect("error: 'pthread_join' failed");
                drop(t);
            }
        }
    }
}
