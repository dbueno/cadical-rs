//! Port of `file.hpp` and `file.cpp`: wraps a C `FILE` with name and
//! supports zipped reading and writing through 'popen' using external
//! helper tools.  Reading has line numbers.

use crate::internal::Internal;

extern "C" {
    fn getc_unlocked(stream: *mut libc::FILE) -> libc::c_int;
    fn putc_unlocked(c: libc::c_int, stream: *mut libc::FILE) -> libc::c_int;
}

pub struct File {
    pub internal: *mut Internal,
    pub writing: bool,
    /// Need to close file (1=fclose, 2=pclose, 3=pipe).
    pub close_file: i32,
    pub child_pid: i32,
    pub file: *mut libc::FILE,
    pub _name: String,
    pub _lineno: u64,
    pub _bytes: u64,
}

impl File {
    /// Using the 'unlocked' versions here is way faster but not thread
    /// safe if the same file is used by different threads.
    #[inline]
    pub fn get(&mut self) -> i32 {
        debug_assert!(!self.writing);
        // SAFETY: 'file' is an open stream.
        let res = unsafe { getc_unlocked(self.file) };
        if res == b'\n' as i32 {
            self._lineno += 1;
        }
        if res != libc::EOF {
            self._bytes += 1;
        }
        res
    }

    /// C++ overloads `put (char)` and `put (unsigned char)`.
    #[inline]
    pub fn put_char(&mut self, ch: u8) -> bool {
        debug_assert!(self.writing);
        // SAFETY: 'file' is an open stream.
        if unsafe { putc_unlocked(ch as libc::c_int, self.file) } == libc::EOF {
            return false;
        }
        self._bytes += 1;
        true
    }

    #[inline]
    pub fn endl(&mut self) -> bool {
        self.put_char(b'\n')
    }

    /// C++ overload `put (const char *)`.
    #[inline]
    pub fn put_str(&mut self, s: &str) -> bool {
        for &b in s.as_bytes() {
            if b == 0 {
                break;
            }
            if !self.put_char(b) {
                return false;
            }
        }
        true
    }

    /// C++ overload `put (int lit)`.
    pub fn put_int(&mut self, lit: i32) -> bool {
        debug_assert!(self.writing);
        if lit == 0 {
            self.put_char(b'0')
        } else if lit == i32::MIN {
            self.put_str("-2147483648")
        } else {
            let mut buffer = [0u8; 11];
            let mut i = buffer.len();
            let mut idx = lit.unsigned_abs();
            while idx != 0 {
                debug_assert!(i > 0);
                i -= 1;
                buffer[i] = b'0' + (idx % 10) as u8;
                idx /= 10;
            }
            if lit < 0 && !self.put_char(b'-') {
                return false;
            }
            for &b in &buffer[i..] {
                if !self.put_char(b) {
                    return false;
                }
            }
            true
        }
    }

    /// C++ overload `put (int64_t l)`.
    pub fn put_i64(&mut self, l: i64) -> bool {
        debug_assert!(self.writing);
        if l == 0 {
            self.put_char(b'0')
        } else if l == i64::MIN {
            self.put_str("-9223372036854775808")
        } else {
            let mut buffer = [0u8; 21];
            let mut i = buffer.len();
            let mut k = l.unsigned_abs();
            while k != 0 {
                debug_assert!(i > 0);
                i -= 1;
                buffer[i] = b'0' + (k % 10) as u8;
                k /= 10;
            }
            if l < 0 && !self.put_char(b'-') {
                return false;
            }
            for &b in &buffer[i..] {
                if !self.put_char(b) {
                    return false;
                }
            }
            true
        }
    }

    /// C++ overload `put (uint64_t l)`.
    pub fn put_u64(&mut self, mut l: u64) -> bool {
        debug_assert!(self.writing);
        if l == 0 {
            self.put_char(b'0')
        } else {
            let mut buffer = [0u8; 22];
            let mut i = buffer.len();
            while l != 0 {
                debug_assert!(i > 0);
                i -= 1;
                buffer[i] = b'0' + (l % 10) as u8;
                l /= 10;
            }
            for &b in &buffer[i..] {
                if !self.put_char(b) {
                    return false;
                }
            }
            true
        }
    }

    #[inline]
    pub fn name(&self) -> &str {
        &self._name
    }
    #[inline]
    pub fn lineno(&self) -> u64 {
        self._lineno
    }
    #[inline]
    pub fn bytes(&self) -> u64 {
        self._bytes
    }
    #[inline]
    pub fn connect_internal(&mut self, i: *mut Internal) {
        self.internal = i;
    }
    #[inline]
    pub fn closed(&self) -> bool {
        self.file.is_null()
    }
}

/*------------------------------------------------------------------------*/
// Port of the functions defined in 'file.cpp'.

#[allow(unused_imports)]
use crate::prelude::*;
use crate::format::cfmt_f64;
use std::ffi::CString;

/// Convert a path (or other string) to a C string (paths never contain
/// zero bytes when they come from the command line or API).
fn cstr(s: &str) -> CString {
    match CString::new(s) {
        Ok(c) => c,
        Err(e) => {
            let pos = e.nul_position();
            CString::new(&s.as_bytes()[..pos]).unwrap()
        }
    }
}

#[inline]
fn errno() -> i32 {
    std::io::Error::last_os_error().raw_os_error().unwrap_or(0)
}

#[inline]
fn s_isdir(mode: libc::mode_t) -> bool {
    (mode & libc::S_IFMT) == libc::S_IFDIR
}

#[inline]
fn s_isfifo(mode: libc::mode_t) -> bool {
    (mode & libc::S_IFMT) == libc::S_IFIFO
}

fn stat_path(path: &str, buf: &mut libc::stat) -> i32 {
    let c = cstr(path);
    // SAFETY: valid C string and 'stat' buffer.
    unsafe { libc::stat(c.as_ptr(), buf) }
}

fn access_path(path: &str, mode: i32) -> i32 {
    let c = cstr(path);
    // SAFETY: valid C string.
    unsafe { libc::access(c.as_ptr(), mode) }
}

fn new_stat() -> libc::stat {
    // SAFETY: 'struct stat' is plain old data.
    unsafe { std::mem::zeroed() }
}

// These are signatures for supported compressed file types.  In 2018 the
// SAT Competition was running on StarExec and used internally 'bzip2'
// compressed files, but gave them uncompressed to the solver using exactly
// the same path (with '.bz2' suffix).  Then 'CaDiCaL' tried to read that
// actually uncompressed file through 'bzip2', which of course failed.  Now
// we double check and fall back to reading the file as is, if the signature
// does not match after issuing a warning.
//
// (The C++ arrays are terminated by 'EOF', here we use slices.)

static XZSIG: [i32; 7] = [0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00];
static BZ2SIG: [i32; 3] = [0x42, 0x5A, 0x68];
static GZSIG: [i32; 2] = [0x1F, 0x8B];
static SIG7Z: [i32; 6] = [0x37, 0x7A, 0xBC, 0xAF, 0x27, 0x1C];
static LZMASIG: [i32; 1] = [0x5D];

#[cfg(target_os = "macos")]
static mut COMPRESSED_FILE_WRITING_MUTEX: libc::pthread_mutex_t = libc::PTHREAD_MUTEX_INITIALIZER;

#[cfg(target_os = "macos")]
fn compressed_file_writing_mutex_lock() {
    // SAFETY: statically initialized mutex.
    unsafe {
        libc::pthread_mutex_lock(std::ptr::addr_of_mut!(COMPRESSED_FILE_WRITING_MUTEX));
    }
}

#[cfg(target_os = "macos")]
fn compressed_file_writing_mutex_unlock() {
    // SAFETY: statically initialized mutex locked by this thread.
    unsafe {
        libc::pthread_mutex_unlock(std::ptr::addr_of_mut!(COMPRESSED_FILE_WRITING_MUTEX));
    }
}

impl File {
    pub fn exists(path: &str) -> bool {
        let mut buf = new_stat();
        if stat_path(path, &mut buf) != 0 {
            return false;
        }
        if access_path(path, libc::R_OK) != 0 {
            return false;
        }
        true
    }

    pub fn writable(path: &str) -> bool {
        let res: i32;
        if path == "/dev/null" {
            res = 0;
        } else if path.is_empty() {
            res = 2;
        } else {
            let mut buf = new_stat();
            match path.rfind('/') {
                None => {
                    if stat_path(path, &mut buf) != 0 {
                        res = if errno() == libc::ENOENT { 0 } else { -2 };
                    } else if s_isdir(buf.st_mode) {
                        res = 3;
                    } else {
                        res = if access_path(path, libc::W_OK) != 0 { 4 } else { 0 };
                    }
                }
                Some(p) if p + 1 == path.len() => res = 5,
                Some(p) => {
                    let dirname = &path[..p];
                    if stat_path(dirname, &mut buf) != 0 {
                        res = 6;
                    } else if !s_isdir(buf.st_mode) {
                        res = 7;
                    } else if access_path(dirname, libc::W_OK) != 0 {
                        res = 8;
                    } else if stat_path(path, &mut buf) != 0 {
                        res = if errno() == libc::ENOENT { 0 } else { -3 };
                    } else {
                        res = if access_path(path, libc::W_OK) != 0 { 9 } else { 0 };
                    }
                }
            }
        }
        res == 0
    }

    pub fn piping(&mut self) -> bool {
        let mut st = new_stat();
        // SAFETY: 'file' is an open stream.
        let fd = unsafe { libc::fileno(self.file) };
        // SAFETY: valid descriptor and buffer.
        if unsafe { libc::fstat(fd, &mut st) } != 0 {
            return true;
        }
        s_isfifo(st.st_mode)
    }

    /// C++ overload `File::match` (renamed).
    pub fn matches(internal: *mut Internal, path: &str, sig: &[i32]) -> bool {
        let c = cstr(path);
        // SAFETY: valid C strings.
        let tmp = unsafe { libc::fopen(c.as_ptr(), b"r\0".as_ptr() as *const libc::c_char) };
        if tmp.is_null() {
            warning!(internal, "failed to open '{}' to check signature", path);
            return false;
        }
        let mut res = true;
        for &p in sig {
            if !res {
                break;
            }
            // SAFETY: 'tmp' is an open stream.
            res = unsafe { getc_unlocked(tmp) } == p;
        }
        // SAFETY: 'tmp' is an open stream.
        unsafe {
            libc::fclose(tmp);
        }
        if !res {
            warning!(internal, "file type signature check for '{}' failed", path);
        }
        res
    }

    pub fn size(path: &str) -> usize {
        let mut buf = new_stat();
        if stat_path(path, &mut buf) != 0 {
            return 0;
        }
        buf.st_size as usize
    }

    /// Search in 'PATH'.  Check that 'prg' is in the 'PATH' and thus can
    /// be found if executed through 'popen' or 'exec'.
    pub fn find_program(prg: &str) -> Option<String> {
        let c = std::env::var_os("PATH")?;
        let e = c.to_string_lossy().into_owned();
        let bytes = e.as_bytes();
        let len = bytes.len();
        let mut p = 0usize;
        while p < len {
            let mut q = p;
            while q < len && bytes[q] != b':' {
                q += 1;
            }
            let path = format!("{}/{}", &e[p..q], prg);
            if File::exists(&path) {
                return Some(path);
            }
            p = q + 1;
        }
        None
    }

    pub fn open_file(internal: *mut Internal, path: &str, mode: &str) -> *mut libc::FILE {
        let _ = internal;
        let c = cstr(path);
        let m = cstr(mode);
        // SAFETY: valid C strings.
        unsafe { libc::fopen(c.as_ptr(), m.as_ptr()) }
    }

    pub fn read_file(internal: *mut Internal, path: &str) -> *mut libc::FILE {
        msg!(internal, "opening file to read '{}'", path);
        File::open_file(internal, path, "r")
    }

    pub fn write_file(internal: *mut Internal, path: &str) -> *mut libc::FILE {
        msg!(internal, "opening file to write '{}'", path);
        File::open_file(internal, path, "wb")
    }

    pub fn split_str(command: &str, argv: &mut Vec<String>) {
        let c = command.as_bytes();
        let mut i = 0;
        while i < c.len() && c[i] == b' ' {
            i += 1;
        }
        while i < c.len() {
            let mut p = i;
            while p < c.len() && c[p] != b' ' {
                p += 1;
            }
            argv.push(command[i..p].to_string());
            while p < c.len() && c[p] == b' ' {
                p += 1;
            }
            i = p;
        }
    }

    pub fn delete_str_vector(argv: &mut Vec<String>) {
        argv.clear();
    }

    pub fn open_pipe(internal: *mut Internal, fmt: &str, path: &str, mode: &str) -> *mut libc::FILE {
        let prglen = fmt.find(' ').unwrap_or(fmt.len());
        let prg = &fmt[..prglen];
        let found = File::find_program(prg);
        if let Some(f) = &found {
            msg!(internal, "found '{}' in path for '{}'", f, prg);
        }
        if found.is_none() {
            msg!(internal, "did not find '{}' in path", prg);
        }
        if found.is_none() {
            return std::ptr::null_mut();
        }
        // 'snprintf (cmd, cmd_size, fmt, path)' with a single '%s' in 'fmt'.
        let cmd = fmt.replacen("%s", path, 1);
        let c = cstr(&cmd);
        let m = cstr(mode);
        // SAFETY: valid C strings.
        unsafe { libc::popen(c.as_ptr(), m.as_ptr()) }
    }

    pub fn read_pipe(internal: *mut Internal, fmt: &str, sig: &[i32], path: &str) -> *mut libc::FILE {
        if !File::exists(path) {
            log!(internal, "file '{}' does not exist", path);
            return std::ptr::null_mut();
        }
        log!(internal, "file '{}' exists", path);
        if !sig.is_empty() && !File::matches(internal, path, sig) {
            return std::ptr::null_mut();
        }
        log!(internal, "file '{}' matches signature for '{}'", path, fmt);
        msg!(internal, "opening pipe to read '{}'", path);
        File::open_pipe(internal, fmt, path, "r")
    }

    pub fn write_pipe(internal: *mut Internal, command: &str, path: &str, child_pid: &mut i32) -> *mut libc::FILE {
        debug_assert!(!command.is_empty() && !command.starts_with(' '));
        msg!(internal, "writing through command '{}' to '{}'", command, path);
        let mut args: Vec<String> = Vec::new();
        File::split_str(command, &mut args);
        debug_assert!(!args.is_empty());
        let absolute_command_path = File::find_program(&args[0]);
        // Prepare everything needed in the child before forking.
        let c_args: Vec<CString> = args.iter().map(|a| cstr(a)).collect();
        let mut argv: Vec<*const libc::c_char> = c_args.iter().map(|a| a.as_ptr()).collect();
        argv.push(std::ptr::null());
        let c_abs = absolute_command_path.as_deref().map(cstr);
        let c_path = cstr(path);
        let mut pipe_fds: [libc::c_int; 2] = [0; 2];
        let out: libc::c_int;
        let mut res: *mut libc::FILE = std::ptr::null_mut();
        #[cfg(target_os = "macos")]
        compressed_file_writing_mutex_lock();
        // SAFETY (whole block): plain POSIX calls on valid arguments, the
        // child only uses async-signal-safe functions before 'execv'.
        unsafe {
            if absolute_command_path.is_none() {
                msg!(internal, "could not find '{}' in 'PATH' environment variable", args[0]);
            } else if libc::pipe(pipe_fds.as_mut_ptr()) < 0 {
                msg!(internal, "could not generate pipe to '{}' command", command);
            } else if {
                out = libc::open(c_path.as_ptr(), libc::O_CREAT | libc::O_TRUNC | libc::O_WRONLY, 0o644 as libc::c_uint);
                out < 0
            } {
                msg!(internal, "could not open '{}' for writing", path);
            } else if {
                *child_pid = libc::fork();
                *child_pid < 0
            } {
                msg!(internal, "could not fork process to execute '{}' command", command);
                libc::close(out);
            } else if *child_pid != 0 {
                libc::close(pipe_fds[0]);
                res = libc::fdopen(pipe_fds[1], b"wb\0".as_ptr() as *const libc::c_char);
            } else {
                // Connect stdin and stdout in child

                libc::dup2(pipe_fds[0], 0);
                libc::dup2(out, 1);

                // Surpress '7z' verbose output on 'stderr'.

                if command.as_bytes()[0] == b'7' {
                    libc::close(2);
                }

                // Before the fork another thread could have created more
                // fds.  These fds are cloned into the child process.  As
                // this inhibits pipes to be closed by the parent process we
                // have to close all of the erroneously cloned fds here
                // (simplistic replacement for 'closefrom (3)', as used by
                // the reference build configured with '-DNCLOSEFROM').

                let mut fd = 3;
                while fd != libc::FD_SETSIZE as libc::c_int {
                    libc::close(fd);
                    fd += 1;
                }
                libc::execv(c_abs.as_ref().unwrap().as_ptr(), argv.as_ptr());
                libc::_exit(1);
            }
        }
        #[cfg(target_os = "macos")]
        if res.is_null() {
            compressed_file_writing_mutex_unlock();
        }
        res
    }

    /// C++ overload `File::read` (renamed).
    pub fn read_fp(internal: *mut Internal, f: *mut libc::FILE, n: &str) -> *mut File {
        Box::into_raw(Box::new(File::new(internal, false, 0, 0, f, n)))
    }

    /// C++ overload `File::write` (renamed).
    pub fn write_fp(internal: *mut Internal, f: *mut libc::FILE, n: &str) -> *mut File {
        Box::into_raw(Box::new(File::new(internal, true, 0, 0, f, n)))
    }

    pub fn read(internal: *mut Internal, path: &str) -> *mut File {
        let mut file: *mut libc::FILE = std::ptr::null_mut();
        let mut close_input = 2;
        let mut read_file = true;
        if has_suffix(path, ".xz") {
            file = File::read_pipe(internal, "xz -c -d %s", &XZSIG, path);
            read_file = file.is_null();
        } else if has_suffix(path, ".lzma") {
            file = File::read_pipe(internal, "lzma -c -d %s", &LZMASIG, path);
            read_file = file.is_null();
        } else if has_suffix(path, ".bz2") {
            file = File::read_pipe(internal, "bzip2 -c -d %s", &BZ2SIG, path);
            read_file = file.is_null();
        } else if has_suffix(path, ".gz") {
            file = File::read_pipe(internal, "gzip -c -d %s", &GZSIG, path);
            read_file = file.is_null();
        } else if has_suffix(path, ".7z") {
            file = File::read_pipe(internal, "7z x -so %s 2>/dev/null", &SIG7Z, path);
            read_file = file.is_null();
        }
        if read_file {
            // READ_FILE:
            file = File::read_file(internal, path);
            close_input = 1;
        }

        if file.is_null() {
            return std::ptr::null_mut();
        }

        Box::into_raw(Box::new(File::new(internal, false, close_input, 0, file, path)))
    }

    pub fn write(internal: *mut Internal, path: &str) -> *mut File {
        let file: *mut libc::FILE;
        let mut close_output = 3;
        let mut child_pid = 0;
        if has_suffix(path, ".xz") {
            file = File::write_pipe(internal, "xz -c", path, &mut child_pid);
        } else if has_suffix(path, ".bz2") {
            file = File::write_pipe(internal, "bzip2 -c", path, &mut child_pid);
        } else if has_suffix(path, ".gz") {
            file = File::write_pipe(internal, "gzip -c", path, &mut child_pid);
        } else if has_suffix(path, ".7z") {
            file = File::write_pipe(internal, "7z a -an -txz -si -so", path, &mut child_pid);
        } else {
            file = File::write_file(internal, path);
            close_output = 1;
        }

        if file.is_null() {
            return std::ptr::null_mut();
        }

        Box::into_raw(Box::new(File::new(internal, true, close_output, child_pid, file, path)))
    }

    /// `print` defaults to `false` in C++
    pub fn close(&mut self, mut print: bool) {
        debug_assert!(!self.file.is_null());
        let internal = self.internal;
        {
            // SAFETY: 'internal' is valid while the file is open.
            let opts = unsafe { &(*internal).opts };
            if opts.quiet != 0 {
                print = false;
            } else if opts.verbose > 0 {
                print = true;
            }
        }
        if self.close_file == 0 && print {
            msg!(internal, "disconnecting from '{}'", self.name());
        }
        if self.close_file == 1 {
            if print {
                msg!(internal, "closing file '{}'", self.name());
            }
            // SAFETY: open stream.
            unsafe {
                libc::fclose(self.file);
            }
        }
        if self.close_file == 2 {
            if print {
                msg!(internal, "closing input pipe to read '{}'", self.name());
            }
            // SAFETY: stream opened with 'popen'.
            unsafe {
                libc::pclose(self.file);
            }
        }
        if self.close_file == 3 {
            if print {
                msg!(internal, "closing output pipe to write '{}'", self.name());
            }
            // SAFETY: open stream and child process.
            unsafe {
                libc::fclose(self.file);
                libc::waitpid(self.child_pid, std::ptr::null_mut(), 0);
            }
            #[cfg(target_os = "macos")]
            compressed_file_writing_mutex_unlock();
        }
        self.file = std::ptr::null_mut(); // mark as closed

        // TODO what about error checking for 'fclose', 'pclose' or 'waitpid'?

        if print {
            if self.writing {
                let written_bytes: u64 = self.bytes();
                let written_mb = written_bytes as f64 / (1i32 << 20) as f64;
                msg!(
                    internal,
                    "after writing {} bytes {} MB",
                    written_bytes,
                    cfmt_f64("%.1f", written_mb)
                );
                if self.close_file == 3 {
                    let actual_bytes = File::size(self.name());
                    if actual_bytes != 0 {
                        let actual_mb = actual_bytes as f64 / (1i32 << 20) as f64;
                        msg!(
                            internal,
                            "deflated to {} bytes {} MB",
                            actual_bytes as isize,
                            cfmt_f64("%.1f", actual_mb)
                        );
                        msg!(
                            internal,
                            "factor {} ({}% compression)",
                            cfmt_f64("%.2f", relative(written_bytes as f64, actual_bytes as f64)),
                            cfmt_f64("%.2f", percent(actual_bytes as f64, written_bytes as f64))
                        );
                    } else {
                        msg!(internal, "but could not determine actual size of written file");
                    }
                }
            } else {
                let read_bytes: u64 = self.bytes();
                let read_mb = read_bytes as f64 / (1i32 << 20) as f64;
                msg!(internal, "after reading {} bytes {} MB", read_bytes, cfmt_f64("%.1f", read_mb));
                if self.close_file == 2 {
                    let actual_bytes = File::size(self.name());
                    let actual_mb = actual_bytes as f64 / (1i32 << 20) as f64;
                    msg!(
                        internal,
                        "inflated from {} bytes {} MB",
                        actual_bytes as isize,
                        cfmt_f64("%.1f", actual_mb)
                    );
                    msg!(
                        internal,
                        "factor {} ({}% compression)",
                        cfmt_f64("%.2f", relative(read_bytes as f64, actual_bytes as f64)),
                        cfmt_f64("%.2f", percent(actual_bytes as f64, read_bytes as f64))
                    );
                }
            }
        }
    }

    pub fn flush(&mut self) {
        debug_assert!(!self.file.is_null());
        // SAFETY: open stream.
        unsafe {
            libc::fflush(self.file);
        }
    }
}

impl File {
    /// `File (Internal *, bool writing, int close, int child_pid, FILE *, const char *name)`.
    pub fn new(
        internal: *mut Internal,
        writing: bool,
        close: i32,
        child_pid: i32,
        file: *mut libc::FILE,
        name: &str,
    ) -> File {
        debug_assert!(!file.is_null());
        File {
            internal,
            writing,
            close_file: close,
            child_pid,
            file,
            _name: name.to_string(),
            _lineno: 1,
            _bytes: 0,
        }
    }
}

impl Drop for File {
    fn drop(&mut self) {
        if !self.file.is_null() {
            self.close(false);
        }
    }
}
