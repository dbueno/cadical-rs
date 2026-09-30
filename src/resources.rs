//! Port of `resources.hpp` and `resources.cpp` (Unix only).

use crate::internal::Internal;

pub fn absolute_real_time() -> f64 {
    // SAFETY: 'gettimeofday' with a valid buffer.
    unsafe {
        let mut tv: libc::timeval = std::mem::zeroed();
        if libc::gettimeofday(&mut tv, std::ptr::null_mut()) != 0 {
            return 0.0;
        }
        1e-6 * tv.tv_usec as f64 + tv.tv_sec as f64
    }
}

/// We use 'getrusage' for 'process_time' and 'maximum_resident_set_size'.
pub fn absolute_process_time() -> f64 {
    // SAFETY: 'getrusage' with a valid buffer.
    unsafe {
        let mut u: libc::rusage = std::mem::zeroed();
        if libc::getrusage(libc::RUSAGE_SELF, &mut u) != 0 {
            return 0.0;
        }
        let mut res = u.ru_utime.tv_sec as f64 + 1e-6 * u.ru_utime.tv_usec as f64; // user time
        res += u.ru_stime.tv_sec as f64 + 1e-6 * u.ru_stime.tv_usec as f64; // + system time
        res
    }
}

pub fn maximum_resident_set_size() -> u64 {
    // SAFETY: 'getrusage' with a valid buffer.
    unsafe {
        let mut u: libc::rusage = std::mem::zeroed();
        if libc::getrusage(libc::RUSAGE_SELF, &mut u) != 0 {
            return 0;
        }
        #[cfg(not(target_os = "macos"))]
        {
            (u.ru_maxrss as u64) << 10
        }
        #[cfg(target_os = "macos")]
        {
            u.ru_maxrss as u64
        }
    }
}

/// Uses the '/proc' file system (returns 0 if not available).
pub fn current_resident_set_size() -> u64 {
    // SAFETY: 'getpid'.
    let pid = unsafe { libc::getpid() } as i64;
    let path = format!("/proc/{}/statm", pid);
    let content = match std::fs::read_to_string(&path) {
        Ok(c) => c,
        Err(_) => return 0,
    };
    let mut it = content.split_whitespace();
    let dummy = it.next().and_then(|s| s.parse::<u64>().ok());
    let rss = it.next().and_then(|s| s.parse::<u64>().ok());
    match (dummy, rss) {
        (Some(_), Some(rss)) => {
            // SAFETY: 'sysconf'.
            let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as u64;
            rss * page
        }
        _ => 0,
    }
}

impl Internal {
    /// Real time since solver was initialized.
    pub fn real_time(&self) -> f64 {
        absolute_real_time() - self.stats.time.real
    }

    /// Process time since solver was initialized.
    pub fn process_time(&self) -> f64 {
        absolute_process_time() - self.stats.time.process
    }
}
