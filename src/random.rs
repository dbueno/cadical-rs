//! Port of `random.hpp` and `random.cpp`: the (bit-exact) random number
//! generator.

use crate::util::hash_string;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Random {
    state: u64,
}

impl Random {
    #[inline]
    fn add(&mut self, a: u64) {
        self.state = self.state.wrapping_add(a);
        if self.state == 0 {
            self.state = 1;
        }
        self.next();
    }

    /// `Random (uint64_t seed)`.
    #[inline]
    pub fn new(seed: u64) -> Random {
        Random { state: seed }
    }

    /// `operator= (uint64_t seed)`.
    #[inline]
    pub fn set_seed(&mut self, seed: u64) {
        self.state = seed;
    }

    #[inline]
    pub fn seed(&self) -> u64 {
        self.state
    }

    #[inline]
    pub fn next(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005u64);
        self.state = self.state.wrapping_add(1442695040888963407u64);
        debug_assert!(self.state != 0);
        self.state
    }

    #[inline]
    pub fn generate(&mut self) -> u32 {
        self.next();
        (self.state >> 32) as u32
    }

    #[inline]
    pub fn generate_int(&mut self) -> i32 {
        self.generate() as i32
    }

    #[inline]
    pub fn generate_bool(&mut self) -> bool {
        self.generate() < 2147483648u32
    }

    /// Generate `double` value in the range `[0,1]`.
    #[inline]
    pub fn generate_double(&mut self) -> f64 {
        self.generate() as f64 / 4294967295.0
    }

    /// Generate `int` value in the range `[l,r]`.
    pub fn pick_int(&mut self, l: i32, r: i32) -> i32 {
        debug_assert!(l <= r);
        let delta: u32 = 1u32.wrapping_add(r as u32).wrapping_sub(l as u32);
        let tmp: u32 = self.generate();
        let scaled: u32;
        if delta != 0 {
            let fraction = tmp as f64 / 4294967296.0;
            scaled = (delta as f64 * fraction) as u32;
        } else {
            scaled = tmp;
        }
        let res = scaled.wrapping_add(l as u32) as i32;
        debug_assert!(l <= res);
        debug_assert!(res <= r);
        res
    }

    pub fn pick_log(&mut self, l: i32, r: i32) -> i32 {
        debug_assert!(l <= r);
        let delta: u32 = 1u32.wrapping_add(r as u32).wrapping_sub(l as u32);
        let mut log_delta: i32 = if delta != 0 { 0 } else { 32 };
        while log_delta < 32 && (1u32 << log_delta) < delta {
            log_delta += 1;
        }
        let log_res = self.pick_int(0, log_delta);
        let mut tmp = self.generate();
        if log_res < 32 {
            tmp &= (1u32 << log_res).wrapping_sub(1);
        }
        if delta != 0 {
            tmp %= delta;
        }
        let res = (l as u32).wrapping_add(tmp) as i32;
        debug_assert!(l <= res);
        debug_assert!(res <= r);
        res
    }

    /// Generate `double` value in the range `[l,r]`.
    pub fn pick_double(&mut self, l: f64, r: f64) -> f64 {
        debug_assert!(l <= r);
        let mut res = (r - l) * self.generate_double();
        res += l;
        debug_assert!(l <= res);
        debug_assert!(res <= r);
        res
    }

    /// `Random ()`: machine, process and time dependent seed (port of
    /// `random.cpp`).
    pub fn new_random() -> Random {
        let mut r = Random { state: 1 };
        r.add(hash_machine_identifier());
        r.add(hash_network_addresses());
        r.add(hash_clock_cycles());
        r.add(hash_process());
        r.add(hash_time());
        r
    }
}

impl std::ops::AddAssign<u64> for Random {
    /// `operator+= (uint64_t a)`.
    #[inline]
    fn add_assign(&mut self, a: u64) {
        self.add(a)
    }
}

/*------------------------------------------------------------------------*/

// Port of 'random.cpp' (seeding helpers).

fn hash_machine_identifier() -> u64 {
    match std::fs::read("/var/lib/dbus/machine-id") {
        Ok(bytes) => {
            let n = bytes.len().min(127);
            if n > 0 {
                // C string semantics: stop at the first zero byte.
                let s: Vec<u8> = bytes[..n].iter().copied().take_while(|&b| b != 0).collect();
                hash_string(&String::from_utf8_lossy(&s))
            } else {
                0
            }
        }
        Err(_) => 0,
    }
}

fn hash_network_addresses() -> u64 {
    let mut res: u64 = 0;
    // SAFETY: plain libc calls with properly sized buffers.
    unsafe {
        let mut addrs: *mut libc::ifaddrs = std::ptr::null_mut();
        if libc::getifaddrs(&mut addrs) == 0 {
            let mut addr = addrs;
            while !addr.is_null() {
                let a = &*addr;
                addr = a.ifa_next;
                if a.ifa_addr.is_null() {
                    continue;
                }
                let family = (*a.ifa_addr).sa_family as i32;
                if family == libc::AF_INET || family == libc::AF_INET6 {
                    let size = if family == libc::AF_INET {
                        std::mem::size_of::<libc::sockaddr_in>()
                    } else {
                        std::mem::size_of::<libc::sockaddr_in6>()
                    };
                    let mut buffer = [0 as libc::c_char; 128];
                    if libc::getnameinfo(
                        a.ifa_addr,
                        size as libc::socklen_t,
                        buffer.as_mut_ptr(),
                        buffer.len() as libc::socklen_t,
                        std::ptr::null_mut(),
                        0,
                        libc::NI_NUMERICHOST,
                    ) == 0
                    {
                        let s = std::ffi::CStr::from_ptr(buffer.as_ptr());
                        let tmp = hash_string(&s.to_string_lossy());
                        res ^= tmp;
                        res = res.wrapping_mul(10000000000000000051u64);
                    }
                }
            }
            libc::freeifaddrs(addrs);
        }
    }
    res
}

fn hash_time() -> u64 {
    // SAFETY: 'time (0)'.
    unsafe { libc::time(std::ptr::null_mut()) as u64 }
}

fn hash_process() -> u64 {
    // SAFETY: 'getpid ()'.
    unsafe { libc::getpid() as u64 }
}

extern "C" {
    fn clock() -> libc::clock_t;
}

fn hash_clock_cycles() -> u64 {
    // SAFETY: 'std::clock ()'.
    unsafe { clock() as u64 }
}
