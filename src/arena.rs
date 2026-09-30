//! Port of `arena.hpp` and `arena.cpp`: memory arena for the moving
//! garbage collector `copy_non_garbage_clauses` in `collect.cpp`.
//!
//! The standard sequence of using the arena is as follows:
//!
//! ```text
//!   arena.prepare (bytes);
//!   q1 = arena.copy (p1, bytes1);
//!   ...
//!   qn = arena.copy (pn, bytesn);
//!   arena.swap ();
//!   ...
//!   if (!arena.contains (q)) delete q;
//! ```

use crate::internal::Internal;

#[derive(Clone, Copy, Debug)]
pub struct ArenaSpace {
    pub start: *mut u8,
    pub top: *mut u8,
    pub end: *mut u8,
}

impl ArenaSpace {
    const EMPTY: ArenaSpace = ArenaSpace {
        start: std::ptr::null_mut(),
        top: std::ptr::null_mut(),
        end: std::ptr::null_mut(),
    };
}

pub struct Arena {
    pub internal: *mut Internal,
    pub from: ArenaSpace,
    pub to: ArenaSpace,
}

impl Arena {
    pub fn new(i: *mut Internal) -> Arena {
        Arena { internal: i, from: ArenaSpace::EMPTY, to: ArenaSpace::EMPTY }
    }

    /// Prepare 'to' space to hold that amount of memory.  Precondition is
    /// that the 'to' space is empty.
    pub fn prepare(&mut self, bytes: usize) {
        #[cfg(feature = "logging")]
        if !self.internal.is_null() {
            // SAFETY: the arena is a field of a live 'Internal'.
            let internal = unsafe { &*self.internal };
            log!(internal, "preparing 'to' space of arena with {} bytes", bytes);
        }
        debug_assert!(self.to.start.is_null());
        // 'new char[bytes]' (malloc returns suitably aligned memory).
        // SAFETY: allocation of at least one byte.
        let p = unsafe { libc::malloc(bytes.max(1)) } as *mut u8;
        if p.is_null() {
            crate::message::fatal(format_args!("out of memory preparing arena"));
        }
        self.to.start = p;
        self.to.top = p;
        // SAFETY: within (one past) the allocation.
        self.to.end = unsafe { p.add(bytes) };
    }

    /// Does the memory pointed to by `p` belong to this arena?  More
    /// precisely to the 'from' space, since that is the only one remaining
    /// after 'swap'.
    #[inline]
    pub fn contains(&self, p: *const u8) -> bool {
        let c = p as *mut u8;
        (self.from.start <= c && c < self.from.top) || (self.to.start <= c && c < self.to.top)
    }

    /// Allocate that amount of memory in 'to' space and copy the memory
    /// pointed to by `p` of size `bytes` into it.
    #[inline]
    pub fn copy(&mut self, p: *const u8, bytes: usize) -> *mut u8 {
        let res = self.to.top;
        // SAFETY: 'prepare' reserved enough memory (asserted).
        unsafe {
            self.to.top = self.to.top.add(bytes);
            debug_assert!(self.to.top <= self.to.end);
            std::ptr::copy_nonoverlapping(p, res, bytes);
        }
        res
    }

    /// Completely delete 'from' space and then replace 'from' by 'to' (by
    /// pointer swapping).
    pub fn swap(&mut self) {
        // SAFETY: 'from.start' was obtained from 'malloc' (or is null).
        unsafe { libc::free(self.from.start as *mut libc::c_void) };
        #[cfg(feature = "logging")]
        if !self.internal.is_null() {
            // SAFETY: the arena is a field of a live 'Internal'.
            let internal = unsafe { &*self.internal };
            log!(
                internal,
                "delete 'from' space of arena with {} bytes",
                (self.from.end as usize).wrapping_sub(self.from.start as usize)
            );
        }
        self.from = self.to;
        self.to = ArenaSpace::EMPTY;
    }
}

impl Drop for Arena {
    fn drop(&mut self) {
        // SAFETY: both spaces were allocated with 'malloc' (or are null).
        unsafe {
            libc::free(self.from.start as *mut libc::c_void);
            libc::free(self.to.start as *mut libc::c_void);
        }
    }
}
