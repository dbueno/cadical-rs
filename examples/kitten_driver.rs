//! Differential test driver for the kitten port (Rust side).
//!
//! Reads kitten API calls from a file (one per line) and prints the
//! results in exactly the same format as the C reference driver
//! `scripts/kitten/kitten_driver.c`.  See `scripts/kitten/kitten_diff.py`.

use cadical::cprintf;
use cadical::kitten::*;
use cadical::message::{c_stdout, fflush};

static mut TERM_CALLS: i64 = 0;
static mut TERM_LIMIT: i64 = 0;

fn cb_terminator(_data: *mut libc::c_void) -> i32 {
    // SAFETY: single threaded driver.
    unsafe {
        TERM_CALLS += 1;
        (TERM_CALLS > TERM_LIMIT) as i32
    }
}

fn int2u(lit: i32) -> u32 {
    (lit < 0) as u32 + 2 * (lit.abs() - 1) as u32
}

fn print_lits(prefix: &str, lits: &[u32]) {
    cprintf!("{}", prefix);
    for l in lits {
        cprintf!(" {}", l);
    }
    cprintf!("\n");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: kitten_driver <commands>");
        std::process::exit(1);
    }
    let text = std::fs::read_to_string(&args[1]).expect("can not read commands");
    let mut toks = text.split_ascii_whitespace();
    let mut k = kitten_init();
    let mut tracked = false;
    macro_rules! next_i {
        () => {
            toks.next().unwrap().parse::<i64>().unwrap()
        };
    }
    while let Some(cmd) = toks.next() {
        cprintf!("> {}\n", cmd);
        match cmd {
            "clear" => {
                kitten_clear(&mut k);
                tracked = false;
            }
            "track" => {
                kitten_track_antecedents(&mut k);
                tracked = true;
            }
            "log" => {
                #[cfg(feature = "logging")]
                kitten_set_logging(&mut k);
            }
            "c" | "x" | "e" | "k" => {
                let mut id = 0u32;
                let mut a = 0i32;
                let mut b = 0i32;
                if cmd != "k" {
                    id = next_i!() as u32;
                }
                if cmd == "x" || cmd == "e" {
                    a = next_i!() as i32;
                }
                if cmd == "e" {
                    b = next_i!() as i32;
                }
                let mut ints = Vec::new();
                loop {
                    let lit = next_i!() as i32;
                    if lit == 0 {
                        break;
                    }
                    ints.push(lit);
                }
                let uns: Vec<u32> = ints.iter().map(|&l| int2u(l)).collect();
                match cmd {
                    "c" => citten_clause_with_id(&mut k, id, &ints),
                    "x" => citten_clause_with_id_and_exception(&mut k, id, &ints, int2u(a)),
                    "e" => citten_clause_with_id_and_equivalence(&mut k, id, &ints, int2u(a), int2u(b)),
                    _ => {
                        if uns.len() == 1 {
                            kitten_unit(&mut k, uns[0]);
                        } else if uns.len() == 2 {
                            kitten_binary(&mut k, uns[0], uns[1]);
                        } else {
                            kitten_clause(&mut k, &uns);
                        }
                    }
                }
            }
            "a" => {
                let lit = next_i!() as i32;
                kitten_assume_signed(&mut k, lit);
            }
            "au" => {
                let lit = next_i!() as i32;
                kitten_assume(&mut k, int2u(lit));
            }
            "s" => {
                let res = kitten_solve(&mut k);
                let status = kitten_status(&mut k);
                let ticks = kitten_current_ticks(&mut k);
                cprintf!("s {} status {} ticks {}\n", res, status, ticks);
            }
            "limit" => {
                let d: u64 = toks.next().unwrap().parse().unwrap();
                kitten_set_ticks_limit(&mut k, d);
            }
            "nolimit" => kitten_no_ticks_limit(&mut k),
            "ticks" => {
                let t = kitten_current_ticks(&mut k);
                cprintf!("ticks {}\n", t);
            }
            "term" => {
                let n = next_i!();
                // SAFETY: single threaded driver.
                unsafe {
                    TERM_CALLS = 0;
                    TERM_LIMIT = n;
                }
                kitten_set_terminator(&mut k, std::ptr::null_mut(), cb_terminator);
            }
            "noterm" => kitten_no_terminator(&mut k),
            "v" | "vu" => {
                let lit = next_i!() as i32;
                if kitten_status(&mut k) == 10 {
                    let v = if cmd == "vu" {
                        kitten_value(&mut k, int2u(lit))
                    } else {
                        kitten_signed_value(&mut k, lit)
                    };
                    cprintf!("v {} {}\n", lit, v as i32);
                }
            }
            "f" => {
                let lit = next_i!() as i32;
                let v = kitten_fixed_signed(&mut k, lit);
                cprintf!("f {} {}\n", lit, v as i32);
            }
            "F" => {
                let lit = next_i!() as i32;
                if kitten_status(&mut k) == 20 {
                    let v = kitten_failed(&mut k, int2u(lit));
                    cprintf!("F {} {}\n", lit, v as i32);
                }
            }
            "p" => {
                let lit = next_i!() as i32;
                if kitten_status(&mut k) == 10 {
                    let v = kitten_flip_signed_literal(&mut k, lit);
                    cprintf!("p {} {}\n", lit, v as i32);
                }
            }
            "core" => {
                if kitten_status(&mut k) == 20 && tracked {
                    let mut learned = 0u64;
                    let original = kitten_compute_clausal_core(&mut k, Some(&mut learned));
                    cprintf!("core {} {}\n", original, learned);
                    kitten_traverse_core_ids(&mut k, &mut |id| {
                        cprintf!("coreid {}\n", id);
                    });
                    kitten_traverse_core_clauses(&mut k, &mut |learned, lits| {
                        cprintf!("coreclause {}", learned as i32);
                        print_lits("", lits);
                    });
                    kitten_traverse_core_clauses_with_id(&mut k, &mut |id, learned, lits| {
                        cprintf!("coreclauseid {} {}", id, learned as i32);
                        print_lits("", lits);
                    });
                    kitten_trace_core(&mut k, &mut |cid, id, learned, lits, chain| {
                        cprintf!("trace {} {} {}", cid, id, learned as i32);
                        print_lits(" lits", lits);
                        print_lits("  chain", chain);
                    });
                }
            }
            "core0" => {
                if kitten_status(&mut k) == 20 && tracked {
                    let original = kitten_compute_clausal_core(&mut k, None);
                    cprintf!("core0 {}\n", original);
                }
            }
            "shrink" => {
                if kitten_status(&mut k) == 21 {
                    kitten_shrink_to_clausal_core(&mut k);
                }
            }
            "rand" => kitten_randomize_phases(&mut k),
            "flipph" => kitten_flip_phases(&mut k),
            "shuffle" => {
                if kitten_status(&mut k) == 0 {
                    kitten_shuffle_clauses(&mut k);
                }
            }
            "prime" => {
                if kitten_status(&mut k) == 10 {
                    let res = kitten_compute_prime_implicant(&mut k, &mut |id| id % 3 == 0);
                    cprintf!("prime {}\n", res);
                }
            }
            "addprime" => {
                let side = next_i!() as i32;
                if kitten_status(&mut k) == 11 {
                    kitten_add_prime_implicant(&mut k, side, &mut |side, lits| {
                        cprintf!("implicant {}", side);
                        print_lits("", lits);
                    });
                }
            }
            "jflip" => {
                let lit = next_i!() as i32;
                if kitten_status(&mut k) == 10 {
                    let res = kitten_flip_and_implicant_for_signed_literal(&mut k, lit);
                    cprintf!("jflip {} {}\n", lit, res);
                }
            }
            "status" => {
                let s = kitten_status(&mut k);
                cprintf!("status {}\n", s);
            }
            "dump" => {
                let s = kitten_dump_state(&k);
                cprintf!("{}", s);
            }
            _ => {
                eprintln!("unknown command '{}'", cmd);
                std::process::exit(2);
            }
        }
        fflush(c_stdout());
    }
    kitten_release(k);
    cprintf!("done\n");
    fflush(c_stdout());
}
