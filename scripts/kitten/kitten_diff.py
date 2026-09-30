#!/usr/bin/env python3
"""Differential testing of the kitten port against kitten.c.

Generates random API call sequences (see kitten_driver.c for the command
language), runs the C reference driver and the Rust driver
(examples/kitten_driver.rs) on each and requires identical stdout and
the same exit class (success / crash, since both have assertions enabled).

usage: kitten_diff.py C_DRIVER RUST_DRIVER OUTDIR COUNT [SEED] [--log]
"""

import os
import random
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor


def gen(rng, logging):
    out = []
    n = rng.randint(1, rng.choice([4, 8, 16, 40]))
    next_id = [1]
    # hard mode: random 3-SAT near the threshold (many conflicts)
    hard = [rng.random() < 0.35]
    if hard[0]:
        n = rng.randint(20, 250)
    tracked = [False]

    def reset():
        if rng.random() < 0.85:
            out.append("track")
            tracked[0] = True
        else:
            tracked[0] = False
        if logging:
            out.append("log")

    def lit():
        v = rng.randint(1, n)
        return v if rng.random() < 0.5 else -v

    def clause():
        if hard[0]:
            k = min(3, n)
            vs = rng.sample(range(1, n + 1), k)
            return [v if rng.random() < 0.5 else -v for v in vs]
        r = rng.random()
        if r < 0.01:
            k = 0
        elif r < 0.08:
            k = 1
        elif r < 0.3:
            k = 2
        else:
            k = rng.randint(3, min(n, 6)) if n >= 3 else n
        k = min(k, n)
        vs = rng.sample(range(1, n + 1), k)
        return [v if rng.random() < 0.5 else -v for v in vs]

    def add_clause():
        c = clause()
        r = rng.random()
        i = next_id[0]
        next_id[0] += 1
        if r < 0.55 or not c:
            out.append("c %d %s 0" % (i, " ".join(map(str, c))))
        elif r < 0.7:
            ex = rng.choice(c) if rng.random() < 0.7 else lit()
            out.append("x %d %d %s 0" % (i, ex, " ".join(map(str, c))))
        elif r < 0.85:
            a = rng.choice(c) if rng.random() < 0.5 else lit()
            b = lit()
            if rng.random() < 0.5:
                a = -a
            out.append("e %d %d %d %s 0" % (i, a, b, " ".join(map(str, c))))
        else:
            out.append("k %s 0" % " ".join(map(str, c)))

    reset()
    ratio = rng.choice([2.0, 3.5, 4.3, 5.0, 8.0])
    rounds = rng.randint(1, 8)
    first = True
    for _ in range(rounds):
        if rng.random() < 0.12:
            out.append("clear")
            reset()
            n = rng.randint(1, rng.choice([4, 8, 16, 40]))
        if hard[0] and first:
            m = int(rng.uniform(3.9, 4.6) * n)
        else:
            m = rng.randint(0, int(ratio * n / rounds) + 2)
        first = False
        for _ in range(m):
            add_clause()
        for _ in range(rng.randint(0, 2)):
            out.append(rng.choice(["rand", "flipph", "shuffle"]))
        na = rng.choice([0, 0, 1, 2, 3, 5])
        for _ in range(na):
            out.append("%s %d" % ("a" if rng.random() < 0.8 else "au", lit()))
        r = rng.random()
        if r < 0.25:
            out.append("limit %d" % rng.randint(0, 400))
        elif r < 0.35:
            out.append("nolimit")
        r = rng.random()
        if r < 0.08:
            out.append("term %d" % rng.randint(0, 30))
        elif r < 0.12:
            out.append("noterm")
        out.append("s")
        out.append("status")
        vars_ = list(range(1, n + 1))
        for v in vars_:
            out.append("v %d" % v)
        out.append("vu %d" % lit())
        for _ in range(rng.randint(0, 3)):
            out.append("f %d" % lit())
        for _ in range(rng.randint(0, 4)):
            out.append("F %d" % lit())
        r = rng.random()
        if r < 0.25:
            out.append("prime")
            out.append("addprime %d" % rng.randint(0, 1))
            if rng.random() < 0.5:
                add_clause()
                out.append("s")
        elif r < 0.4:
            out.append("jflip %d" % lit())
            if rng.random() < 0.5:
                out.append("addprime %d" % rng.randint(0, 1))
        else:
            for _ in range(rng.randint(0, 4)):
                out.append("p %d" % lit())
            for v in vars_:
                out.append("v %d" % v)
        if rng.random() < 0.8:
            out.append("core" if rng.random() < 0.8 else "core0")
            # shrinking requires an inconsistent formula (not failing
            # assumptions), otherwise kitten.c reads out of bounds
            # (with logging, kitten.c logs stale clause data during
            # shrinking, which is undefined behaviour, thus not in --log)
            if na == 0 and not logging and rng.random() < 0.4:
                out.append("shrink")
                if rng.random() < 0.5:
                    out.append("shuffle")
                if rng.random() < 0.5:
                    out.append("limit %d" % rng.randint(0, 1000))
                out.append("s")
                out.append("core")
        out.append("ticks")
        out.append("dump")
    out.append("dump")
    return "\n".join(out) + "\n"


def classify(rc):
    return "ok" if rc == 0 else "crash"


def run_one(args):
    cdrv, rdrv, outdir, idx, seed, logging = args
    rng = random.Random(seed * 1000003 + idx)
    text = gen(rng, logging)
    path = os.path.join(outdir, "t%06d.txt" % idx)
    with open(path, "w") as f:
        f.write(text)
    c = subprocess.run([cdrv, path], capture_output=True)
    r = subprocess.run([rdrv, path], capture_output=True)
    same = c.stdout == r.stdout and classify(c.returncode) == classify(r.returncode)
    # For crashes compare only the stdout (both flushed per command).
    if not same:
        with open(path + ".c.out", "wb") as f:
            f.write(c.stdout + b"\n--- stderr\n" + c.stderr)
        with open(path + ".rs.out", "wb") as f:
            f.write(r.stdout + b"\n--- stderr\n" + r.stderr)
    else:
        os.remove(path)
    return idx, same, c.returncode, r.returncode, c.stdout.count(b"\ns ")


def main():
    argv = [a for a in sys.argv[1:] if a != "--log"]
    logging = "--log" in sys.argv
    cdrv, rdrv, outdir, count = argv[0], argv[1], argv[2], int(argv[3])
    seed = int(argv[4]) if len(argv) > 4 else 1
    os.makedirs(outdir, exist_ok=True)
    fails = 0
    crashes = 0
    solves = 0
    jobs = [(cdrv, rdrv, outdir, i, seed, logging) for i in range(count)]
    with ThreadPoolExecutor(max_workers=os.cpu_count()) as ex:
        for idx, same, crc, rrc, ns in ex.map(run_one, jobs):
            solves += ns
            if crc != 0:
                crashes += 1
            if not same:
                fails += 1
                print("MISMATCH t%06d (c rc %d, rust rc %d)" % (idx, crc, rrc))
    print("tests %d mismatches %d crashes(both) %d solve calls %d"
          % (count, fails, crashes, solves))
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
