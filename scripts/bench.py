#!/usr/bin/env python3
"""Head-to-head benchmark harness for cadical-rs against the reference CaDiCaL.

Runs a CaDiCaL-CLI-compatible solver on every instance of a list, keeps full
logs, and checks:

  (a) no crash: exit code must be 10 (SAT), 20 (UNSAT) or 0 (limit reached),
      consistent with the 's ...' status line;
  (b) status agrees with the reference CSV whenever both decided;
  (c) SAT models are verified with dimocheck;
  (d) --proof: UNSAT results are re-run with a proof (LRAT with --lrat, DRAT
      otherwise) and the proof is checked with lrat-trim / drat-trim; checker
      timeouts are reported separately from failures;
  (e) --compare-stats: 'c conflicts:', 'c decisions:', 'c propagations:' counts
      must be identical to the reference (bit-exact behaviour target).

Without --ref-csv the harness simply classifies instances; its output CSV has
the same format that --ref-csv expects (this is how reference.csv is built).

Python 3 standard library only.

Examples
  scripts/bench.py --solver target/release/cadical \\
      --ref-csv /Volumes/Shampoo/cadical-rs/bench/reference.csv \\
      --list /Volumes/Shampoo/cadical-rs/bench/quick.txt \\
      --jobs 12 --timeout 60 --out /Volumes/Shampoo/cadical-rs/bench/runs/rs-quick \\
      --compare-stats --proof --lrat
"""

import argparse
import concurrent.futures as cf
import csv
import datetime
import json
import lzma
import os
import re
import shlex
import shutil
import signal
import subprocess
import sys
import threading
import time

TOOLS = "/Volumes/Shampoo/cadical-rs/result-1/bin"
DEFAULT_MEMGUARD = os.path.expanduser("~/.claude/skills/memory-guard/memguard.sh")
STAT_KEYS = ("conflicts", "decisions", "propagations")
DECIDED = ("SAT", "UNSAT")

FIELDS = [
    "instance", "status", "exit_code", "wall", "conflicts", "decisions",
    "propagations", "peak_mem_mb", "ref_status", "agree", "model", "proof",
    "proof_wall", "stats", "stats_detail", "verdict", "log",
]


# ---------------------------------------------------------------- utilities

def run_limited(cmd, stdout_path, stderr_path, timeout, mem_gib, memguard):
    """Run cmd with stdout/stderr to files, killing its whole process group
    after `timeout` seconds. Returns (returncode, wall, timed_out)."""
    if mem_gib and memguard:
        cmd = [memguard, str(mem_gib)] + cmd
    t0 = time.monotonic()
    with open(stdout_path, "wb") as out, open(stderr_path, "wb") as err:
        p = subprocess.Popen(cmd, stdout=out, stderr=err, stdin=subprocess.DEVNULL,
                             start_new_session=True)
        timed_out = False
        try:
            rc = p.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            rc = p.wait()
    return rc, time.monotonic() - t0, timed_out


def parse_solver_log(path):
    """Return dict with 's' status line and statistic counts."""
    res = {"s": None}
    stat_re = re.compile(r"^c (%s):\s+(\d+)" % "|".join(STAT_KEYS))
    with open(path, "rb") as f:
        for raw in f:
            if raw.startswith(b"v "):
                continue
            line = raw.decode("utf-8", "replace").rstrip("\n")
            if line.startswith("s "):
                res["s"] = line[2:].strip()
            else:
                m = stat_re.match(line)
                if m and m.group(1) not in res:
                    res[m.group(1)] = int(m.group(2))
    return res


def parse_time_l(path):
    """Peak memory (MB), real time (s) from `/usr/bin/time -l` in stderr, plus
    whether memguard killed the job."""
    peak, rss, killed, real = None, None, False, None
    try:
        with open(path, errors="replace") as f:
            for line in f:
                m = re.match(r"\s*([\d.]+) real\s", line)
                if m:
                    real = float(m.group(1))
                elif "peak memory footprint" in line:
                    peak = int(line.split()[0])
                elif "maximum resident set size" in line:
                    rss = int(line.split()[0])
                elif line.startswith("memguard:") and "killing" in line:
                    killed = True
    except FileNotFoundError:
        pass
    v = peak if peak is not None else rss
    return (round(v / 2**20, 1) if v is not None else None), killed, real


def safe_name(path):
    return os.path.basename(path).replace(".cnf", "").replace(".xz", "").replace(".gz", "")


def decompress(src, dst):
    if src.endswith(".xz"):
        opener = lzma.open
    elif src.endswith(".gz"):
        import gzip
        opener = gzip.open
    else:
        opener = open
    with opener(src, "rb") as i, open(dst, "wb") as o:
        shutil.copyfileobj(i, o, 1 << 22)


def load_ref(path):
    ref = {}
    if not path:
        return ref
    with open(path, newline="") as f:
        for r in csv.DictReader(f):
            ref[os.path.realpath(r["instance"])] = r
    return ref


# ---------------------------------------------------------------- one instance

class Runner:
    def __init__(self, a):
        self.a = a
        self.solver_args = shlex.split(a.solver_args or "")
        self.memguard = a.memguard if (a.mem_limit and os.path.exists(a.memguard)) else None
        self.lock = threading.Lock()

    def solver_cmd(self, inst, extra=()):
        a = self.a
        cmd = ["/usr/bin/time", "-l", a.solver] + self.solver_args
        if a.timeout:
            cmd += ["-t", str(int(a.timeout))]
        cmd += list(extra) + [inst]
        return cmd

    def run(self, idx, inst, ref):
        a = self.a
        base = f"{idx:05d}-{safe_name(inst)}"
        log = os.path.join(a.out, "logs", base + ".log")
        err = os.path.join(a.out, "logs", base + ".err")
        hard = a.timeout * 1.1 + 15 if a.timeout else None
        cmd = self.solver_cmd(inst)
        with open(os.path.join(a.out, "logs", base + ".cmd"), "w") as f:
            f.write(shlex.join(cmd) + "\n")
        rc, wall, killed_to = run_limited(cmd, log, err, hard, a.mem_limit, self.memguard)
        info = parse_solver_log(log)
        peak, killed_mem, real = parse_time_l(err)
        if real is not None and not killed_to:
            wall = real  # excludes memguard polling latency
        s = info["s"]
        if killed_to:
            status = "TIMEOUT"
        elif killed_mem or rc == 137:
            status = "MEMOUT"
        elif rc == 10 and s == "SATISFIABLE":
            status = "SAT"
        elif rc == 20 and s == "UNSATISFIABLE":
            status = "UNSAT"
        elif rc == 0 and s in (None, "UNKNOWN"):
            status = "UNKNOWN"
        elif rc < 0 or rc > 128:
            status = "CRASH"
        else:
            status = "ERROR"  # inconsistent exit code / status line
        row = dict(instance=inst, status=status, exit_code=rc, wall=round(wall, 3),
                   peak_mem_mb=peak, log=log)
        for k in STAT_KEYS:
            row[k] = info.get(k)

        # (b) agreement with reference
        rs = ref.get("status") if ref else None
        row["ref_status"] = rs or ""
        if rs in DECIDED and status in DECIDED:
            row["agree"] = "agree" if rs == status else "DISAGREE"
        else:
            row["agree"] = "n/a"

        # (c) model check
        row["model"] = "n/a"
        if status == "SAT":
            out = os.path.join(a.out, "logs", base + ".dimocheck")
            c = [a.dimocheck, inst, log]
            crc, _, cto = run_limited(c, out, out + ".err", a.check_timeout, None, None)
            row["model"] = "ok" if crc == 0 and not cto else ("timeout" if cto else "FAIL")

        # (d) proof check
        row["proof"], row["proof_wall"] = "n/a", ""
        if a.proof and status == "UNSAT":
            row["proof"], row["proof_wall"] = self.proof(inst, base)

        # (e) statistics comparison
        row["stats"], row["stats_detail"] = "n/a", ""
        if a.compare_stats and ref:
            if status in DECIDED and rs in DECIDED:
                diffs = []
                for k in STAT_KEYS:
                    mine, theirs = row[k], ref.get(k)
                    theirs = int(theirs) if theirs not in (None, "") else None
                    if mine != theirs:
                        diffs.append(f"{k}:{mine}!={theirs}")
                row["stats"] = "identical" if not diffs else "DIFF"
                row["stats_detail"] = " ".join(diffs)

        bad = (status in ("CRASH", "ERROR") or row["agree"] == "DISAGREE"
               or row["model"] == "FAIL" or row["proof"] == "FAIL" or row["stats"] == "DIFF")
        row["verdict"] = "FAIL" if bad else "ok"
        return row

    def proof(self, inst, base):
        a = self.a
        pdir = os.path.join(a.out, "proofs")
        ext = ".lrat" if a.lrat else ".drat"
        proof = os.path.join(pdir, base + ext)
        cnf = os.path.join(pdir, base + ".cnf")
        plog = os.path.join(a.out, "logs", base + ".proofrun.log")
        extra = ["--lrat"] if a.lrat else []
        if not a.binary_proof:
            extra.append("--no-binary")
        cmd = self.solver_cmd(inst, extra) + [proof]
        with open(os.path.join(a.out, "logs", base + ".proofrun.cmd"), "w") as f:
            f.write(shlex.join(cmd) + "\n")
        hard = a.timeout * 1.1 + 15 if a.timeout else None
        rc, _, _ = run_limited(cmd, plog, plog + ".err", hard, a.mem_limit, self.memguard)
        if rc != 20:
            self._cleanup(proof, None, keep=True)
            return f"solver-rc-{rc}", ""
        try:
            decompress(inst, cnf)
            clog = os.path.join(a.out, "logs", base + ".proofcheck.log")
            if a.lrat:
                c = [a.lrat_trim, cnf, proof]
            else:
                c = [a.drat_trim, cnf, proof, "-t", str(int(a.proof_timeout)), "-w"]
            with open(os.path.join(a.out, "logs", base + ".proofcheck.cmd"), "w") as f:
                f.write(shlex.join(c) + "\n")
            crc, cwall, cto = run_limited(c, clog, clog + ".err", a.proof_timeout + 10,
                                          a.mem_limit, self.memguard)
            text = open(clog, errors="replace").read()
            if a.lrat:
                ok = crc == 20 and "s VERIFIED" in text
            else:
                ok = crc == 0 and "s VERIFIED" in text
            if cto or (not a.lrat and "TIMEOUT" in text):
                verdict = "timeout"
            elif ok:
                verdict = "verified"
            else:
                verdict = "FAIL"
            self._cleanup(proof, cnf, keep=a.keep_proofs or verdict == "FAIL")
            return verdict, round(cwall, 3)
        except Exception as e:  # noqa
            self._cleanup(proof, cnf, keep=True)
            return f"FAIL", f"exception: {e}"

    @staticmethod
    def _cleanup(proof, cnf, keep):
        if cnf and os.path.exists(cnf):
            os.remove(cnf)
        if not keep and os.path.exists(proof):
            os.remove(proof)


# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--solver", required=True, help="solver binary (CaDiCaL CLI)")
    ap.add_argument("--ref-csv", help="reference CSV (as produced by this script)")
    ap.add_argument("--list", required=True, help="file with one instance path per line")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--timeout", type=float, default=60, help="seconds; passed as -t and enforced externally")
    ap.add_argument("--out", required=True, help="output directory (logs, CSV, summary)")
    ap.add_argument("--solver-args", default="", help="extra solver arguments (quoted string)")
    ap.add_argument("--proof", action="store_true", help="re-run UNSAT instances with a proof and check it")
    ap.add_argument("--lrat", action="store_true", help="with --proof: LRAT + lrat-trim (default DRAT + drat-trim)")
    ap.add_argument("--no-binary-proof", dest="binary_proof", action="store_false",
                    help="with --proof: ASCII proof (--no-binary)")
    ap.add_argument("--proof-timeout", type=float, default=600, help="proof checker timeout (s)")
    ap.add_argument("--keep-proofs", action="store_true", help="keep verified proof files")
    ap.add_argument("--compare-stats", action="store_true",
                    help="require identical conflicts/decisions/propagations vs reference")
    ap.add_argument("--check-timeout", type=float, default=300, help="dimocheck timeout (s)")
    ap.add_argument("--mem-limit", type=int, default=8, help="GiB cap per job via memguard (0 = off)")
    ap.add_argument("--memguard", default=DEFAULT_MEMGUARD)
    ap.add_argument("--dimocheck", default=f"{TOOLS}/dimocheck")
    ap.add_argument("--lrat-trim", default=f"{TOOLS}/lrat-trim")
    ap.add_argument("--drat-trim", default=f"{TOOLS}/drat-trim")
    ap.add_argument("--resume", action="store_true",
                    help="keep rows already in DIR/results.csv and only run the missing instances")
    a = ap.parse_args()

    a.solver = os.path.abspath(a.solver)
    a.out = os.path.abspath(a.out)
    os.makedirs(os.path.join(a.out, "logs"), exist_ok=True)
    os.makedirs(os.path.join(a.out, "proofs"), exist_ok=True)
    insts = [os.path.abspath(l.strip()) for l in open(a.list)
             if l.strip() and not l.startswith("#")]
    ref = load_ref(a.ref_csv)
    if a.compare_stats and a.solver_args:
        print("warning: --compare-stats with --solver-args: reference was run with default options",
              file=sys.stderr)
    if a.mem_limit and not os.path.exists(a.memguard):
        print(f"warning: memguard not found at {a.memguard}; running without memory cap",
              file=sys.stderr)

    with open(os.path.join(a.out, "config.json"), "w") as f:
        json.dump(dict(vars(a), started=datetime.datetime.now().isoformat(),
                       n_instances=len(insts)), f, indent=2)

    runner = Runner(a)
    csv_path = os.path.join(a.out, "results.csv")
    rows = []
    if a.resume and os.path.exists(csv_path):
        with open(csv_path, newline="") as f:
            rows = [r for r in csv.DictReader(f)
                    if r.get("verdict") and r.get("status") != "HARNESS-ERROR"]
        with open(csv_path, "w", newline="") as f:  # drop partial/errored rows
            w = csv.DictWriter(f, fieldnames=FIELDS, extrasaction="ignore")
            w.writeheader()
            w.writerows(rows)
        print(f"resume: {len(rows)} instances already done", flush=True)
    done = {r["instance"] for r in rows}
    todo = [(i, p) for i, p in enumerate(insts) if p not in done]
    t0 = time.monotonic()
    with open(csv_path, "a" if rows else "w", newline="") as fcsv:
        w = csv.DictWriter(fcsv, fieldnames=FIELDS, extrasaction="ignore")
        if not rows:
            w.writeheader()
        with cf.ThreadPoolExecutor(a.jobs) as ex:
            futs = {ex.submit(runner.run, i, p, ref.get(os.path.realpath(p))): p
                    for i, p in todo}
            for n, fut in enumerate(cf.as_completed(futs), 1):
                p = futs[fut]
                try:
                    row = fut.result()
                except Exception as e:  # noqa
                    row = dict(instance=p, status="HARNESS-ERROR", verdict="FAIL",
                               stats_detail=repr(e))
                rows.append(row)
                w.writerow(row)
                fcsv.flush()
                flag = "" if row.get("verdict") == "ok" else "  <-- FAIL"
                print(f"[{n}/{len(todo)} {time.monotonic() - t0:7.0f}s] {row.get('status', ''):8} "
                      f"{row.get('wall', '')!s:>8}s model={row.get('model', '')} "
                      f"proof={row.get('proof', '')} stats={row.get('stats', '')} "
                      f"{os.path.basename(p)}{flag}", flush=True)

    summary = summarize(rows, a)
    print(summary)
    with open(os.path.join(a.out, "summary.txt"), "w") as f:
        f.write(summary + "\n")
    sys.exit(0 if all(r.get("verdict") == "ok" for r in rows) else 1)


def summarize(rows, a):
    from collections import Counter

    def table(title, counter):
        lines = [f"{title}:"]
        for k, v in sorted(counter.items(), key=lambda kv: (-kv[1], str(kv[0]))):
            lines.append(f"  {k!s:<16} {v:6d}")
        return "\n".join(lines)

    out = ["", "=" * 60, f"instances: {len(rows)}   solver: {a.solver}"]
    out.append(table("status", Counter(r.get("status") for r in rows)))
    out.append(table("agreement with reference", Counter(r.get("agree") for r in rows)))
    out.append(table("model check (dimocheck)", Counter(r.get("model") for r in rows)))
    if a.proof:
        out.append(table(f"proof check ({'lrat-trim' if a.lrat else 'drat-trim'})",
                         Counter(r.get("proof") for r in rows)))
    if a.compare_stats:
        out.append(table("statistics vs reference", Counter(r.get("stats") for r in rows)))
    solved = [r for r in rows if r.get("status") in DECIDED]
    out.append(f"solved: {len(solved)}  total wall of solved: "
               f"{sum(float(r['wall']) for r in solved):.1f}s")
    # Head-to-head time on commonly solved instances
    both = [r for r in solved if r.get("ref_status") in DECIDED]
    if both and a.ref_csv:
        ref = load_ref(a.ref_csv)
        mine = sum(float(r["wall"]) for r in both)
        theirs = sum(float(ref[os.path.realpath(r["instance"])]["wall"]) for r in both)
        out.append(f"commonly solved: {len(both)}  wall ours {mine:.1f}s vs ref {theirs:.1f}s"
                   f"  (ratio {mine / theirs if theirs else float('nan'):.2f})")
    fails = [r for r in rows if r.get("verdict") != "ok"]
    out.append(f"FAILURES: {len(fails)}")
    for r in fails[:50]:
        out.append(f"  {r.get('status')} agree={r.get('agree')} model={r.get('model')} "
                   f"proof={r.get('proof')} stats={r.get('stats')} {r.get('stats_detail', '')} "
                   f"{r.get('instance')}")
    out.append(f"results: {os.path.join(a.out, 'results.csv')}")
    out.append("=" * 60)
    return "\n".join(out)


if __name__ == "__main__":
    main()
