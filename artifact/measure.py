"""Run one install step and record its wall time and peak memory.

    python3 artifact/measure.py STEP LOG STATS -- CMD [ARGS...]

CMD's output is appended to LOG. Once a second the process tree of CMD is sampled: the sum of
the proportional set sizes (PSS, from /proc/PID/smaps_rollup; shared pages such as Mathlib's
mapped .olean files count once over all processes) and the sum of the resident set sizes (RSS,
counts shared pages once per process, so it overstates parallel Lean builds). When the cgroup
v2 file memory.stat of this process is readable, its anonymous memory (the part the kernel
cannot reclaim, page cache excluded) is sampled too. One tab-separated line is appended to
STATS: step, exit status, wall seconds, peak PSS sum, peak RSS sum, peak cgroup anon (MiB;
`-` if unavailable). The exit status of CMD is returned. Standard library only.
"""

import os
import signal
import subprocess
import sys
import time

MIB = 1024 * 1024


def children_map():
    kids = {}
    for d in os.listdir("/proc"):
        if not d.isdigit():
            continue
        try:
            with open(f"/proc/{d}/stat") as f:
                s = f.read()
        except OSError:
            continue
        # the command name is in parentheses and may contain spaces
        ppid = int(s[s.rfind(")") + 2:].split()[1])
        kids.setdefault(ppid, []).append(int(d))
    return kids


def tree(root):
    kids = children_map()
    out, todo = [], [root]
    while todo:
        p = todo.pop()
        out.append(p)
        todo.extend(kids.get(p, []))
    return out


def mem_kb(pid):
    """(PSS, RSS) of one process in kB; (0, 0) if it is gone or unreadable."""
    pss = rss = 0
    try:
        with open(f"/proc/{pid}/smaps_rollup") as f:
            for line in f:
                if line.startswith("Pss:"):
                    pss = int(line.split()[1])
                elif line.startswith("Rss:"):
                    rss = int(line.split()[1])
    except OSError:
        try:
            with open(f"/proc/{pid}/status") as f:
                for line in f:
                    if line.startswith("VmRSS:"):
                        rss = pss = int(line.split()[1])
        except OSError:
            pass
    return pss, rss


def cgroup_stat():
    try:
        with open("/proc/self/cgroup") as f:
            path = next(l.split(":", 2)[2].strip() for l in f if l.startswith("0::"))
        p = f"/sys/fs/cgroup{path}/memory.stat"
        open(p).close()
        return p
    except (OSError, StopIteration):
        return None


def cgroup_anon(p):
    try:
        with open(p) as f:
            for line in f:
                if line.startswith("anon "):
                    return int(line.split()[1])
    except OSError:
        pass
    return None


def main():
    if len(sys.argv) < 6 or sys.argv[4] != "--":
        sys.exit(__doc__.strip().splitlines()[2])
    step, log, stats, cmd = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[5:]
    cg = cgroup_stat()
    peak_pss = peak_rss = 0
    peak_cg = None
    t0 = time.time()
    with open(log, "ab") as out:
        child = subprocess.Popen(cmd, stdout=out, stderr=subprocess.STDOUT, start_new_session=True)

        def forward(sig, _frame):
            try:
                os.killpg(child.pid, sig)
            except OSError:
                pass

        signal.signal(signal.SIGINT, forward)
        signal.signal(signal.SIGTERM, forward)
        while True:
            try:
                rc = child.wait(timeout=1.0)
                break
            except subprocess.TimeoutExpired:
                pass
            pss = rss = 0
            for p in tree(child.pid):
                a, b = mem_kb(p)
                pss += a
                rss += b
            peak_pss, peak_rss = max(peak_pss, pss), max(peak_rss, rss)
            if cg:
                a = cgroup_anon(cg)
                if a is not None:
                    peak_cg = max(peak_cg or 0, a)
    wall = time.time() - t0
    cgs = "-" if peak_cg is None else str(round(peak_cg / MIB))
    with open(stats, "a") as f:
        f.write(f"{step}\t{rc}\t{wall:.0f}\t{round(peak_pss / 1024)}\t{round(peak_rss / 1024)}\t{cgs}\n")
    sys.exit(rc if rc >= 0 else 128 - rc)


if __name__ == "__main__":
    main()
