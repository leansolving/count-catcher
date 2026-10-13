"""Generation modes of the drivers' GEN, and the race of structural generation against a
second mode (the `race` value).

Modes (generator options added to GEN_FL): struct (cpog-gen's structural mode), mono (-m,
monolithic: one SAT call), hybrid (-M GEN_M -W GEN_W of cpog-gen-fwd: a node whose subgraph has
tree size at most GEN_M is justified by one SAT call, once the first GEN_W structural
justifications have made at least one SAT call per 100; scratchpad measurements 2026-10-02 in
tools-src/README.md).

The race: monolithic or hybrid generation is many times faster on low-sharing circuits and
much slower on sharing-rich ones, so structural generation and the contender run at once, each
in its own subdirectory of the work directory (cpog-gen writes temporary files into its
working directory) and in its own session, i.e. process group, so that the loser is killed
together with its cadical and drat-trim children. The first run that exits 0 with a non-empty
certificate wins; its cert.cpog and gen.log move into the work directory. The hybrid
contender runs without the gate (-M GEN_M only), since structural generation covers the
circuits where the hybrid does not pay. Used by count_catcher.py, m2_worker.py and graph_orbits.py
(keep this file next to them).
"""

import os
import shutil
import signal
import subprocess
import time

GEN_M, GEN_W = 10000, 100  # hybrid: subgraph tree-size limit (-M) and gate warm-up (-W)


def mode_flags(mode):
    """Generator options of a generation mode (struct, mono, hybrid)."""
    return {"struct": [], "mono": ["-m"], "hybrid": ["-M", str(GEN_M), "-W", str(GEN_W)]}[mode]


RACE_FLAGS = {"mono": ["-m"], "hybrid": ["-M", str(GEN_M)]}  # the contender (no gate)


def _kill(pid):
    """SIGTERM to the process group, up to a second for its leader to exit, then SIGKILL to
    the group (children that outlived the leader), then reap. killpg on a group whose members
    have all exited gives ESRCH, or EPERM on macOS while they are unreaped."""
    def killpg(sig):
        try:
            os.killpg(pid, sig)
        except (ProcessLookupError, PermissionError):
            pass
    killpg(signal.SIGTERM)
    for _ in range(20):
        try:
            if os.waitpid(pid, os.WNOHANG)[0]:
                break
        except ChildProcessError:
            break
        time.sleep(0.05)
    killpg(signal.SIGKILL)
    try:
        os.waitpid(pid, 0)
    except ChildProcessError:
        pass


def race(gen_bin, flags, cnf, nnf, d, env=None, timeout=0, contender="hybrid"):
    """Run `gen_bin flags CNF NNF cert.cpog` in d/g_struct and the same with the contender's
    options (RACE_FLAGS: mono or hybrid) in d/g_CONTENDER.
    Returns {"winner": "struct" | contender | None, "wall_s", "exit": {mode: code}, "s": {mode:
    seconds}, "maxrss": ru_maxrss of the winner (kB on Linux, bytes on macOS), "timeout"}.
    The modes that have not finished when there is a winner (or after timeout seconds, 0 =
    none) are killed; the subdirectories are removed. Without a winner, struct's gen.log is
    copied to d for diagnosis."""
    t0 = time.time()
    res = {"winner": None, "exit": {}, "s": {}, "maxrss": 0, "timeout": False}
    procs, logs = {}, {}
    modes = (("struct", []), (contender, RACE_FLAGS[contender]))
    for mode, extra in modes:
        sub = os.path.join(d, "g_" + mode)
        os.makedirs(sub, exist_ok=True)
        logs[mode] = open(os.path.join(sub, "gen.log"), "w")
        procs[mode] = subprocess.Popen(
            [gen_bin, *extra, *flags, os.path.abspath(cnf), os.path.abspath(nnf), "cert.cpog"],
            cwd=sub, stdout=logs[mode], stderr=subprocess.STDOUT, env=env,
            start_new_session=True)
    running = dict(procs)
    while running and res["winner"] is None:
        for mode, p in list(running.items()):
            pid, status, ru = os.wait4(p.pid, os.WNOHANG)
            if pid == 0:
                continue
            del running[mode]
            p.returncode = code = os.waitstatus_to_exitcode(status)
            res["exit"][mode], res["s"][mode] = code, round(time.time() - t0, 2)
            cert = os.path.join(d, "g_" + mode, "cert.cpog")
            if code == 0 and os.path.exists(cert) and os.path.getsize(cert) > 0:
                res["winner"], res["maxrss"] = mode, ru.ru_maxrss
                break
        if running and res["winner"] is None:
            if timeout and time.time() - t0 > timeout:
                res["timeout"] = True
                break
            time.sleep(0.1)
    for p in running.values():
        _kill(p.pid)
        p.returncode = -signal.SIGKILL
    for f in logs.values():
        f.close()
    w = res["winner"]
    if w:
        for f in ("cert.cpog", "gen.log"):
            os.replace(os.path.join(d, "g_" + w, f), os.path.join(d, f))
    else:
        shutil.copy(os.path.join(d, "g_struct", "gen.log"), os.path.join(d, "gen.log"))
    for mode, _ in modes:
        shutil.rmtree(os.path.join(d, "g_" + mode), ignore_errors=True)
    res["wall_s"] = round(time.time() - t0, 2)
    return res
