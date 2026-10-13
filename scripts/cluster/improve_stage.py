"""Run one stage of improve_gen.sbatch or improve_check.sbatch and record it.

Usage: python3 improve_stage.py RESULT NAME TIMEOUT OUT CMD [ARGS...]

Runs CMD in its own process group (cwd inherited), stdout and stderr to the file OUT (`-`:
discarded), and appends key=value lines to RESULT:
  NAME_s         wall seconds
  NAME_cpu_s     user + system seconds of the process tree (wait4)
  NAME_rss_mb    peak RSS of the largest process in the tree (wait4 ru_maxrss; covers children
                 the command waited for, e.g. lean under `lake env`)
  NAME_exit      exit code; 124 after TIMEOUT seconds (the group is killed), 128+N on signal N
  NAME_mono0_ms, NAME_mono1_ms   CLOCK_MONOTONIC at start and end in ms, the clock of Lean's
                 IO.monoMsNow, so stamps printed by Lean can be placed inside the stage
TIMEOUT 0 means none. The exit status of this script is NAME_exit. /usr/bin/time does not exist
on the compute nodes, hence this wrapper.
"""

import os
import signal
import subprocess
import sys
import threading
import time


def main():
    res, name, timeout, out = sys.argv[1], sys.argv[2], float(sys.argv[3]), sys.argv[4]
    cmd = sys.argv[5:]
    f = open(os.devnull if out == "-" else out, "wb")
    m0, t0 = time.monotonic(), time.time()
    p = subprocess.Popen(cmd, stdout=f, stderr=subprocess.STDOUT, start_new_session=True)
    fired = []

    def kill():
        fired.append(1)
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass

    timer = threading.Timer(timeout, kill) if timeout > 0 else None
    if timer:
        timer.start()
    _, status, ru = os.wait4(p.pid, 0)
    if timer:
        timer.cancel()
    t1, m1 = time.time(), time.monotonic()
    f.close()
    code = os.waitstatus_to_exitcode(status)
    code = 124 if fired else (128 - code if code < 0 else code)
    p.returncode = code
    with open(res, "a") as r:
        r.write(f"{name}_s={t1 - t0:.1f}\n")
        r.write(f"{name}_cpu_s={ru.ru_utime + ru.ru_stime:.1f}\n")
        r.write(f"{name}_rss_mb={ru.ru_maxrss / 1024:.0f}\n")
        r.write(f"{name}_exit={code}\n")
        r.write(f"{name}_mono0_ms={int(m0 * 1000)}\n{name}_mono1_ms={int(m1 * 1000)}\n")
    sys.exit(code)


if __name__ == "__main__":
    main()
