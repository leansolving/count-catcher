---
keywords: [cpog-gen, reverse implication, deletions, forward only, -F, cpog-gen-norev, patch, certificate size, generation time, peak memory]
context: When deciding whether to generate CPOG certificates without the reverse-direction deletions, rebuilding cpog-gen-norev, or reading the with/without comparison
added: 2026-09-30
---
# cpog-gen without the reverse half (2026-09-30)

## Insight

- No existing option. cpog-gen a97ed85 has `-1` (one-sided: asserts the root without a forward
  proof, keeps the input-clause deletions), the opposite of what mccert needs. The SCPOG
  generator (rebryant/scpog, `cpog/generator/cpog-generate`, SAT 2025) has `-a f` (forward
  implication only), compiles the derived-clause deletions out (`DELETE_FULL 0`) and deletes
  input clauses only with a disabled `-d`, so it confirms the design; but it writes the SCPOG
  format (`as`, `t`, `S`, `m` steps), which neither translator accepts, and its forward proof
  differs (monolithic thresholds), so it is no drop-in replacement.
- Where the deletions come from (`tools/cpog/src`): `Cnf_reasoner::start_assertion` pushes a
  vector (clause ID plus every hint, copied again in `add_hint`) onto `deletion_stack` for each
  addition; after the root unit, `delete_assertions()` pops the stack and writes a `d` line for
  every addition except the root unit, then `cpog-gen.cpp run()` loops over all input clauses
  and `Pog::delete_input_clause` walks all POG nodes per clause to build the RUP hint
  (O(|F| times |POG|) time; it is also cpog-gen's overcount check).
- Patch `tools-src/cpog-gen-noreverse.patch` (3 files, 20 lines added, 2 changed): option `-F`,
  default off. `start_assertion` records no deletion vector; `run()` returns after the root
  unit. Everything before the deletions is byte-identical: the `-F` certificate equals the
  default certificate with its `d` lines removed (checked on every instance below by sha1).
  Built without `-march` (plain `-O2`, no GMP), so no SIGILL risk: ran on b501 (Zen 2), b403
  (Broadwell) and slurm-cpu01 (Zen 4). Installed as `tools/bin/cpog-gen-norev` on the Mac and
  the cluster (source tree `/home1/szeider/mccert/tools/cpog-norev`); `cpog-gen` untouched.
- Translators need no change: `scripts/cpog2lrat.py` and `tools-src/cpog2lrat` skip every `d`
  line, take the root from the `r` line (written when the POG is read, before the proof) and
  the root unit from the additions, and size their ID maps from additions and declarations.
- Lean on the Mac (2026-09-30): domino 8x8 (`lean/test/data/dom08.dimacs`) and 8-queens
  (`scripts/gen_queens.py 8`) through D4, `cpog-gen-norev -F`, both translators: `.cnf`,
  `.lrat`, `.pog` identical to those from the default certificate (with and without
  `--delete`) and to the committed `lean/test/data/{dom08,q08}.*`. Copies of `Dom08.lean` and
  `Queens8.lean` on the new files check: 12,988,816 and 92, axioms `propext`,
  `Classical.choice`, `Quot.sound` and one `native_decide` axiom; the wrong count 12,988,817
  is rejected.
- Earlier logs already show the time split (scoping 2026-09-28, EPYC 7402, unmodified
  cpog-gen, seconds): the reverse half is 5 to 28 percent on dominoes and queens and 56 to 71
  percent on the grids; nearly all of it is the input-clause loop.

| Instance | total | forward done | derived-clause deletions | input-clause deletions | reverse share |
|---|---:|---:|---:|---:|---:|
| domino 10x10 | 27 | 26 | 0 | 1 | 5 % |
| domino 12x12 | 373 | 345 | 4 | 24 | 7 % |
| grid 12x12 | 7 | 3 | 0 | 4 | 56 % |
| grid 14x14 | 94 | 34 | 2 | 57 | 63 % |
| grid 16x16 | 1313 | 376 | 39 | 897 | 71 % |
| 12-queens | 121 | 100 | 3 | 18 | 17 % |
| 13-queens | 932 | 722 | 16 | 194 | 22 % |
| 14-queens | 5389 | 3892 | 91 | 1406 | 28 % |

## Cluster measurement (2026-09-30)

`scope/norev.sbatch` (local copy `scripts/cluster/norev.sbatch`), list `scope/norev_list.txt`,
results `scope/results/norev/INST.txt` plus both gen logs. Per instance, one job on
slurm-cpu01 (`-C genoa -c 2`, 32 GB, 13-queens 64 GB as in `e2e.sbatch`): D4 once, then
cpog-gen and `cpog-gen-norev -F` one after the other, each in its own job step (wall s,
peak RSS of the process tree, cgroup `memory.peak` of the step, which includes the page cache
of the certificate), certificate bytes, sha1 check. Certificates only in `$SLURM_TMPDIR`.

- Jobs 113300 (array 1-13: dom12, q12, ind14, cub120, games120, mc2022 track1_037, track2_005,
  track1_103, track2_011, track2_095, track2_125, track2_091, track1_069) and 113301 (q13,
  64 GB), ran 2026-09-30 from 16:41 to 17:34. Final state (sacct, checked 2026-09-30 22:35):
  all 14 tasks COMPLETED, exit 0:0, all on slurm-cpu01; every result file has `status=ok`, D4,
  full and forward exit 0, and matching sha1. Longest task: track2_091, 42:54 elapsed.

| Instance | clauses | full s | fwd s | time saved | full GB | fwd GB | bytes saved | input-del share of full | full RSS GB | fwd RSS GB | full cg GB | fwd cg GB | reverse in log s (derived + input) | sha1 ok | status |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|
| dom12 | 868 | 246.5 | 225.3 | 9 % | 0.93 | 0.50 | 46 % | 27 % | 2.28 | 1.90 | 3.33 | 2.50 | 19 (2 + 17) | yes | ok |
| q12 | 2608 | 100.6 | 76.5 | 24 % | 0.91 | 0.41 | 56 % | 41 % | 1.20 | 0.94 | 2.20 | 1.41 | 21 (2 + 19) | yes | ok |
| ind14 | 364 | 98.1 | 31.9 | 67 % | 1.10 | 0.33 | 70 % | 59 % | 3.25 | 2.95 | 4.49 | 3.39 | 66 (2 + 64) | yes | ok |
| cub120 | 180 | 186.0 | 92.7 | 50 % | 3.01 | 1.08 | 64 % | 52 % | 8.63 | 7.79 | 11.98 | 9.13 | 93 (5 + 88) | yes | ok |
| games120 | 638 | 336.0 | 83.5 | 75 % | 3.56 | 0.86 | 76 % | 68 % | 8.05 | 7.43 | 11.95 | 8.54 | 253 (3 + 249) | yes | ok |
| mc2022_track1_037 | 1776 | 7.1 | 1.5 | 79 % | 0.07 | 0.04 | 47 % | 30 % | 0.15 | 0.12 | 0.26 | 0.19 | 6 (0 + 5) | yes | ok |
| mc2022_track2_005 | 250 | 77.1 | 38.4 | 50 % | 1.79 | 0.91 | 49 % | 33 % | 3.42 | 2.83 | 5.38 | 3.87 | 38 (3 + 35) | yes | ok |
| mc2022_track1_103 | 2638 | 203.3 | 152.8 | 25 % | 5.62 | 5.03 | 11 % | 5 % | 6.27 | 5.44 | 12.25 | 10.79 | 50 (4 + 46) | yes | ok |
| mc2022_track2_011 | 523 | 341.1 | 145.3 | 57 % | 6.69 | 3.47 | 48 % | 32 % | 11.55 | 9.57 | 18.76 | 13.42 | 190 (11 + 179) | yes | ok |
| mc2022_track2_095 | 120524 | 329.1 | 27.0 | 92 % | 0.42 | 0.32 | 24 % | 19 % | 0.69 | 0.64 | 1.17 | 1.07 | 301 (0 + 301) | yes | ok |
| mc2022_track2_125 | 1533 | 706.2 | 684.8 | 3 % | 2.29 | 1.39 | 39 % | 5 % | 3.31 | 2.27 | 5.78 | 3.86 | 19 (7 + 12) | yes | ok |
| mc2022_track2_091 | 1898 | 1433.5 | 1043.9 | 27 % | 12.98 | 7.53 | 42 % | 27 % | 19.88 | 15.84 | 33.81 | 24.03 | 530 (24 + 506) | yes | ok |
| mc2022_track1_069 | 57629 | 1896.4 | 218.9 | 88 % | 1.95 | 1.40 | 28 % | 16 % | 2.88 | 2.36 | 4.99 | 3.94 | 1694 (3 + 1691) | yes | ok |
| q13 | 3341 | 635.3 | 509.7 | 20 % | 6.12 | 2.85 | 54 % | 40 % | 7.76 | 6.21 | 14.31 | 9.33 | 155 (10 + 145) | yes | ok |

Columns: wall seconds of each cpog-gen run; GB = 1e9 bytes; input-del share = bytes of the
input-clause deletions (last M lines) over the full certificate; RSS = peak RSS of the process
tree (getrusage); cg = cgroup memory.peak of the run's job step (includes the page cache of
the written certificate); reverse in log = time after the root unit in the full run's log.
The RSS columns are ru_maxrss (KiB) divided by 1e6, as in the first partial table; in units of
1e9 bytes they are 2.4 % higher.

Summary (14 of 14 instances completed; families = dom12, q12, q13, ind14, cub120, games120;
MC2022 = the other 8):

- Bytes saved: families 46 to 76 % (dom12 and queens 46 to 56 %, ind14, cub120, games120 64 to
  76 %), MC2022 11 to 49 %. Over all 14 instances 47.5 GB of full certificates become 26.1 GB
  (45 % saved). Bytes saved exceed the input-del share by the derived-clause deletions, 5 to 34
  percentage points; track2_125 has the largest gap (39 % saved, 5 % input deletions).
- Time saved: families 9 to 75 % (dom12 9 %, queens 20 to 24 %, ind14, cub120, games120 50 to
  75 %), MC2022 3 to 92 %. Summed wall time 6596 s becomes 3332 s (49 % saved). The saving is
  the input-clause loop: it is largest on the two MC2022 instances with many clauses (track2_095,
  120,524 clauses, 92 %; track1_069, 57,629 clauses, 88 %) and smallest where the forward proof
  dominates (track2_125, 3 %: 354 of its 706 s are SAT calls and the reverse half takes 19 s;
  dom12, 9 %).
- Peak memory: the forward run is lower on every instance. Peak RSS drops by 8 to 22 % on the
  families and 7 to 31 % on MC2022, the cgroup peak by 24 to 36 % and 8 to 33 %. Largest values:
  full RSS 8.63 GB on the families (cub120) and 19.88 GB on MC2022 (track2_091), forward 7.79 and
  15.84 GB. The full run of track2_091 reached a cgroup peak of 33.81 GB, 98 % of the 32 GiB
  (34.36 GB) request (page cache included); its forward run peaked at 24.03 GB.
