# Paper rerun, 2026-10-02

Status: R1, R2, R4 and R5 complete; R3 170 of 180 at 15:05 (written incrementally).

## Pipeline and provenance

- Sources: commit `68fc5685260e077f0100519e4eb59729640f5693` (`git archive HEAD lean scripts
  tools-src`), cluster copy `/home1/szeider/mccert/final/src/68fc568/`.
- Lean: private copy `/home1/szeider/mccert/lean_final` (lean/ of the commit; Mathlib and the other
  packages of `lean/.lake/packages` symlinked read-only, own lrat-catcher clone at `b2e8d59`);
  McCert, McCertMath, McCertTool built on slurm-login01; plugin sha256: see `rerun_raw/`
  (fields `sha256_plugin_*` of every e2e result).
- Tools: `/home1/szeider/mccert/tools_final/bin`.
  - `cpog-gen-fwd` built from the commit's two patches on rebryant/cpog a97ed85 (gcc, `-O2`, no
    warnings), sha256 `b028452a88c9bf7de8121b0e47812b80863ded6577285f3d149ef8b5bc293561`.
  - `cpog2lrat` built by `tools-src/cpog2lrat/build.sh`, sha256
    `77151b2cf2d457b79f373da2b7c0cb3cd8dcef34fe260218a2e4906ddfe82bf2`.
  - Symlinks to the shared `tools/bin`: `d4` (sha256 `90ac342f…`, d4fat), `cpog-gen` (unpatched,
    `4bc1baa0…`, used only for the full certificate of the CPOG comparison), `cpog-check`
    (`65e4e226…`), `cpog-lean-check` (`5bea4cc5…`), `cadical`, `drat-trim`.
- Pipeline: D4 `-dDNNF`; `cpog-gen-fwd -F -T 500 -G` (structural, one core);
  `cpog2lrat --delete --binary --trim --keep --inline` (INLINE=1: 14-queens with inlining proved
  in 307.2 s and 308.4 s against 488 s without, in the earlier before/after measurements on
  stored certificates, 2026-10-02); Lean streamed with the keep mask (`count_models +stream … (keep := …)`, THM=command).
- Driver: `scripts/cluster/e2e.sbatch` with two changes for this rerun: `TOOLS` (directory put
  first on PATH) and `SCRIPTS` also for `pog_count.py`; and CPOG_CHECK=1 no longer switches our
  own pipeline to the full generator: our pipeline runs unchanged, then the full certificate is
  generated from the same D4 output by the unpatched `cpog-gen` (fields `gen_full_s`,
  `gen_full_maxrss_kb`, `gen_full_bytes`) and CPOG's checkers run on it; both certificates are
  deleted. Checked on domino 8x8 (job 120984, b414): proved 12,988,816; forward certificate
  2,976,419 bytes, full 6,089,162 bytes; `cpog-check` and `cpog-lean-check` succeed with the same
  count.
- Array wrappers: `scripts/cluster/rerun_funnel.sbatch` (R3, R4), `scripts/cluster/rerun_showcase.sbatch`
  (R2). Results on the cluster under `/home1/szeider/mccert/final/results/`.

## R1 families

All 11 proved on slurm-cpu01 (EPYC 9554P, `-C genoa`, `-c 2`), 10:14 to 11:13, node load 55
to 65 on 128 threads (another user's jobs). Object-level statements through the family lemmas
(`count_models +stream … via (LEMMA) … (keep := …)`), streamed with the keep mask and inlining
for every row (the canonical table of 2026-09-29 embedded four of them). "gen" is
`cpog-gen-fwd -F -T 500 -G`; "Lean" is the whole `lake env lean` run (Mathlib import and
elaboration included); "Lean GB" is the peak RSS of the Lean process (`lean_maxrss_kb`, which
includes about 3 GB of memory-mapped Mathlib .olean files); part B and parts A and C are the
verified evaluations reported by `count_models`. Every count equals D4's and `pog_count.py`'s.

| theorem | count | CPOG bytes | LRAT bytes | D4 s | gen s | gen GB | translator s | part B s | parts A, C s | Lean total s | Lean GB |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `domino_12x12` | 53,060,477,521,960,000 | 500,069,353 | 142,116,532 | 3.4 | 225.4 | 0.8 | 5.6 | 10.2 | 0.7 | 20.1 | 3.6 |
| `queens12` | 14,200 | 406,310,128 | 70,318,165 | 3.3 | 73.9 | 0.3 | 4.4 | 6.0 | 0.5 | 12.9 | 3.5 |
| `queens13` | 73,712 | 2,845,838,650 | 490,472,254 | 22.5 | 461.2 | 1.9 | 28.9 | 39.8 | 4.4 | 56.0 | 4.5 |
| `queens14` | 365,596 | 18,194,257,525 | 3,119,344,359 | 174.0 | 2,740.8 | 10.5 | 188.7 | 268.6 | 28.2 | 302.5 | 9.3 |
| `grid14_indepSets` | 3.39e35 | 327,924,698 | 50,361,186 | 13.8 | 36.4 | 0.9 | 4.4 | 6.0 | 5.1 | 23.1 | 5.0 |
| `grid16_indepSets` | 1.84e46 | 3,548,722,499 | 525,868,552 | 181.0 | 421.8 | 8.7 | 43.7 | 63.1 | 59.2 | 136.7 | 20.8 |
| `Q_6` (64 / 192) | 19,768,832,143 | 68,081,073 | 8,939,847 | 1.5 | 3.7 | 0.2 | 0.9 | 1.3 | 0.6 | 11.9 | 3.5 |
| random cubic 100 | 8,281,581,627,129,350,099 | 117,828,761 | 15,442,090 | 4.5 | 11.2 | 0.3 | 1.6 | 2.1 | 1.3 | 12.8 | 4.0 |
| random cubic 120 | 5.00e22 | 1,076,388,251 | 143,114,891 | 34.5 | 101.6 | 2.4 | 13.1 | 17.0 | 10.9 | 39.7 | 8.3 |
| games120 | 30,467,298,966,717 | 860,632,202 | 131,735,140 | 28.8 | 88.3 | 2.0 | 10.9 | 15.5 | 15.2 | 43.1 | 7.5 |
| homer (561 / 1628) | 4.99e123 | 32,710,675 | 3,623,227 | 2.4 | 6.2 | 0.1 | 0.5 | 0.6 | 0.6 | 12.4 | 3.4 |

Exact counts: grid 14 338,752,110,195,939,290,445,247,645,371,206,783; grid 16
18,396,766,424,410,124,752,958,806,046,933,947,217,821,482,942; random cubic 120
50,037,826,758,434,291,658,793; homer 4990279720487638784402415134793666363321484439419783396315037955127460372623831147937096773412337132142531994684416327680000.
Against the theorem table of 2026-09-29: Lean total 175 to 56.0 s (13-queens),
1,028 to 302.5 s (14-queens), 480 to 136.7 s (grid 16); 14-queens generation 3,497 s (full
cpog-gen, 86.7 GB cgroup peak) to 2,740.8 s at 10.5 GB.

## R2 showcases

All 8 proved, each through its own driver with `lean_final` and `tools_final`, one job per
showcase (`scripts/cluster/rerun_showcase.sbatch`, 64 GB); all landed on slurm-cpu01
(`-C 'bc5|genoa'`), 10:15 to 11:13. "gen" is the generator time (graph drivers: wall time of
all certificates, run in parallel with `-j` = the job's CPUs); "Lean" is the whole Lean run;
"Lean GB" the Lean process's peak RSS; "end to end" the driver's wall time (export, D4,
generation, translation, Lean).

| showcase | driver and options | count | CPOG bytes | gen s | Lean s | Lean GB | end to end s | CPUs | native axioms |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| X1 triangle-free graphs, 10 vertices, up to isomorphism | `graph_orbits.py --family clique:3 --n 10 --inline -j 8` (no `--split`, as the recorded run) | 12,172 classes (19,213,627,145 labelled) | 2,308,341,453 (42 terms) | 146.3 | 74.8 | 9.2 | 232 | 8 | 44 (`tri10_isoClasses`: 47 axioms, 44 native, as on 2026-09-30) |
| X2 Dedekind M(7) | `showcase/dedekind.py --n 7` | 2,414,682,040,998 | 1,678,830,332 | 116.9 | 88.8 (B 59.7, A+C 19.2) | 9.3 | 273 | 2 | 2 |
| X3 Latin squares of order 7 (fallback for order 8) | `showcase/latin_cycles.py --n 7 --inline` (4 cycle-type fibres, no split) | 16,942,080 reduced | 697,847,194 (4 leaves) | 26.6 (4 leaves) | 64.0 (4 leaves 12.6 to 14.2 each, assembly 11.6) | 4.0 (assembly), 3.6 (leaves) | 135 | 2 | 8 (assembly: 11 axioms) |
| X4 (3,5)-Ramsey graph on 13 vertices, unique | `graph_orbits.py --family ramsey:3:5 --n 13 --split --witness "(circulantGraph ({1, 5} : Set (Fin 13)))" --inline -j 8` | 1 class (119,750,400 labelled) | 3,361,510,423 (4 certified terms, 109 refuted) | 668.1 | 78.9 | 5.4 | 759 | 8 | 115 |
| X5 A358391(6), Kreweras | `showcase/kreweras.py --n 6` | 206,103,695,057,137,712 | 2,936,129,321 | 206.7 | 170.5 (B 108.5, A+C 57.3) | 13.4 | 510 | 2 | 2 |
| X5 A396728(7), Sperner | `showcase/sperner.py --n 7` (see below) | 696,132,184,469 | 7,181,575,662 | 271.8 | 424.6 (B 292.5, A+C 126.9) | 18.2 | 923 | 2 | 2 |
| X5 A303210(9), total domination | `showcase/a303210.py --n 9` | 72,691,237,364,024,529,045,028 | 4,321,918,260 | 167.2 | 145.0 (B 122.2, A+C 17.8) | 11.8 | 446 | 2 | 2 |
| X5 A303210(10) | `showcase/a303210.py --n 10` | 16,751,614,615,998,096,965,673,730,489 | 236,388,276 | 9.0 | 14.8 (B 7.8, A+C 1.2) | 3.9 | 42 | 2 | 2 |

Notes:
- `dedekind.py`, `kreweras.py`, `a303210.py` and `sperner.py` have no `--inline` option: they
  translate with `--delete --trim` and, above the embedding limit, `--keep --binary` (streamed,
  masked, not inlined). The graph drivers and `latin_cycles.py` ran with `--inline`.
- The Sperner driver of the X5 run (`x5_sp/sperner.py` on the cluster) used `cpog-gen-norev -F`;
  for this rerun it was regenerated as `scripts/showcase/dedekind.py` of 68fc568 with the
  Sperner lemma, statement and reference values substituted (cluster copy
  `final/src/68fc568/scripts/showcase/sperner.py`; the repository's `scripts/showcase/sperner.py`
  is that file).
- X4: 115 native axioms, as on 2026-09-30; two of its terms are streamed (the labelled
  neighbourhood term `nbr_4`, 573 s of generation, dominates). X1: two terms streamed.

## R3 MC2022 funnel

**Final (2026-10-03, all 180 tasks finished; raw: `rerun_raw/r3_results.tgz`, 180 result
files):** 57 D4 timeouts, 22 generator timeouts, 4 generator kills at 64 GB, 1 Lean timeout, 96
proved. The Lean timeout is track1_083 (forward certificate 126.9 GB, LRAT 37.6 GB after
translation, count of 45 digits, Lean limit 3,600 s). Largest proved certificate: track2_061
(33.9 GB forward-only; LRAT 12.1 GB; count 594 digits; its full certificate was 44.3 GB on
2026-09-30). Largest proved count: track1_049 with 1,681 digits. The D4 row reads 123 of 180
(the "123 of 170" below counted only the finished tasks). The R4 rule set (proved with
generation under 600 s) has 82 instances; the 82nd, track1_069, is in `rerun_raw/r4_results_extra.tgz`.
The d4v2 control arrays 120888 and 120889 finished (57 and 52 completed, 2 and 5 out of
memory; not evaluated).

State at 15:05: 170 of 180 finished, 10 still running (array 120985, see below). All 180 tasks
ran on b5 nodes (AMD EPYC 7402, `-C bc5`, `-c 2`, 64 GB, at most 24 at once), 10:15 to 15:05+;
DIMACS mode, streamed, limits D4 4,000 s, generator 4,000 s (also bounding `pog_count.py` and
the translator), Lean 3,600 s. The b5 nodes are about 1.45 times slower than slurm-cpu01, so
the limits bite earlier than they would on slurm-cpu01. Order of the array: longest expected
first (the 2026-09-30 sweep's D4 timeouts, then its generator failures, then the rest).

| stage | reached | failed there |
|---|---:|---|
| D4 (4,000 s) | 123 of 170 passed | 57 timeouts (of the 66 D4 timeouts at 1,000 s on 2026-09-30, 9 now pass D4 in 1,325 to 3,977 s) |
| generation (4,000 s, 64 GB) | 92 passed | 21 timeouts, 4 killed at 64 GB (all four are D4 timeouts of 2026-09-30 that the higher D4 limit let through, D4 2,877 to 3,977 s) |
| translation | 91 passed | none failed (one running) |
| Lean (3,600 s) | 88 proved | none failed (three running) |

- Earlier generator failures now proved: track1_073 and track1_117 (killed at 32 GB on
  2026-09-30), track1_121 (timeout then); plus track1_157 (D4 timeout at 1,000 s then; now D4
  1,969.5 s, count 7). Of the 2026-09-30 sweep's 90 proved instances, 84 are proved again and
  6 were still running at 15:05; none is lost.
- Track-1 references (the organizers' log10 values, `mc2022_process.sh`): 52 proved instances
  have one, all 52 agree. Every count equals `pog_count.py`'s on the certificate.
- Medians over the 88 proved: D4 3.1 s, generation 25.0 s, translator 1.8 s, Lean total
  13.9 s (part B 2.3 s, parts A and C 0.5 s); generator peak RSS median 0.11 GB (max 9.05 GB),
  Lean process median 3.42 GB (max 21.5 GB). Lean total max 971.3 s.
- Largest so far: count 777 digits (track2_041); certificate 28.2 GB forward-only
  (track1_117: D4 118.2 s, generation 1,222.9 s at 9.5 GB, translator 368.8 s, LRAT 7.24 GB,
  Lean 934.8 s at 21.5 GB with part B 823.0 s and parts A and C 100.6 s). The 1,681-digit
  instance (track1_049) and the 44 GB (full) certificate of 2026-09-30 (track2_061) were among
  the 10 still running.
- Newly proved earlier failures, details: track1_073: D4 206.6 s, generation 977.3 s at
  7.5 GB, certificate 20.5 GB, LRAT 6.69 GB, Lean 971.3 s at 18.7 GB (part B 899.6 s); track1_121:
  generation 3,552.9 s (close to the limit) at 8.6 GB, certificate 22.5 GB, Lean 880.0 s.
- R4 rule check: R3 proved 82 instances with generation under 600 s; the 81 of R4 are all among
  them; the 82nd, track1_069 (generation 306.4 s), was added to R4 at 15:05 (job 121512, running).
- Still running at 15:05 (array 120985): track2_139, track1_083, track1_129, track1_167
  (earlier generator failures or unknown), track2_061, track2_079, track1_049, track2_111,
  track2_091, track2_183 (proved on 2026-09-30, the most expensive ones).

Per-instance table: `rerun_raw/` (key=value files of the 170 finished; the collector
`final_collect.py` prints the full table). Raw: `rerun_raw/r3_results_partial.tgz`.

## R4 comparison with CPOG's checkers

90 instances: 81 MC2022 instances and the 9 families of R1 without 14-queens and grid 16. The
MC2022 set was chosen before R3 had results (R3 runs the expensive instances first): the
instances proved by the 2026-09-30 sweep with generation under 600 s there (full generator,
32 GB). The paper's rule (proved in R3 with generation under 600 s) is to be applied once R3 has
finished; see the R3 section for the cross-check. Each job (`CPOG_CHECK=1`, `-c 2`, 32 GB for
the MC2022 array after the first 45 tasks, 64 or 48 GB for the families) ran our pipeline, then
the full certificate (unpatched `cpog-gen`, same D4 output) and both CPOG checkers, each limited
to 3,600 s. Node class: 89 of 90 on b4 nodes (Intel Xeon E5-2640 v4, 2.4 GHz), one on a b5 node
(EPYC 7402); every ratio below is taken within one job. 12:35 to 13:19.

- Our pipeline proved all 90. `cpog-lean-check` (CPOG's Lean-verified checker) succeeded on all
  90 with the same count. `cpog-check` (the C prototype) reported success on all 90 but printed
  a wrong count on 7: cub100, cub120, homer, ind14, mc2022_track1_031, mc2022_track2_027,
  mc2022_track2_035 (the known miscount on large counts, reported as
  https://github.com/rebryant/cpog/issues/3; on track2_027 its count differs
  from D4's, `pog_count.py`'s, ours and `cpog-lean-check`'s in the 31st digit).
- Medians over the 90: our verified check (part B plus parts A and C, as reported by
  `count_models`) 4.5 s, our Lean total 19.6 s (Mathlib import over NFS on b4 nodes included,
  about 10 s), `cpog-lean-check` 21.8 s, `cpog-check` 3.6 s; peak RSS: our Lean process 3.40 GB,
  `cpog-lean-check` 0.96 GB, `cpog-check` 0.09 GB; full certificate over forward certificate
  2.03 times in bytes; generation 20.7 s forward-only against 60.4 s full.
- Three boundaries, our time over `cpog-lean-check`'s (median of the per-instance ratios):
  checking prepared input (our part B plus parts A and C against the checker) 0.23, ours lower
  on all 90; translation plus theorem (translator plus Lean total against the checker) 1.28,
  ours lower on 37; pipeline after D4 (forward generation, translator and Lean against full
  generation and the checker) 0.93, ours lower on 54.
- Size dependence (full certificate bytes; medians of the ratios within each band): below
  10 MB (18 instances) Lean total over checker 86, Lean RSS over checker RSS 37; 10 to 100 MB
  (15) 3.9 and 12; 100 MB to 1 GB (43) 0.93 and 2.5; above 1 GB (14) 0.35 and 0.53. The check
  alone is 0.20 to 0.29 of the checker's time in every band. Time parity of the whole Lean run
  sits near 100 MB to 1 GB of certificate, memory parity near 1 GB.
- Largest here: track2_011 (full certificate 6.69 GB): ours check 167.9 s, Lean 184.7 s at
  6.8 GB; `cpog-lean-check` 519.9 s at 24.2 GB; `cpog-check` 99.8 s at 4.1 GB.

Per instance (sorted by full certificate size; "gen s" forward-only / full; "count" ok or WRONG
against D4):

| instance | fwd cert MB | full cert MB | gen s (fwd / full) | translator s | our check s (B+A+C) | Lean total s | Lean GB | cpog-check s | GB | count | cpog-lean-check s | GB | count |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|---:|---|
| mc2022_track1_015 | 0.0 | 0.0 | 0.1 / 0.0 | 0.1 | 0.0 | 10.4 | 3.32 | 0.0 | 0.01 | ok | 0.1 | 0.09 | ok |
| mc2022_track1_007 | 0.1 | 0.1 | 0.1 / 0.0 | 0.1 | 0.0 | 12.1 | 3.32 | 0.0 | 0.01 | ok | 0.1 | 0.09 | ok |
| mc2022_track1_009 | 0.1 | 0.3 | 0.1 / 0.0 | 0.1 | 0.0 | 54.3 | 3.24 | 0.0 | 0.01 | ok | 0.8 | 0.08 | ok |
| mc2022_track1_013 | 0.2 | 0.5 | 0.1 / 0.0 | 0.1 | 0.0 | 13.3 | 3.32 | 0.0 | 0.01 | ok | 0.1 | 0.09 | ok |
| mc2022_track2_047 | 0.2 | 0.5 | 0.1 / 0.0 | 0.1 | 0.0 | 10.9 | 3.32 | 0.0 | 0.01 | ok | 0.1 | 0.09 | ok |
| mc2022_track1_033 | 0.3 | 0.7 | 0.1 / 0.1 | 0.1 | 0.0 | 10.5 | 3.32 | 0.0 | 0.01 | ok | 0.1 | 0.09 | ok |
| mc2022_track2_021 | 0.3 | 0.7 | 0.1 / 0.1 | 0.1 | 0.0 | 13.5 | 3.32 | 0.0 | 0.01 | ok | 0.1 | 0.09 | ok |
| mc2022_track2_067 | 0.3 | 0.7 | 0.1 / 0.1 | 0.1 | 0.0 | 11.2 | 3.32 | 0.0 | 0.01 | ok | 0.1 | 0.09 | ok |
| mc2022_track2_015 | 0.3 | 0.7 | 0.1 / 0.1 | 0.1 | 0.0 | 12.8 | 3.32 | 0.0 | 0.01 | ok | 0.1 | 0.09 | ok |
| mc2022_track2_045 | 0.4 | 0.8 | 0.1 / 0.1 | 0.1 | 0.0 | 11.5 | 3.32 | 0.0 | 0.01 | ok | 0.1 | 0.09 | ok |
| mc2022_track1_035 | 0.5 | 1.2 | 0.2 / 0.1 | 0.1 | 0.0 | 11.5 | 3.32 | 0.0 | 0.01 | ok | 0.2 | 0.09 | ok |
| mc2022_track1_039 | 0.6 | 1.4 | 0.2 / 0.1 | 0.1 | 0.0 | 10.9 | 3.32 | 0.0 | 0.01 | ok | 0.2 | 0.09 | ok |
| mc2022_track2_017 | 0.6 | 1.5 | 0.2 / 0.1 | 0.1 | 0.0 | 12.0 | 3.32 | 0.0 | 0.01 | ok | 0.2 | 0.09 | ok |
| mc2022_track1_017 | 0.6 | 1.5 | 0.2 / 0.1 | 0.1 | 0.0 | 11.1 | 3.32 | 0.0 | 0.01 | ok | 0.2 | 0.09 | ok |
| mc2022_track1_047 | 1.9 | 5.5 | 7.1 / 7.1 | 0.2 | 0.1 | 11.7 | 3.32 | 0.1 | 0.01 | ok | 0.4 | 0.11 | ok |
| mc2022_track1_021 | 2.9 | 5.8 | 0.4 / 0.8 | 0.2 | 0.2 | 12.8 | 3.33 | 0.1 | 0.01 | ok | 0.5 | 0.12 | ok |
| mc2022_track1_023 | 3.0 | 6.0 | 2.8 / 36.8 | 0.2 | 0.2 | 14.8 | 3.32 | 0.1 | 0.01 | ok | 0.6 | 0.11 | ok |
| mc2022_track1_057 | 1.5 | 7.5 | 10.6 / 10.9 | 0.2 | 0.2 | 12.9 | 3.34 | 0.1 | 0.01 | ok | 0.6 | 0.12 | ok |
| mc2022_track1_043 | 3.4 | 11.0 | 3.3 / 138.4 | 0.2 | 0.2 | 12.0 | 3.32 | 0.2 | 0.01 | ok | 1.0 | 0.12 | ok |
| mc2022_track1_079 | 6.9 | 11.2 | 1.7 / 2.9 | 0.2 | 0.3 | 12.3 | 3.33 | 0.2 | 0.01 | ok | 1.0 | 0.14 | ok |
| mc2022_track2_009 | 6.7 | 12.8 | 0.7 / 0.9 | 0.3 | 0.3 | 11.4 | 3.33 | 0.2 | 0.01 | ok | 1.1 | 0.15 | ok |
| mc2022_track1_011 | 13.3 | 25.1 | 1.1 / 1.5 | 0.4 | 0.6 | 12.5 | 3.35 | 0.4 | 0.02 | ok | 2.1 | 0.21 | ok |
| mc2022_track2_013 | 15.0 | 30.3 | 1.4 / 1.9 | 0.5 | 0.7 | 11.0 | 3.35 | 0.5 | 0.03 | ok | 2.4 | 0.24 | ok |
| mc2022_track2_007 | 16.0 | 32.1 | 1.6 / 2.1 | 0.5 | 0.7 | 12.0 | 3.34 | 0.5 | 0.03 | ok | 2.5 | 0.23 | ok |
| mc2022_track1_087 | 29.7 | 42.1 | 8.9 / 13.9 | 0.5 | 0.8 | 14.5 | 3.34 | 0.6 | 0.03 | ok | 3.4 | 0.24 | ok |
| mc2022_track1_005 | 28.2 | 52.0 | 19.4 / 23.0 | 0.8 | 1.4 | 17.5 | 3.34 | 0.8 | 0.01 | ok | 4.5 | 0.27 | ok |
| mc2022_track1_077 | 36.8 | 67.6 | 15.6 / 85.1 | 1.1 | 1.9 | 17.0 | 3.32 | 1.2 | 0.01 | ok | 5.3 | 0.33 | ok |
| mc2022_track2_081 | 35.6 | 68.4 | 11.3 / 134.8 | 0.8 | 4.5 | 10.1 | 3.40 | 4.3 | 0.04 | ok | 68.3 | 0.54 | ok |
| mc2022_track1_037 | 37.2 | 70.4 | 2.8 / 8.4 | 0.9 | 1.9 | 13.4 | 3.39 | 1.0 | 0.05 | ok | 5.4 | 0.40 | ok |
| mc2022_track1_149 | 35.0 | 72.3 | 5.1 / 154.0 | 1.2 | 5.5 | 22.4 | 3.53 | 1.1 | 0.04 | ok | 32.8 | 0.57 | ok |
| mc2022_track2_149 | 38.8 | 77.5 | 5.6 / 160.7 | 1.0 | 6.0 | 21.9 | 3.51 | 1.2 | 0.05 | ok | 34.8 | 0.60 | ok |
| mc2022_track2_023 | 64.2 | 85.3 | 14.3 / 15.8 | 1.0 | 1.8 | 17.1 | 3.35 | 1.1 | 0.05 | ok | 6.0 | 0.38 | ok |
| mc2022_track1_051 | 48.4 | 92.8 | 3.6 / 13.2 | 1.1 | 2.5 | 13.7 | 3.41 | 1.4 | 0.06 | ok | 7.5 | 0.51 | ok |
| mc2022_track1_081 | 40.1 | 104.2 | 56.1 / 58.3 | 1.1 | 1.9 | 17.3 | 3.34 | 1.2 | 0.01 | ok | 7.1 | 0.41 | ok |
| mc2022_track2_019 | 37.1 | 108.7 | 10.5 / 13.9 | 0.8 | 1.1 | 13.8 | 3.38 | 1.5 | 0.05 | ok | 7.9 | 0.46 | ok |
| mc2022_track2_089 | 64.8 | 119.6 | 293.4 / 333.2 | 1.4 | 3.4 | 19.0 | 3.39 | 3.0 | 0.04 | ok | 30.1 | 0.57 | ok |
| mc2022_track2_029 | 38.8 | 139.6 | 11.6 / 20.8 | 0.8 | 1.4 | 17.2 | 3.40 | 2.3 | 0.09 | ok | 10.8 | 0.70 | ok |
| mc2022_track1_091 | 82.9 | 146.9 | 38.4 / 39.5 | 2.6 | 4.6 | 19.7 | 3.33 | 2.7 | 0.02 | ok | 11.7 | 0.61 | ok |
| homer | 32.7 | 152.1 | 11.6 / 22.0 | 0.8 | 1.6 | 20.0 | 3.54 | 2.1 | 0.10 | WRONG | 12.6 | 0.82 | ok |
| hq6 | 68.1 | 155.6 | 6.2 / 11.5 | 1.6 | 2.8 | 17.9 | 3.64 | 2.6 | 0.16 | ok | 13.7 | 1.01 | ok |
| mc2022_track1_109 | 91.2 | 159.8 | 82.1 / 107.8 | 2.2 | 4.8 | 15.6 | 3.34 | 2.8 | 0.05 | ok | 13.6 | 0.62 | ok |
| mc2022_track2_031 | 58.3 | 165.2 | 13.2 / 25.1 | 1.2 | 1.8 | 17.7 | 3.42 | 2.8 | 0.11 | ok | 13.1 | 0.79 | ok |
| mc2022_track2_051 | 81.6 | 182.7 | 11.9 / 18.5 | 1.9 | 3.4 | 19.5 | 3.55 | 2.9 | 0.14 | ok | 15.0 | 0.93 | ok |
| mc2022_track1_025 | 55.2 | 183.5 | 15.3 / 27.6 | 1.2 | 2.1 | 17.7 | 3.43 | 2.5 | 0.10 | ok | 14.2 | 0.88 | ok |
| mc2022_track1_045 | 101.0 | 192.9 | 12.0 / 15.6 | 2.0 | 3.0 | 15.1 | 3.46 | 2.9 | 0.12 | ok | 16.2 | 0.90 | ok |
| mc2022_track1_019 | 110.8 | 208.2 | 12.2 / 14.9 | 2.5 | 5.5 | 17.9 | 3.38 | 2.8 | 0.11 | ok | 14.7 | 0.84 | ok |
| mc2022_track2_039 | 85.7 | 260.3 | 20.2 / 36.5 | 1.6 | 2.9 | 18.8 | 3.46 | 4.2 | 0.17 | ok | 20.0 | 1.17 | ok |
| mc2022_track2_027 | 104.3 | 294.9 | 21.1 / 40.8 | 2.0 | 3.6 | 18.8 | 3.49 | 4.8 | 0.18 | WRONG | 22.6 | 1.31 | ok |
| mc2022_track2_093 | 232.2 | 309.6 | 44.1 / 60.8 | 3.1 | 6.3 | 21.1 | 3.41 | 4.1 | 0.18 | ok | 20.9 | 1.14 | ok |
| mc2022_track1_097 | 163.9 | 334.2 | 49.8 / 52.1 | 4.8 | 7.0 | 22.3 | 3.35 | 4.7 | 0.02 | ok | 19.9 | 1.15 | ok |
| cub100 | 117.8 | 334.3 | 18.4 / 27.2 | 2.7 | 4.8 | 20.5 | 3.94 | 5.1 | 0.32 | WRONG | 29.7 | 2.21 | ok |
| mc2022_track1_055 | 220.3 | 376.9 | 14.8 / 70.0 | 4.5 | 11.5 | 27.4 | 3.59 | 5.5 | 0.21 | ok | 29.2 | 1.46 | ok |
| mc2022_track1_101 | 22.4 | 379.9 | 191.8 / 306.2 | 0.6 | 2.5 | 18.8 | 3.38 | 5.2 | 0.03 | ok | 24.6 | 0.99 | ok |
| mc2022_track2_035 | 119.5 | 385.2 | 32.3 / 69.1 | 2.4 | 4.7 | 20.9 | 3.55 | 7.0 | 0.24 | WRONG | 35.7 | 1.65 | ok |
| mc2022_track2_025 | 277.9 | 391.7 | 50.1 / 61.2 | 4.0 | 9.3 | 24.7 | 3.41 | 5.1 | 0.21 | ok | 27.0 | 1.31 | ok |
| mc2022_track1_095 | 202.1 | 393.4 | 57.7 / 60.0 | 6.1 | 9.0 | 23.6 | 3.35 | 5.5 | 0.03 | ok | 23.9 | 1.33 | ok |
| mc2022_track1_029 | 125.6 | 409.6 | 33.4 / 62.6 | 2.4 | 4.4 | 63.7 | 3.47 | 5.5 | 0.20 | ok | 33.3 | 1.74 | ok |
| mc2022_track2_095 | 323.6 | 424.6 | 44.6 / 463.5 | 4.1 | 20.7 | 38.8 | 3.57 | 6.5 | 0.24 | ok | 315.0 | 2.32 | ok |
| mc2022_track2_043 | 157.6 | 435.5 | 33.9 / 65.0 | 2.8 | 4.9 | 62.8 | 3.47 | 8.1 | 0.26 | ok | 35.1 | 1.73 | ok |
| mc2022_track1_031 | 323.9 | 487.4 | 45.5 / 63.2 | 5.3 | 12.4 | 68.0 | 3.44 | 6.5 | 0.27 | WRONG | 37.8 | 1.63 | ok |
| mc2022_track1_065 | 244.4 | 527.7 | 37.0 / 133.7 | 4.2 | 10.3 | 26.0 | 3.54 | 6.8 | 0.19 | ok | 36.1 | 1.43 | ok |
| mc2022_track2_133 | 296.8 | 572.8 | 693.2 / 917.6 | 6.2 | 18.7 | 35.0 | 3.54 | 10.5 | 0.20 | ok | 147.9 | 1.96 | ok |
| mc2022_track2_033 | 185.8 | 599.3 | 32.9 / 55.2 | 3.7 | 7.5 | 22.9 | 3.72 | 8.7 | 0.34 | ok | 49.6 | 2.28 | ok |
| mc2022_track2_127 | 349.0 | 620.2 | 154.8 / 156.5 | 9.6 | 20.9 | 35.4 | 3.34 | 11.6 | 0.09 | ok | 49.8 | 1.95 | ok |
| mc2022_track1_135 | 349.2 | 650.7 | 308.5 / 322.1 | 7.9 | 15.4 | 30.9 | 3.37 | 9.3 | 0.06 | ok | 48.3 | 1.97 | ok |
| mc2022_track2_053 | 189.5 | 736.7 | 70.9 / 137.2 | 3.8 | 8.3 | 19.7 | 3.67 | 12.7 | 0.43 | ok | 67.5 | 2.99 | ok |
| mc2022_track2_101 | 497.9 | 740.3 | 450.9 / 461.1 | 4.4 | 4.9 | 66.8 | 3.71 | 11.1 | 0.42 | ok | 63.2 | 2.95 | ok |
| mc2022_track2_041 | 631.1 | 775.1 | 115.1 / 126.6 | 7.9 | 17.4 | 33.5 | 3.42 | 9.8 | 0.43 | ok | 52.2 | 2.31 | ok |
| mc2022_track1_059 | 415.0 | 877.3 | 29.8 / 186.3 | 7.4 | 18.6 | 34.6 | 3.73 | 11.5 | 0.33 | ok | 58.6 | 2.38 | ok |
| mc2022_track1_171 | 512.0 | 884.8 | 282.2 / 469.9 | 6.5 | 14.7 | 30.0 | 3.61 | 11.8 | 0.38 | ok | 61.2 | 2.70 | ok |
| q12 | 406.3 | 913.1 | 103.9 / 119.0 | 7.0 | 9.8 | 63.8 | 3.45 | 12.0 | 0.37 | ok | 64.5 | 2.99 | ok |
| dom12 | 500.1 | 931.5 | 437.9 / 430.2 | 9.0 | 17.9 | 33.4 | 3.58 | 12.4 | 0.40 | ok | 71.7 | 3.20 | ok |
| mc2022_track1_093 | 679.7 | 943.1 | 299.0 / 318.6 | 6.5 | 3.6 | 19.1 | 3.60 | 14.9 | 0.58 | ok | 78.4 | 3.75 | ok |
| mc2022_track1_063 | 443.6 | 948.6 | 66.5 / 205.6 | 8.6 | 22.6 | 38.6 | 3.59 | 15.6 | 0.35 | ok | 76.5 | 2.89 | ok |
| mc2022_track2_049 | 659.0 | 953.4 | 50.4 / 91.8 | 11.1 | 23.3 | 40.7 | 3.69 | 13.0 | 0.52 | ok | 63.8 | 2.88 | ok |
| mc2022_track1_153 | 542.1 | 961.6 | 537.8 / 521.9 | 16.0 | 29.9 | 44.9 | 3.34 | 17.4 | 0.14 | ok | 70.8 | 3.28 | ok |
| mc2022_track1_041 | 501.2 | 1,080.4 | 99.0 / 335.1 | 7.8 | 23.5 | 36.9 | 3.79 | 14.3 | 0.47 | ok | 108.9 | 3.58 | ok |
| ind14 | 327.9 | 1,099.1 | 57.7 / 110.3 | 7.3 | 14.9 | 30.5 | 5.02 | 16.3 | 0.88 | WRONG | 92.8 | 5.98 | ok |
| mc2022_track1_027 | 883.8 | 1,237.5 | 84.4 / 112.2 | 13.5 | 33.2 | 45.9 | 3.56 | 15.9 | 0.59 | ok | 85.7 | 3.49 | ok |
| mc2022_track2_005 | 907.0 | 1,789.4 | 71.8 / 106.6 | 20.1 | 44.2 | 60.7 | 4.61 | 27.6 | 1.19 | ok | 142.7 | 7.48 | ok |
| mc2022_track1_141 | 1,077.0 | 1,913.9 | 336.8 / 351.5 | 20.3 | 45.8 | 71.3 | 3.45 | 27.5 | 0.28 | ok | 136.5 | 5.61 | ok |
| mc2022_track1_145 | 1,075.7 | 2,045.7 | 267.8 / 278.2 | 31.2 | 46.9 | 63.3 | 3.37 | 30.1 | 0.13 | ok | 121.7 | 6.47 | ok |
| mc2022_track1_133 | 1,324.3 | 2,566.5 | 549.0 / 557.7 | 41.9 | 63.4 | 82.0 | 3.37 | 45.2 | 0.08 | ok | 181.8 | 7.14 | ok |
| mc2022_track2_087 | 1,364.6 | 2,570.9 | 136.9 / 328.4 | 23.1 | 55.5 | 71.6 | 4.08 | 34.9 | 0.88 | ok | 184.5 | 7.57 | ok |
| cub120 | 1,076.4 | 3,010.6 | 170.9 / 239.1 | 23.1 | 41.2 | 53.7 | 8.24 | 45.4 | 2.54 | WRONG | 250.8 | 16.90 | ok |
| games120 | 860.6 | 3,560.9 | 154.3 / 355.9 | 20.1 | 43.3 | 57.3 | 7.54 | 53.0 | 1.95 | ok | 268.5 | 14.20 | ok |
| mc2022_track2_103 | 3,032.6 | 3,974.0 | 276.4 / 344.8 | 36.2 | 50.8 | 66.8 | 4.08 | 55.4 | 2.30 | ok | 271.8 | 12.68 | ok |
| mc2022_track1_103 | 5,028.2 | 5,620.8 | 338.9 / 383.7 | 47.4 | 48.4 | 60.6 | 3.72 | 73.1 | 3.43 | ok | 387.9 | 16.67 | ok |
| q13 | 2,845.8 | 6,124.6 | 732.8 / 1028.2 | 56.1 | 80.2 | 96.9 | 4.47 | 104.0 | 2.51 | ok | 547.9 | 19.01 | ok |
| mc2022_track2_011 | 3,465.1 | 6,692.8 | 297.4 / 452.7 | 76.7 | 167.9 | 184.7 | 6.79 | 99.8 | 4.07 | ok | 519.9 | 24.18 | ok |

Raw results: `rerun_raw/r4_results.tgz` (`results/cpog/<instance>/{e2e_stream.txt,cpog_baseline.txt}`).
For 6 instances with counts of more than about 300 digits the part times are cut from `cmd_info`
(400 bytes); their check time is the `count_models` stamp difference (on q13 the two agree to
0.2 percent); `e2e.sbatch` now writes `part_b_ms` and `part_ac_ms` separately.

## R5 ablation of part B

Done in full: 7 instances by 4 variants, one repetition, on the certificates that
`improve_gen.sbatch` had stored for the before/after measurements of the previous night
(`cpog-gen-norev -F` certificates on slurm-cpu01's scratch; the same certificates for all four
variants), translator and Lean of 68fc568 (`tools_final`,
`lean_final`), theorem file in the DIMACS form (`theorem_lean.py dimacs … stream`, statement over
`parseDimacs` of the CNF), slurm-cpu01, 11:13 to 12:16, node load 70 to 83 on 128 threads.
Driver: `scripts/cluster/improve_check.sbatch` (variants `r5_text`, `r5_trimbin`, `r5_keep`,
`r5_inline`). "additions" is the number of LRAT additions written (all, after trimming, or
after inlining); "initial clauses" is what part B loads (all, or the keep mask's ones of all).

| instance | translator options | translator s | translator MB | LRAT GB | additions | initial clauses loaded | part B s | parts A, C s | Lean total s | Lean GB |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 13-queens | `--delete`, text | 22.0 | 324 | 3.09 | 16,298,260 | all | 148.2 | 4.6 | 158.6 | 6.0 |
| | `--trim --binary` | 21.2 | 231 | 0.89 | 9,663,308 | all | 80.9 | 4.6 | 91.7 | 5.9 |
| | `--keep --binary` | 21.6 | 232 | 0.87 | 9,663,308 | 1,096,010 of 4,631,044 | 71.3 | 4.7 | 82.2 | 4.4 |
| | `--keep --inline --binary` | 29.6 | 310 | 0.49 | 4,547,249 | 1,096,010 of 4,631,044 | 41.2 | 4.7 | 49.8 | 4.4 |
| 14-queens | `--delete`, text | 137.1 | 1,580 | 19.62 | 88,974,864 | all | 1,000.5 | 27.1 | 1,032.1 | 17.1 |
| | `--trim --binary` | 129.2 | 1,076 | 5.51 | 51,750,015 | all | 519.9 | 27.3 | 553.5 | 17.1 |
| | `--keep --binary` | 128.1 | 1,075 | 5.44 | 51,750,015 | 5,419,870 of 23,767,256 | 438.5 | 27.6 | 477.3 | 9.2 |
| | `--keep --inline --binary` | 179.5 | 1,206 | 3.12 | 25,160,671 | 5,419,870 of 23,767,256 | 256.7 | 27.5 | 294.8 | 9.2 |
| grid 16 | `--delete`, text | 30.9 | 1,356 | 3.96 | 37,974,284 | all | 201.3 | 60.9 | 270.1 | 42.1 |
| | `--trim --binary` | 33.5 | 1,350 | 1.72 | 37,974,284 | all | 284.9 | 60.2 | 350.6 | 42.1 |
| | `--keep --binary` | 32.5 | 1,354 | 1.51 | 37,974,284 | 25,837,291 of 77,950,926 | 118.0 | 57.4 | 183.3 | 20.8 |
| | `--keep --inline --binary` | 44.5 | 1,782 | 0.53 | 7,715,690 | 25,837,291 of 77,950,926 | 62.9 | 57.5 | 128.1 | 20.8 |
| Sperner 7 | `--delete`, text | 57.4 | 1,249 | 7.52 | 32,840,428 | all | 424.0 | 121.0 | 552.4 | 36.3 |
| | `--trim --binary` | 70.0 | 1,247 | 3.42 | 32,840,428 | all | 454.1 | 126.2 | 588.2 | 35.9 |
| | `--keep --binary` | 68.4 | 1,246 | 3.25 | 32,840,428 | 22,926,713 of 65,797,977 | 292.1 | 124.1 | 423.9 | 18.1 |
| | `--keep --inline --binary` | 79.4 | 1,615 | 0.94 | 7,229,406 | 22,926,713 of 65,797,977 | 99.8 | 122.8 | 231.9 | 18.1 |
| MC2022 track2_011 | `--delete`, text | 24.5 | 587 | 3.75 | 22,774,054 | all | 145.8 | 11.3 | 163.7 | 11.4 |
| | `--trim --binary` | 28.9 | 585 | 1.69 | 22,773,434 | all | 121.4 | 11.8 | 137.5 | 11.4 |
| | `--keep --binary` | 28.8 | 586 | 1.64 | 22,773,434 | 5,144,702 of 15,562,631 | 103.7 | 11.4 | 119.3 | 6.7 |
| | `--keep --inline --binary` | 39.6 | 682 | 1.15 | 16,051,266 | 5,144,702 of 15,562,631 | 91.5 | 11.1 | 108.9 | 6.7 |
| MC2022 track2_087 | `--delete`, text | 8.6 | 169 | 1.41 | 4,480,863 | all | 62.7 | 7.7 | 76.7 | 5.0 |
| | `--trim --binary` | 10.1 | 170 | 0.59 | 3,819,162 | all | 45.8 | 6.9 | 59.1 | 5.0 |
| | `--keep --binary` | 9.8 | 167 | 0.57 | 3,819,162 | 1,189,921 of 3,363,015 | 41.8 | 7.5 | 53.2 | 4.0 |
| | `--keep --inline --binary` | 14.0 | 161 | 0.43 | 2,470,697 | 1,189,921 of 3,363,015 | 32.9 | 7.7 | 46.9 | 4.0 |
| MC2022 track2_095 | `--delete`, text | 2.1 | 50 | 0.33 | 649,599 | all | 18.3 | 6.0 | 30.5 | 3.7 |
| | `--trim --binary` | 2.1 | 64 | 0.11 | 458,754 | all | 12.0 | 5.9 | 23.8 | 3.7 |
| | `--keep --binary` | 2.1 | 65 | 0.11 | 458,754 | 114,002 of 625,522 | 8.6 | 5.7 | 20.3 | 3.5 |
| | `--keep --inline --binary` | 2.4 | 70 | 0.08 | 317,441 | 114,002 of 625,522 | 7.4 | 6.0 | 22.5 | 3.5 |

- Part B from text to the full default (`--keep --inline --binary`): 3.6x (13-queens), 3.9x
  (14-queens), 3.2x (grid 16), 4.2x (Sperner 7), 1.6x (track2_011), 1.9x (track2_087), 2.5x
  (track2_095). Lean memory halves through the mask (14-queens 17.1 to 9.2 GB, grid 16 42.1 to
  20.8 GB, Sperner 7 36.3 to 18.1 GB); inlining does not change it.
- Trimming and binary without the mask is slower than text on grid 16 (part B 284.9 against
  201.3 s) and Sperner 7 (454.1 against 424.0 s), the two instances where trimming removes no
  addition; the cause is not established (one repetition, node load 70 to 83). The earlier
  before/after runs showed the same direction on grid 16 (variant `new_nomask`, not in
  this record).
- Inlining costs translator time (q14 128 to 180 s) and memory (up to +430 MB, grid 16).
- Parts A and C do not depend on the translator options (as expected).

## Not done, or done differently

- R3: 10 of 180 instances were still running when this summary was written (15:05); their
  results come with the final collection (`results/funnel/`, array 120985).
- R4: track1_069 (the 82nd instance of the rule) is running (job 121512).
- The 1 TB run for the true memory peak of CPOG's verified checker (not run).
- Triangle-free graphs on 11 vertices (not part of this rerun).
- X5 drivers without `--inline` (dedekind, kreweras, a303210, sperner): their certificates were
  translated without inlining; the families, X1, X3, X4, the funnel and R4 used inlining.
- `lean_commit` in the e2e results reads `unknown`: `lean_final` is a `git archive` export, not a
  checkout; its file `OVN_SOURCE` and this summary record the commit.
- Node classes: R1, R2 and R5 on slurm-cpu01 (EPYC 9554P); R3 on b5 (EPYC 7402); R4 on b4
  (Xeon E5-2640 v4, 89 instances) and b5 (1).
