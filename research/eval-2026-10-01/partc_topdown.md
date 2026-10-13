# Part C: top-down short-circuit baseline, 2026-10-01

## Protocol (fixed 2026-10-01 before any implementation or timing)

Methods, all compiled natively into one executable (same compiler and runtime):

- M1 per-clause bottom-up: `checkRev` (verified, `McCert/Rev.lean`), one pass over all nodes
  per clause, skipping nodes whose support misses vars(C). Needs the part A supports; part A
  runs in the same process but outside M1's clock.
- M2 top-down short-circuit, plain: per clause a depth-first evaluation from the root with an
  explicit stack; per-clause memo and literal table reset by stamps (no per-clause clearing);
  a product is killed at its first killed argument (input literals tried first), a sum only if
  both arguments are killed; tautological clauses are skipped.
- M3 as M2, plus a 63-bit hashed support signature per node (bit v mod 63 for each variable v
  of the support, computed once in O(N + edges), inside M3's clock); a node whose signature
  misses the clause's signature is untouched by the clause, hence satisfiable under ¬C
  (negation-free POG), and is skipped.
- M4 bit-parallel with table reuse: `checkRevKillFast` (verified, one occurrence table reused across
  the 63-clause batches; the current checker).
- M2 and M3 are unverified (`partial def`) in `McCert/RevTD.lean`, not imported by `Check.lean`.

Rules:

- P1 Correctness gate on the Mac before any timing: the regression pairs of `lean/test/data`
  with their cross pairs, the adversarial suite and a random POG/CNF suite give identical
  verdicts under all four methods.
- P2 Same POG and CNF per instance (current pipeline route: D4, `cpog-gen-norev -F`, native
  `cpog2lrat`). Each check in its own process, 1800 s timeout per check, slurm-cpu01
  (`-C genoa -c 2`); the clock covers the check only (parsing and part A excluded). Fixed
  order M4, M3, M2, M1. Checks under 60 s run 3 times, the median is reported.
- P3 Per instance: time and verdict of each method; for M2 and M3 the nodes evaluated (total,
  mean and max per clause), against N·m (M1's sweep) and N·⌈m/63⌉ (M4's passes).
- P4 Decision rule: the top-down check enters the checker (verified, as replacement or
  per-instance hybrid) only if M2 or M3 is at least 2x faster than M4 on at least one
  canonical-table instance whose M4 part C takes more than 10 s. Otherwise it stays a
  baseline for the evaluation.

Instances: the set of the table-reuse measurement of 2026-09-30 (mc2022_track2_095, track2_081,
track2_089, track1_149, track1_171, track1_063, grid14, queens13) plus the theorem table of
2026-09-29 (domino12, queens12, queens14, grid16, Q_6, random cubic 100 and 120, games120, homer).

## Implementation

- `lean/McCert/RevTD.lean` (new, unverified, not imported by `McCert.lean` or `Check.lean`):
  `flattenPog` turns the node table into a flat argument array (input literals first, edges
  only to earlier nodes, else `none`) and, for M3, the signatures; `tdLoop` is the depth-first
  evaluation (`partial def`, tail-recursive, explicit stack); `clauseTD` marks the clause's
  literals with its stamp (out-of-range literals ignored, as M4 does) and starts at the root;
  `checkRevTD useSig` runs over the clauses and returns the verdict, the evaluated nodes summed
  over the clauses and their maximum. The generated C (`.lake/build/ir/McCert/RevTD.c`) updates
  memo, positions and stack with `lean_array_set` / `lean_array_push` without an increment
  before them, and the per-clause loop hands the arrays over unshared (no copy per clause).
- `lean/PartcMain.lean`: modes `m1`, `m2`, `m3`, `m4` (one method) and `all` (part A, M4, M3,
  M2, M1, verdict comparison) beside the table-reuse modes (`both`, `old`, `new`); lines are flushed, so a killed run keeps
  its output; `partc-load` gives the load time. Mac `lakefile.toml`: new `lean_exe`
  `mccert-partc`.
- Cluster: private copy `/home1/szeider/mccert/lean_partc` (the copy of the table-reuse measurement; `Rev.lean`,
  `RevFast.lean`, `Pog.lean`, `Spec.lean` identical to the Mac by md5), `RevTD.lean` and
  `PartcMain.lean` copied in, `lake build mccert-partc` on slurm-login01. Jobs:
  `scripts/cluster/td_pog.sbatch` (phase 1, POG per instance to `td/pog/`) and
  `scripts/cluster/td_time.sbatch` (phase 2, the four methods), in `/home1/szeider/mccert/td/`.
  The cluster `cpog2lrat` lacks the B1/B2 fix, which only concerns valid formulas and empty
  hint lists (byte-identical output otherwise), so it gives the same POGs here.

## Correctness gate (P1)

Mac, `mccert-partc --list suite.list all` (part A, then M4, M3, M2, M1 per case). Suite built
by a scratch script: D4, `cpog-gen-norev -F` and native `cpog2lrat` on 13 family CNFs from
the repository generators (queens 6 to 8, domino 4x4, 4x5, 6x6, 8x8, grid 6 and 8, hypercubes
Q_4 and Q_5, random cubic 60 and 80), each with up to 8 CNF variants against its POG (the
formula, 3 extra random clauses, a random clause inserted after position 63, a random subset,
a permutation, inserted tautologies and repeated literals, every clause weakened by a literal,
one clause strengthened by dropping a literal); all 156 cross pairs of the family POGs and
CNFs; random CNFs (V 4 to 60, up to 4V + 20 clauses of width 1 to 4, 600 seeds, satisfiable
ones certified) with the same variants plus the previous seed's CNF; the 9 adversarial
certificates that translate (a5, a5b, a9 give no POG, as in the table-reuse measurement).

- 3183 cases, identical verdicts under all four methods: 2007 accept, 1176 reject. Part A
  rejects a4 and a14 (overlapping products); there M1 does not run and M2, M3, M4 agree.
- Positive control (on a first suite of 3151 cases, same generator): M2/M3 with the memo
  stamp ignored (`mj > 0` instead of `mj / 2 == s`) differ on 745 cases (false accepts); M3
  with a clause signature shifted by one bit differs on 1789 cases. Source restored and rebuilt
  afterwards (`diff` against a saved copy).
- M4 (verified `clearClauseOcc`, `set!`) prints an index panic for CNF literals beyond the
  POG's V (cross pairs only); the write is a no-op and the verdict is unaffected. In the
  pipeline the POG comes from the same CNF, so this does not occur.
- Pitfall met on the way: without `tools/bin` first on PATH, cpog-gen calls Homebrew's
  cadical and fails justification (exit 10, e.g. domino 8x8), a known pitfall of the local build. The
  first suite therefore lacked such instances; the final suite has them.

## Timing (P2, P3)

slurm-cpu01 (EPYC 9554P), `-C genoa -c 2`, 2026-10-01 evening; the node was shared with
another user's jobs (dedicated cores, shared memory bandwidth). Phase 1 jobs 117440 to 117456
(POGs from D4 and `cpog-gen-norev -F`; every count equals the known value), phase 2 jobs
117531, 117534, 117535, 117543 to 117556; one executable (md5 `349b0b71…`) for all. Raw
results `/home1/szeider/mccert/td/results/`, table by `td/td_collect.sh`, copy in
`partc_topdown_table.tsv`. POGs and CNFs (1.1 GB) archived to
`/home1archive/szeider/projects/mccert/td_pog_2026-10-01` (symlink `td/pog`). Times in seconds, median of 3 runs below 60 s; M1 over 1800 s
counts as timeout (queens14 finished at 2139 s, track2_095 killed at 2400 s). All verdicts
ACCEPT. Spread of the 3 runs mostly within 5 percent (largest: M4 on track2_081, 1.06 to
1.57 s). Nodes: evaluated nodes of M3 summed over the clauses (M2 visits 0 to 89 percent more).

| instance | V | m | N | E | M4 | M3 | M2 | M1 | best top-down / M4 | M3 nodes per clause | M3 nodes / (N·m) | M3 nodes / (N·⌈m/63⌉) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| mc2022_track2_095 | 71,634 | 120,524 | 17,828 | 487,169 | 13.97 | 46.06 | 46.83 | > 1800 | 3.3x | 200 | 1.1% | 0.7 |
| mc2022_track2_081 | 33,667 | 56,116 | 1,231 | 315,176 | 1.35 | 22.79 | 22.86 | 62.40 | 16.9x | 58 | 4.7% | 3.0 |
| mc2022_track2_089 | 23,527 | 43,222 | 3,968 | 184,017 | 0.60 | 8.57 | 8.65 | 94.64 | 14.3x | 74 | 1.9% | 1.2 |
| mc2022_track1_149 | 17,849 | 44,425 | 65,059 | 376,117 | 5.86 | 10.40 | 15.08 | 1306.04 | 1.8x | 2,706 | 4.2% | 2.6 |
| mc2022_track1_171 | 2,303 | 20,963 | 82,925 | 1,157,724 | 7.18 | 7.52 | 7.21 | 346.51 | 1.0x | 1,132 | 1.4% | 0.9 |
| mc2022_track1_063 | 729 | 10,546 | 70,594 | 1,350,115 | 4.23 | 5.22 | 5.09 | 171.37 | 1.2x | 2,359 | 3.3% | 2.1 |
| grid14 | 196 | 364 | 2,162,104 | 5,898,593 | 1.08 | 9.29 | 9.50 | 123.07 | 8.6x | 250,268 | 11.6% | 7.0 |
| queens13 | 169 | 3,341 | 416,316 | 4,211,386 | 4.83 | 9.92 | 9.45 | 375.64 | 2.0x | 31,593 | 7.6% | 4.7 |
| domino12 | 264 | 868 | 183,393 | 1,024,983 | 0.36 | 2.94 | 2.73 | 30.72 | 7.6x | 44,933 | 24.5% | 15.2 |
| queens12 | 144 | 2,608 | 82,771 | 778,681 | 0.69 | 1.54 | 1.55 | 56.06 | 2.2x | 7,572 | 9.1% | 5.7 |
| queens14 | 196 | 4,200 | 2,080,342 | 21,682,713 | 30.32 | 86.29 | 82.08 | > 1800 | 2.7x | 134,051 | 6.4% | 4.0 |
| grid16 | 256 | 480 | 20,826,473 | 57,123,972 | 14.61 | 132.84 | 106.00 | 1315.94 | 7.3x | 2,188,534 | 10.5% | 6.3 |
| Q6 | 64 | 192 | 410,621 | 1,087,766 | 0.14 | 0.65 | 0.64 | 8.02 | 4.6x | 40,176 | 9.8% | 4.7 |
| cubic100 | 100 | 150 | 792,651 | 2,120,431 | 0.22 | 2.07 | 2.15 | 19.83 | 9.4x | 155,608 | 19.6% | 9.8 |
| cubic120 | 120 | 180 | 5,821,073 | 15,638,355 | 1.56 | 18.86 | 19.73 | 170.48 | 12.1x | 1,084,307 | 18.6% | 11.2 |
| games120 | 120 | 638 | 4,487,547 | 14,276,221 | 4.51 | 26.20 | 27.30 | 474.23 | 5.8x | 412,184 | 9.2% | 5.3 |
| homer | 561 | 1,628 | 135,386 | 550,365 | 0.35 | 1.00 | 1.02 | 33.50 | 2.9x | 12,412 | 9.2% | 5.7 |

Findings:

- M4 is the fastest method on all 17 instances. The better top-down variant is 1.0x
  (track1_171, a tie) to 16.9x slower; it comes closest on the MC2022 track 1 instances
  (1.0x to 1.8x), where m is large and the POG has 65k to 83k nodes.
- Top-down beats per-clause bottom-up everywhere: 2.7x (track2_081) to 126x (track1_149),
  over 39x on track2_095, 26x on queens14 (M1 finished at 2139 s) and 12x on grid16.
- Top-down evaluates 1 to 25 percent of the nodes of M1's sweep (N·m), but 0.7 to 15 times as
  many nodes as M4's batch passes (N·⌈m/63⌉), and a node costs it more (stack, memo and
  branches against one word operation per edge). On the families the short circuit leaves 6
  to 25 percent of the POG alive per clause; there the 63-fold batching wins.
- Unmeasured explanation for the two worst cases (track2_081, 17x; track2_089, 14x): few nodes
  per clause (58 and 74) but high fan-in (on average 256 and 46 arguments per node); a product
  that is not killed scans all its arguments, and these edge checks are not in the node count.
  An edge counter would test this; it is not part of the protocol.
- Signatures (M3 against M2) do not decide anything: faster on track1_149 (10.4 against 15.1 s,
  half the nodes), slower on grid16 (132.8 against 106.0 s), elsewhere within 7 percent.
- M4 against the table-reuse measurement of 2026-09-30 (same node type, same N): grid14 1.08 against 3.95 s, queens13 4.83
  against 7.97 s, the MC2022 instances within -5 to +26 percent. Not investigated; the large,
  memory-bound family POGs differ most, which fits different node load but was not tested.
- The driver's part A time (`partc-a`, M1 runs) reads 0 ms on large POGs, so the compiler
  evaluates part A before the clock; it is outside every method's clock anyway and not used.

## Decision (P4)

The rule is not met: no instance has a top-down variant at least 2x faster than M4; the closest
case is a tie within noise (track1_171: M2 7.21 s, M4 7.18 s). The checker keeps
`checkRevKillFast`; `RevTD.lean` stays an unverified baseline. In short: top-down short-circuit
evaluation is 1.0x to 17x slower than the bit-parallel check and 2.7x to 126x faster than
per-clause bottom-up evaluation, on the same POGs and in the same compiled Lean.
