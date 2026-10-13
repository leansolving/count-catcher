# Like-for-like comparison with cpog-lean-check (2026-10-05)

Status: complete. Arrays 129259 (families) and 129260 (MC2022) ran 19:03 to 20:37 on 12 b4 nodes
(b402 to b416); all 91 tasks finished. Per-instance table `unshortened.tsv` (collector
`scripts/cluster/unsh_collect.py`), raw key=value files, lists, driver and job ids in
`unshortened_raw.tgz` (cluster copy `/home1/szeider/mccert/unsh/`).

## Question

Figure 3 and R4 (`research/eval-2026-10-02/rerun.md`) compare our verified check on the refutation
after untrusted post-processing (`cpog2lrat --delete --binary --trim --keep --inline`: trimmed to
the backward cone, initial clauses masked, single-use additions inlined) with `cpog-lean-check` on
the full certificate. Here the same refutation is translated without the shortening steps
(`--delete --binary` only) and checked in the same job, next to the default translation and
`cpog-lean-check`.

## Protocol

- Instances: the 91 of Figure 3 (`PAPER/tables/fig3_data.csv`): 82 MC2022 formulas (R3 proved,
  generation under 600 s; the 81 of R4 plus track1_069) and the 9 families of R1 without
  14-queens and grid 16. Lists `unsh/list_mc.txt` (largest full certificate first) and
  `unsh/list_fam.txt` on the cluster.
- One Slurm array task per instance, driver `scripts/cluster/unshortened.sbatch`, in this order:
  D4 `-dDNNF`; `cpog-gen-fwd -F -T 500 -G` (forward certificate); `pog_count.py`; translation B
  (`--delete --binary`); translation A (`--delete --binary --trim --keep --inline`); the forward
  certificate deleted; Lean on B; Lean on A; full certificate from the same D4 output by the
  unpatched `cpog-gen`; `cpog-check` and `cpog-lean-check -c` on it. Limits as in R4: D4 and
  generation 4,000 s (the generator limit also bounds `pog_count.py` and the translator), Lean
  3,600 s per run, full generation and each CPOG checker 3,600 s.
- Theorem files by `theorem_lean.py --command` (the `count_models +stream` front end, object-level
  statements through the family lemmas, DIMACS form for MC2022), identical for A and B apart from
  the LRAT file, the POG path and A's `(keep := …)` mask.
- Lean on B runs first in each job, so it is measured as the single Lean run of an R4 job was
  (Mathlib import possibly from a cold page cache); Lean on A runs second. The check times
  (part B and parts A and C, as `count_models` reports them) do not include the import; the Lean
  totals do (column `lean_rest_s`: Lean total minus the command).
- Node class: b4 only (`-C bc4`, Intel Xeon E5-2640 v4, 2.4 GHz, as 89 of 90 R4 jobs), `-c 2`,
  32 GB (MC2022) and 48 GB (families), 6 h per task.
- Ratios: ours over `cpog-lean-check`, per instance and within one job, medians over the jointly
  completed runs (ours proved, `cpog-lean-check` finished with D4's count), zero denominators
  skipped, as `scripts/paper_numbers.py` computes R4.

## Builds and tools

- Lean: `/home1/szeider/mccert/lean_cc` (the renamed tree of 2026-10-05; packages symlinked from
  `lean_final`, lrat-catcher `b2e8d59`; plugin `libCountCatcher_CountCatcherChecker.so` sha256
  `6e443ac786d58d6ab9a8b46b5e18e0f616615254577b71bd0b695a15412fdf5f`, lrat-catcher plugin
  `3960e3019a284878be7760b7153f023ba492932f96766e2b61cc4d6c88ab33a3`, the same as in R4). The
  checker sources of `lean_cc` and of R4's `lean_final` differ only in names and comments
  (checked file by file with the names mapped). Built on gpu01; it runs on slurm-login01 and on
  the b4 nodes (all 182 Lean runs proved).
- Tools of R4 (`/home1/szeider/mccert/tools_final/bin`): `cpog2lrat` sha256 `77151b2c…`,
  `cpog-gen-fwd` `b028452a…`, `d4` `90ac342f…`, unpatched `cpog-gen`, `cpog-check`,
  `cpog-lean-check` (hashes in the result files).
- Scripts: `/home1/szeider/mccert/cc_repo/scripts` (the renamed working tree of 2026-10-05;
  `theorem_lean.py` sha256 `506770ac…`).
- Driver test on slurm-login01 (mc2022_track1_015 and homer): both variants proved, counts agree.

## Results

All 91 proved in both variants with D4's count; `cpog-lean-check` succeeded on all 91 with the
same count; `cpog-check` printed a wrong count on the same 7 instances as in R4 (cub100, cub120,
homer, ind14, track1_031, track2_027, track2_035). All ratios below are ours over
`cpog-lean-check`, medians of the per-instance ratios within one job, n = 91.

| boundary | B (`--delete --binary`) | ours lower (B) | A (default) | ours lower (A) | paper (R4, A) |
|---|---:|---:|---:|---:|---:|
| check alone (part B + parts A, C) | 0.39 | 91 | 0.23 | 91 | 0.23 |
| translator + Lean total | 1.21 | 36 | 0.86 | 51 | 1.28 |
| same, Lean outside the command exchanged (see below) | 0.94 | 49 | 1.17 | 38 | |
| pipeline after D4 (forward generation + translator + Lean against full generation + checker) | 0.91 | 55 | 0.79 | 62 | 0.93 |
| same, Lean outside the command exchanged | 0.82 | 62 | 0.86 | 55 | |
| Lean total alone | 1.14 | 39 | 0.70 | 54 | |
| Lean peak RSS over checker peak RSS | 3.98 | 12 | 3.59 | 14 | |

Medians of absolute values: check 7.31 s (B) and 4.65 s (A) against 25.3 s for
`cpog-lean-check`; Lean total 22.8 s and 15.2 s; translator 1.10 s and 2.20 s; Lean peak RSS
3.53 GB and 3.40 GB.

Per band of the full certificate's size (medians of the per-instance ratios; check alone is lower
than `cpog-lean-check` on every instance in every band, for both variants):

| band | n | check B | check A | translator + Lean B | translator + Lean A | Lean RSS B | Lean RSS A |
|---|---:|---:|---:|---:|---:|---:|---:|
| below 10 MB | 18 | 0.30 | 0.22 | 99 | 98 | 35 | 35 |
| 10 to 100 MB | 15 | 0.42 | 0.29 | 3.7 | 2.9 | 12 | 12 |
| 100 MB to 1 GB | 43 | 0.40 | 0.22 | 1.06 | 0.73 | 2.5 | 2.5 |
| above 1 GB | 15 | 0.40 | 0.19 | 0.61 | 0.38 | 0.66 | 0.54 |

B against A (medians of per-instance ratios, range in parentheses): LRAT bytes 1.66 (1.01 to
27.8), part B 1.66 (1.00 to 21.1), check 1.49 (1.00 to 14.1; 1.68 on the 58 instances with a full
certificate of at least 100 MB), Lean total 1.47, Lean peak RSS 1.03 (0.98 to 1.74), translator
0.55. Largest effects: track1_093 (LRAT 13 MB after shortening, 373 MB without; check 3.9 s to
55.2 s against 80.7 s for the checker) and track1_103 (398 MB to 2.54 GB; check 48.5 s to 278.9 s
against 371.9 s, the highest B ratio, 0.75). Lean memory grows most where the mask matters:
games120 7.5 to 13.1 GB (checker 13.8 GB), cub120 8.2 to 14.3 GB (16.9 GB), track2_011 6.8 to
11.3 GB (24.1 GB).

Sanity check against R4 (73 instances with the R4 checker at 1 s or more): `cpog-lean-check`
took 1.09 times as long as in R4 (median; 0.94 to 1.29) and our check on A 1.10 times (0.93 to
1.51), so the nodes ran about 10 percent slower (all their other cores busy with another user's
jobs) and the within-job check ratio for A reproduces the paper's 0.23 exactly.

## What is not like-for-like

- Run order. Lean on B ran first and Lean on A second in every job. The time outside the
  `count_models` command (process start, Mathlib import, `#print axioms`) is 15.9 s for B and
  11.0 s for A (medians); 12 B runs and no A run took 54 to 63 s there, the cold Mathlib import
  over NFS, which 6 of R4's single Lean runs show as well (track1_009, track1_029, track1_031,
  track2_043, track2_101, q12: 54 to 62 s). B's Lean total is
  therefore measured as R4 measured A, and A's here is warmer than in R4. The rows "Lean outside
  the command exchanged" give each variant the other's import time: B with a warm import 0.94 and
  0.82, A with a cold one 1.17 and 0.86 (the paper's 1.28 and 0.93 include the ~10 percent faster
  checker of R4's run). The check-alone ratios do not depend on the order.
- B still uses binary LRAT (1.25 to 1.3 times faster in part B than text) and
  `--delete` (deletion steps after each clause's last use; they free memory and remove no
  proof step). `cpog-lean-check` reads the text certificate, which carries cpog-gen's own
  deletions.
- B is the forward proof of `cpog-gen-fwd -F -T 500 -G`, not the forward half of the full
  certificate: on large instances `-T 500` sends more solver-call proofs through drat-trim, so the
  two proofs may differ slightly. The reverse implication is ours by evaluation (part C)
  and CPOG's by the clausal reverse half of the full certificate, by design.
- The translation to LRAT (renumbering, the POG file) remains untrusted preprocessing in both
  variants; B only drops the three shortening steps.
