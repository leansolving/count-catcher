# Differential test of the checker, rerun on the shipped code and pipeline (2026-10-07)

Status: done (2026-10-07, 21:51 to 22:58). No accepted record has a count different from the
brute-force count, on either route.

Goal: rerun the differential test of 2026-09-30 (`research/eval-2026-09-30/contract_audit.md`, section 3)
on the shipped commit with the default pipeline, and provide a seeded sample as the artifact's
reduced form.

## Shipped code

- Mac repository HEAD: `d0974499271d2a363aa5cc164fc69250be740db8` (commit d097449). The working tree
  has uncommitted changes in `lean/CountCatcher.lean` and new files (`DedekindCorner.lean`, tests);
  the checker library and `CountCatcherMath` are unchanged.
- Cluster build copy `/home1/szeider/mccert/lean_cc`: all 53 source files of `CountCatcherChecker/`,
  `CountCatcherMath/`, the three root modules, `lakefile.toml`, `lake-manifest.json` and
  `lean-toolchain` have the same md5 as `git archive HEAD lean` (checked 2026-10-07). Lean v4.30.0,
  lrat-catcher `b2e8d59` (v0.2.0).
- Tools: `/home1/szeider/mccert/tools_final/bin`: D4 (symlink to `tools/bin/d4`), `cpog-gen-fwd`
  (CPOG 1.2.0 a97ed85 with `cpog-gen-noreverse.patch` and `cpog-gen-fwd.patch`, md5 of the patches
  equal to the Mac's `tools-src/`), native `cpog2lrat` built from `tools_final/src` (main.rs of
  commit 75942ef; HEAD differs only in one comment line), cadical and drat-trim symlinked.

## Protocol changes against 2026-09-30

Unchanged: the formula sets E0 to E3, E3u, R (40,000) and RB (3,000) with their seeds (formula
generator `random.Random(f"{set}-1")`, deterministic enumeration for the E sets), the 48-task
worklist, the brute-force count as the expected value of every record, the mutation functions
(9 POG, 7 LRAT, 4 formula and 7 CPOG kinds, one mutant per kind for the E sets, two for R and RB),
the stage replay and the flags of the Lean driver, a private working directory per task, tool
timeouts of 20 s.

Changed (driver and generator in `research/eval-2026-10-07/contract_audit/`, the 2026-09-30
directory is untouched):

- Checker: the shipped tree (renamed `CountCatcherChecker`, byte-level POG parser, part B over
  the keep mask, lrat-catcher v0.2.0) instead of the working tree of 2026-09-30. Driver
  `count-catcher-audit` (`AuditMain.lean`) in `lean_audit2`, built against the precompiled
  libraries of `lean_cc` (only `AuditMain` was compiled).
- Generator: `cpog-gen-fwd -F -T 500 -G` (the default of `scripts/count_catcher.py`) instead
  of the unpatched `cpog-gen`; translator: the shipped native `cpog2lrat` (B1/B2 fixed).
- Two routes, each a separate record (a certificate is the triple formula, POG, proof):
  - text route: `cpog2lrat --delete --trim`, text LRAT, what `count_models` embeds for a small
    proof in auto mode. Verdict `checkAll` (embedded); the streamed route without keep file
    (`checkAllAC` and `checkStreamCnf (fwdCnfOf F pog)`) is compared with it (STREAMDIFF), as
    before. In 2026-09-30 the text proof had no flags (5% also with `--delete`); now 5% of the
    certified formulas also get a record with the flag-free translation (`/plain`).
  - default route (new): `cpog2lrat --delete --keep --inline --binary`, binary LRAT and keep mask,
    what `count_models … (keep := "fwd.keep")` streams. Verdict `checkAllAC V F pog N &&
    checkStreamCnf (fwdCnfOfSel F pog keep) certFeed streamFuel`, the two native evaluations of
    `countRoute`'s streamed branch (`CountCatcherMath/Command.lean`), with the binary file read by
    lrat-catcher's stream reader (block size 1, 2, 3 or 4096 actions by task). For comparison the
    driver also runs Lean core's LRAT check on the whole parsed binary file against `fwdCnfSel`
    (flag EMBDIFF when it disagrees with the streamed part B; informational).
- Mutants of the default route: the 9 POG and 4 formula mutations reuse the mutated POG or formula
  of the text route with the default proof (`kp_*`, `kf_*`); the 7 LRAT mutations are applied to
  the decoded binary proof and re-encoded (`kl_*`); new kinds `kb_flip` (one bit of the binary
  file flipped), `kb_trunc` (file truncated at a random byte), `kk_drop` (one clause that the
  mask keeps, all of which are cited, dropped from the mask), `kk_add` (one clause that the mask
  drops kept); the 7 CPOG mutations are translated a second time with the default flags (`kc_*`).
  Every binary proof is checked to round-trip through the Python decoder and encoder.
- Random generator: one per formula (`random.Random(f"mut-{name}-1")`) instead of one per shard,
  so a record does not depend on the sharding and the sample's records are records of the full run.
- Positive control in every task: the unmutated certificate of the first certified formula of the
  shard (and of every 1000th) with expected count N + 1, once per route (`/control_text`,
  `/control_default`); each must be flagged WRONG and is then reported CONTROL-OK. Controls are not
  counted in the tables.
- Dropped: the sampled comparison with the Python translator (`--pysample`; the Python script has
  no `--trim`, `--keep` or `--inline`).
- Peak memory per step (`/usr/bin/time`, fields `difftest_maxrss_kb`, `lean_maxrss_kb` in
  `info.txt`) was added to `audit_task.sh` after the full run, for the sample.
- Machine: gpu01 (no scheduler), 40 parallel tasks, scratch `/home/scratch/szeider/mccert_audit2`
  (per task, removed at its end), results `/home1/szeider/mccert/lean_audit2/results/`.

Smoke test before the run (E0, E1, R shard 0 of 200, RB shard 0 of 300; `results_test/`): 18,137
records, all unmutated certificates accepted on both routes, all 8 controls flagged, no WRONG,
BFDIFF, DIAGDIFF or CDIFF. A first smoke run with the scratch directory on NFS took 5 ms per record
(file writes for the stream reader); on gpu01's local disk 0.17 ms.

Hand suite (`contract_cases.py` of 2026-09-30, regenerated with the Mac's `tools/bin`, 40 records, through
the new driver; output `contract_audit/contract_lean.txt`): every record that exists in both runs
has the same verdict, stage, count and stream verdict as on 2026-09-30. The differences are the
translator fixes: c04, c05, c06 (valid formulas, B1) now translate and are accepted with counts 8,
4, 1; c23 and c24 are written with single spaces (B2), so the two double-space records rejected at
B-parse are gone, and the single-space records behave as before (c23 B-check, c24 accepted embedded
and rejected streamed, the known F-S). Table 11's constructed column (from the 2026-09-30 file)
thus describes the shipped checker too.

## Results

Run on gpu01, 2026-10-07 21:51:45 to 22:47:39 (wall 56 min, 40 parallel tasks of the 48-task
worklist); tool runs 33.8 CPU-h (D4, generator, two or three translations per formula and two per
CPOG mutant; 11.3 CPU-h on 2026-09-30), Lean 74.1 min for 12.1 million records (27 min for 5.6
million). Summary `difftest_summary.txt` (written by `contract_audit/summarize.py`), per-kind table
`difftest_kinds.tsv`; raw results archived (see the end).

Toolchain on the 239,173 base formulas: D4's count equals the brute-force count on all; 38,067
unsatisfiable formulas (cpog-gen-fwd refuses, as cpog-gen did); all 201,106 others are certified
and translated by both routes, the valid ones included (194,942 plus the 6,164 of B1, now fixed);
the POG of the two translations is identical and every binary proof round-trips through the
Python decoder and encoder.

### Table 11 format (generated column), old against new

Rejections at the first failing condition in the checker's order; "text" and "default" split
the new column by route.

| Check | Condition (stage) | 2026-09-30 | 2026-10-07 | text | default |
|---|---|---:|---:|---:|---:|
| universe | variables in the universe (cnf-wf) | 0 | 0 | 0 | 0 |
| | node table over V (pog-V) | 0 | 0 | 0 | 0 |
| validity | arguments earlier (A-arg) | 0 | 2 | 1 | 1 |
| | disjoint product supports (A-prod-overlap) | 369,285 | 739,166 | 369,583 | 369,583 |
| | hints cite defining clauses (A-sum-hint-ref) | 15,156 | 31,246 | 15,623 | 15,623 |
| | exclusion by unit propagation (A-sum-rup) | 739,425 | 1,475,770 | 737,885 | 737,885 |
| | root declared (A-root-range) | 0 | 0 | 0 | 0 |
| reverse | no negated node (C-negation) | 265,151 | 542,892 | 271,446 | 271,446 |
| | every clause kills the root (C-clause) | 1,230,613 | 2,493,640 | 1,246,820 | 1,246,820 |
| forward | well-formed LRAT (B-parse) | 67 | 296,388 | 0 | 296,388 |
| | RUP steps, empty clause (B) | 2,198,135 | 5,010,365 | 2,266,319 | 2,744,046 |
| | accepted, each with the brute-force count | 750,387 | 1,553,855 | 733,956 | 819,899 |
| | total | 5,568,219 | 12,143,324 | 5,641,633 | 6,501,691 |

Accepted: 412,447 unmutated certificates (201,106 text, 10,235 flag-free text, 201,106 default),
none rejected; 1,141,408 mutants. Totals line in the format of 2026-09-30: 12,143,324 Lean records,
1,553,855 accepted (402,212 base, 10,235 delete, 1,141,408 mutants), where "base" now counts the
unmutated certificates of both routes and "delete" the flag-free sample. Flags: no WRONG, no
WRONGSTREAM, no BFDIFF, no DIAGDIFF, no CDIFF; all 474 positive controls (237 per route) flagged
WRONG.

### Per kind, old against new

| Kind | Records 09-30 | Accepted 09-30 | Records text | Accepted text | Records default | Accepted default |
|---|---:|---:|---:|---:|---:|---:|
| base | - | - | 201,106 | 201,106 | - | - |
| plain | - | - | 10,235 | 10,235 | - | - |
| default | - | - | - | - | 201,106 | 201,106 |
| mp_flip_arg | 222,545 | 0 | 222,552 | 0 | 222,552 | 0 |
| mp_change_arg | 188,388 | 2 | 189,365 | 0 | 189,365 | 0 |
| mp_drop_arg | 221,504 | 0 | 221,603 | 0 | 221,603 | 0 |
| mp_add_arg | 225,800 | 0 | 233,601 | 0 | 233,601 | 0 |
| mp_root_neg | 194,942 | 0 | 201,106 | 0 | 201,106 | 0 |
| mp_root_change | 187,737 | 3,255 | 193,669 | 0 | 193,669 | 0 |
| mp_sum_hint | 146,677 | 31,356 | 146,581 | 31,189 | 146,581 | 31,189 |
| mp_kind_swap | 157,276 | 0 | 157,266 | 0 | 157,266 | 0 |
| mp_dup_node | 216,053 | 0 | 222,233 | 6,164 | 222,233 | 6,164 |
| ml_drop_hint | 224,602 | 86,538 | 231,593 | 92,794 | 226,930 | 101,115 |
| ml_change_hint | 207,890 | 52,007 | 211,575 | 42,163 | 197,062 | 52,877 |
| ml_flip_lit | 169,978 | 88 | 169,954 | 0 | 150,968 | 0 |
| ml_drop_lit | 169,847 | 58,204 | 169,588 | 57,833 | 151,652 | 77,990 |
| ml_add_lit | 225,713 | 43,824 | 233,316 | 36,132 | 231,444 | 24,757 |
| ml_drop_line | 222,456 | 0 | 222,441 | 0 | 220,443 | 0 |
| ml_swap_lines | 224,254 | 980 | 224,226 | 14 | 221,744 | 5 |
| mf_drop_clause | 226,104 | 60,161 | 230,650 | 64,588 | 230,650 | 0 |
| mf_add_clause | 226,104 | 0 | 234,030 | 0 | 234,030 | 0 |
| mf_flip_lit | 226,104 | 41,445 | 230,650 | 42,941 | 230,650 | 52,585 |
| mf_drop_lit | 225,493 | 75,175 | 230,039 | 76,035 | 230,039 | 88,298 |
| mc_decl_flip | 226,104 | 0 | 226,104 | 0 | 226,104 | 0 |
| mc_decl_change | 220,505 | 21,444 | 220,435 | 21,187 | 220,435 | 21,187 |
| mc_decl_drop | 225,554 | 0 | 225,559 | 0 | 225,559 | 0 |
| mc_add_drop_hint | 226,104 | 48,194 | 226,104 | 32,197 | 226,104 | 21,101 |
| mc_add_change_hint | 206,542 | 22,677 | 206,687 | 17,781 | 206,687 | 11,277 |
| mc_add_flip_lit | 143,443 | 103 | 143,582 | 1,383 | 143,582 | 1,388 |
| mc_root_change | 5,780 | 214 | 5,783 | 214 | 5,783 | 214 |
| kb_flip | - | - | - | - | 234,031 | 62,004 |
| kb_trunc | - | - | - | - | 234,031 | 0 |
| kk_drop | - | - | - | - | 234,031 | 0 |
| kk_add | - | - | - | - | 230,650 | 66,642 |

Default-route rows of the m kinds are the k kinds (`kp_*`, `kl_*`, `kf_*`, `kc_*`); the stages of
every kind are in `difftest_summary.txt`. Translator rejections of CPOG mutants (not Lean records,
equal for both routes): `mc_root_change` 218,729 and `mc_add_flip_lit` 82,522 ("no root unit"),
`mc_decl_drop` 545 ("cites no earlier clause").

### Differences to 2026-09-30

- The text route reproduces the old run: about the same records per kind, and every condition
  rejects about as often as before. The record counts per kind grow by the 6,164 valid formulas
  that the B1 fix lets through (all accepted, count 2^V).
- `mp_dup_node` and `kp_dup_node` now accept 6,164 each: exactly the valid formulas, whose POG is
  the empty product `p u 0`. Duplicating it puts the units `u` and `¬u` (the negated root) among
  the initial clauses, which the core LRAT checker finds contradictory before any step, so every
  final step succeeds; the count stays 2^V. (Example E0:0: `p cnf 0 0`, POG `p  0` twice, LRAT
  `3 0 1 2 0`, accepted with count 1.)
- `mp_root_change` accepted 3,255 random roots on 2026-09-30 and none now; the mutation is the
  same, the proofs differ (forward-only generator, trimmed proof), and the extra rejections land in
  part B (31,393 against 22,068).
- B-parse: 67 on 2026-09-30 (B2, double spaces, fixed since), none on the text route now; on the
  default route 296,388, all from `kb_flip` (89,684) and `kb_trunc` (206,704): the core binary
  parser rejects the file. No truncated file was accepted.
- The keep mask behaves as specified: dropping a cited clause from the mask (`kk_drop`) is
  rejected in part B every time (234,031 of 234,031); keeping an extra clause (`kk_add`) is accepted
  66,642 times, when the clause is a tautology or comes after every cited clause, so no ID shifts.
  The mask is positional, which explains the formula mutants of the default route: dropping a
  clause shifts every later mask byte, so `kf_drop_clause` is always rejected (the text route
  accepts 64,588, for instance when the dropped clause is a tautology, which has no ID anyway);
  `kf_drop_lit` and `kf_flip_lit` are accepted more often than on the text route, consistent with
  a mutation that turns a tautology of F into an ordinary clause: on the text route the new clause
  gets an ID and shifts the later ones (part B fails), on the default route its mask byte is `0`
  and it stays out.
- STREAMDIFF (text route, embedded accepts, streamed rejects): 108 (72 `ml_drop_hint`, 36
  `mc_add_drop_hint`) against 71 (`ml_drop_hint`), the known F-S of lrat-catcher's
  `normalizeAction` on hint-less RUP steps; never the other way.
- EMBDIFF (default route, streamed part B against core's check of the whole parsed file, both on
  `fwdCnfSel`): 403 `kb_flip` records accepted by the stream reader and rejected by the core parser,
  and 1 `kc_add_drop_hint` record (R:37472) rejected streamed and accepted by core (the F-S case).
  In the three `kb_flip` cases decoded (E2:3320, E2:10231, E2:11388, a 19-byte proof each) the
  flipped bit turns the last hint of the final addition into a terminator: the stream reader checks
  the shorter addition, which still derives the empty clause, and stops, while the core parser
  rejects the stray zero byte left at the end of the file. Sound either way (the streamed theorem
  quantifies over every feed); the count is the brute-force count.
- lrat-catcher printed 39,937 "index out of bounds" messages, all on mutants (deletion of a clause
  ID that does not exist, a no-op); the unmutated records of the smoke test printed none.

## Sample for the artifact (`--sample N`)

Option `difftest.py --sample N`: each formula of E2, E3, E3u, R and RB is kept independently with
probability N / 12,143,324 (the record count of the full run without controls, constant
`FULL_RECORDS`), decided by `random.Random(f"sample-{set}-{index}-{seed}")` with `--seed 1`; E0 and
E1 (213 formulas) are kept completely. Mutants come from the per-formula generator, so every
record of the sample is a record of the full run. Worklist `contract_audit/worklist_sample.txt`
(8 tasks, `SAMPLE` = 100000 in the sixth column); run as
`run_gpu01.sh worklist_sample.txt 4 0 7 RESULTS`, then `summarize.py RESULTS`.

Run 2026-10-07 22:51:37 to 22:55:18 on gpu01, 4 parallel tasks (`/usr/bin/time -v` around the
whole run):

- 98,893 records plus 16 controls, from 2,126 formulas (1,655 certified); 12,734 accepted (3,388 unmutated), no
  flagged record, all 16 controls flagged WRONG; summary `difftest_sample_summary.txt`, table
  `difftest_sample_kinds.tsv`.
- Every one of the 98,893 result lines (verdict, stage, count, flags) is identical to the line of
  the same record in the full run.
- Wall time 3 min 42 s on 4 cores (CPU 230%; user 85 s, system 426 s, mostly process starts of
  the tools); tool runs 671 s and Lean 22 s summed over the tasks, so about 12 minutes on one core.
- Peak memory 144 MB (maximum resident set of one process, the Lean driver on the R task; the
  Python generator with its tools 42 MB).

## Hand suite

- Constructed column of Table 11: unchanged (the 2026-09-30 file); the shipped checker gives every
  common record the same verdict (Protocol section).
- Generated column: 12,143,324 certificates, 1,553,855 accepted, rejections as in the table above.

## Axioms of the soundness theorems

`contract_audit/Axioms.lean` (port of the 2026-09-30 file: the nine theorems of the paper's
soundness listing in its order, plus `LRATCatcher.checkLratCnf_sound`
of the old list), run in `lean_audit2` on slurm-login01 with `lake env lean Axioms.lean`
(2026-10-07 21:51, 19 s). Verbatim output:

```
'CountCatcher.checkPog_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CountCatcher.fwd_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound]
'CountCatcher.checkRevKillFast_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CountCatcher.card_models_eq_countRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'CountCatcher.checkAll_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CountCatcher.checkAllAC_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CountCatcher.fwdCnfOf_unsat_of_sel' depends on axioms: [propext, Quot.sound]
'LRATCatcher.checkStreamCnf_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CountCatcher.Family.card_of_checkAC' depends on axioms: [propext, Classical.choice, Quot.sound]
'LRATCatcher.checkLratCnf_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` and no native axiom (`Lean.ofReduceBool`, `*._native.*`). `fwdCnfOf_unsat_of_sel`
needs only two of the three standard axioms, the others all three. A first run without
`import LRATCatcher.StreamOracle` failed on `checkStreamCnf_sound` (unknown constant, the module
was not imported) and printed the other nine identically.

## How `app_adversarial()` should read the new results

Done in `scripts/paper_numbers.py` (only `app_adversarial()` and its constants changed; the output
format is the same): `AUDIT_MD` and the regexes `AUDIT_ROW`, `AUDIT_STAGE`, `AUDIT_TOTALS` are
replaced by `DIFFTEST_TSV = research/eval-2026-10-07/difftest_kinds.tsv` (written by
`contract_audit/summarize.py RESULTS --tsv FILE`: kind, route, records, accepted, rejected stages as
`STAGE:N,...`). The generated column sums the stages over all kinds of both routes; total and
accepted are the column sums; a kind whose stages and acceptances do not add up to its records
warns. The hand suite (`AUDIT_HAND`) and the Lean-format cases stay. A run of `app_adversarial()`
into a scratch directory gave the old table with the new generated column (2, 739,166, 31,246,
1,475,770, 542,892, 2,493,640, 296,388, 5,010,365; accepted 1,553,855; total 12,143,324);
`PAPER/tables/app_adversarial.tex` itself was not rewritten (the next full run of
`paper_numbers.py` does that).

## Files

- `research/eval-2026-10-07/contract_audit/`: `AuditMain.lean` (driver `count-catcher-audit`),
  `difftest.py`, `audit_task.sh`, `run_gpu01.sh`, `audit.sbatch`, `build_audit.sbatch`,
  `worklist.txt` (48 tasks), `worklist_sample.txt`, `summarize.py`, `Axioms.lean`,
  `contract_lean.txt` (hand suite through the new driver).
- `research/eval-2026-10-07/`: this file, `difftest_summary.txt`, `difftest_kinds.tsv`,
  `difftest_sample_summary.txt`, `difftest_sample_kinds.tsv`.
- Cluster: build copy `/home1/szeider/mccert/lean_audit2` (cp -a of `lean_cc`, `.lake/packages`
  still the symlink to `lean_final`'s packages, `lakefile.toml` with the extra `lean_exe`); raw
  results archived in `/home1archive/szeider/projects/mccert/difftest_2026-10-07/` (`results/` with
  per task `info.txt`, `lean.out.gz` (one line per record), `tools.tsv.gz`, `lean.err`;
  `results_sample/`, `results_test/`, `smoke/`, `logs/`, `gpu01_logs/`, the scripts; 79 MB,
  checksums verified), with symlinks `results`, `results_sample`, `results_test`, `smoke` back in
  `lean_audit2`.
- Reproduce: `cp -a lean_cc lean_audit2`, append the `count-catcher-audit` exe to `lakefile.toml`,
  copy `AuditMain.lean` and the scripts (into `lean_audit2/audit/`), `lake build
  count-catcher-audit`, then `run_gpu01.sh audit/worklist.txt 40` on gpu01 (or
  `sbatch --array=0-47%32 audit/audit.sbatch`), then `summarize.py results --tsv kinds.tsv`. The
  scratch directory of a task must be on a local disk (5 ms instead of 0.17 ms per record on NFS).
