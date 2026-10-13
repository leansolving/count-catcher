# count-catcher

Lean theorems from model counting certificates.

count-catcher turns the certificate of an exact propositional model counter into a
kernel-checked Lean 4 theorem, the count theorem, which states the number of models of a CNF
formula given as a Lean term. With an encoding lemma per family, the count theorem becomes an
end-to-end theorem about the number of combinatorial objects, for example

```lean
theorem queens14 : Nat.card {f : Fin 14 → Fin 14 // Queens.Safe f} = 365596
```

The counter is d4 (decision-DNNF). The certificate is CPOG-compatible: the circuit as a POG
(partitioned-operation graph) and a clausal proof that the formula implies the circuit, both
written by cpog-gen. An untrusted translator splits it into a node table and an LRAT
refutation. The checker is a Lean program, proved correct in Lean, that runs three checks: the
validity check (the POG is a valid POG, and its count is computed bottom-up), the forward check
(every model of the formula makes the root true, by checking the LRAT refutation with
lrat-catcher) and the reverse check (every assignment that makes the root true is a model,
by evaluating the circuit against every clause in bit-parallel batches). The soundness
theorems that connect the three checks to the count theorem use only the three standard
axioms `propext`, `Classical.choice` and `Quot.sound`. The checker runs by native evaluation,
so a theorem produced this way depends in addition on one axiom per native evaluation (one
for an embedded certificate, a second for a streamed forward check), which states that the
compiled checker returned true; `#print axioms` lists them.

This is the artifact of the TACAS 2027 submission "count-catcher: Lean Theorems from Model
Counting Certificates" by Johannes K. Fichte and Stefan Szeider. The archived version, with
the inputs and the logs of all runs and a prebuilt tree for offline installation, is on
Zenodo: https://doi.org/10.5281/zenodo.23304375.

## Contents

| Path | What it is |
|---|---|
| `lean/CountCatcherChecker/` | the executable checker (Mathlib-free, precompiled): POG parser, validity check and count, forward check through lrat-catcher, bit-parallel reverse check |
| `lean/CountCatcherMath/` | the soundness proofs, the `count_models` and `#export_cnf` commands (`Command.lean`), and the families in `Families/` (domino tilings, independent sets of grids and of arbitrary graphs, n-queens, Latin squares, Dedekind numbers, Kreweras lattices, Sperner families, total domination, graph isomorphism classes, unsatisfiable formulas), each with its encoding lemma |
| `lean/CountCatcher.lean` | the user front end: `import CountCatcher` |
| `lean/test/` | 37 end-to-end tests with their certificate data (`test/run.sh`), among them the constructed certificates in Lean format (`Adversarial.lean`) |
| `scripts/count_catcher.py` | the driver (installed as `bin/count-catcher`): Lean term or DIMACS file to a checked theorem |
| `scripts/`, `scripts/showcase/` | generators, the reference translator `cpog2lrat.py`, the showcase drivers, `paper_numbers.py` (every number and table of the paper), the cluster job scripts behind the paper's runs (`scripts/cluster/`, with the site defaults of our cluster) |
| `tools-src/` | the native translator `cpog2lrat` (Rust) and the two patches of cpog-gen |
| `inputs/mc2022_subset/` | the 44 formulas of the competition set whose certificates are below 100 MB (Model Counting Competition 2022, CC BY 4.0) |
| `research/` | the run records and result files behind every table of the paper, read by `scripts/paper_numbers.py`; `research/upstream/` for CPOG's verified checker |
| `PAPER/numbers.tex`, `PAPER/tables/` | reference outputs of `paper_numbers.py`, generated, to compare with a rerun |
| `artifact/` | installation (`install.sh`), smoke test (`smoke.sh`), reproduction (`reproduce.sh`, `check.py`, `expected.tsv`), environment (`env.sh`), the order-8 Latin squares theorem (`latin8_all.lean`), the cross-check with two other counters (`xcheck/`) |

## Getting started in the TACAS artifact evaluation VM

The artifact was tested in the TACAS 2026 artifact evaluation VM (Zenodo record 17171929,
Ubuntu 25.04, amd64; no TACAS 2027 VM was published as of 2026-10-11), whose disk image we
ran under QEMU/KVM with 4 vCPUs and 16 GB. Both installation routes below passed there.

1. Machine. The VM ships with 2 vCPUs and 8 GB of memory. Before `reproduce.sh --all`, raise
   it to 4 CPUs and at least 14 GB (16 GB if the host allows; the desktop of the VM uses
   memory too). The `showcases` stage needs 13.0 GiB (9.5 GiB with `--skip-large`), the
   `validation` stage 8.4 GiB. The installation, the smoke test and the short stages
   (`tests`, `axioms`, `handsuite`, `difftest`) stay below 5.5 GiB. The user `tacas` has
   sudo (password `tacas`), which only the apt step of the online route uses.
2. Disk. The VM's disk has 40 GB with 24 GB free. The offline route needs about 14 GB while
   unpacking (2.8 GB tarball plus 11 GB tree); delete the `.tar.zst` afterwards. The online
   route adds about 12 GB. `reproduce.sh --all` needs up to 10 GB more (5 GB with
   `--skip-large`). Both fit, with about 2 to 3 GB to spare.
3. Files. The Zenodo record contains the source tree of this release
   (`count-catcher-src.tar.gz`), the prebuilt tarball `count-catcher-prebuilt-x86_64.tar.zst`,
   `inputs.tar.gz` and `logs.tar.gz`, each with its `.sha256` file.
   With network, download them inside the VM (browser or `curl -LO` with the file links of
   the record). Without network in the VM, download them on the host and attach them to the
   VM, for example through a VirtualBox shared folder (the VM has the guest additions) or on a
   second virtual disk. Check the tarball with
   `sha256sum -c count-catcher-prebuilt-x86_64.tar.zst.sha256`.
4. Unpack the source tree; its top directory (the one with this README) is the repository
   root, from which all commands below run. `MANIFEST` lists every file with its SHA-256 (the
   path after `<-` is where the file was staged from in the development repository, which is
   not part of the release); check the tree with
   `grep -v '^#' MANIFEST | sed 's/  <-  .*//' | sha256sum -c --quiet` (no output means all match).

## Installation

Requirements: x86_64 Linux (d4 links a prebuilt x86_64 PaToH library), so the host must be an
x86_64 (Intel or AMD) machine; on an ARM host such as an Apple Silicon Mac the amd64 VM runs
only under emulation, which is too slow for the reproduction. Tested on Ubuntu 25.04
(the AE VM, and a container with the VM's package set) and Ubuntu 26.04.1 LTS. Beyond the VM's
packages, the online route installs `m4` and `libboost-dev` with apt.

### Offline route (prebuilt tarball, no network)

```sh
tar --zstd -xf PATH/count-catcher-prebuilt-x86_64.tar.zst    # in the repository root, 100 s in the VM
rm PATH/count-catcher-prebuilt-x86_64.tar.zst                # frees 2.8 GB
source artifact/env.sh
artifact/smoke.sh                                             # 15 s, ends with OK
```

The tarball (2.8 GB, 11 GB unpacked) was built by `artifact/pack_prebuilt.sh` from a clean
online installation on Ubuntu 25.04. It adds `lean/.lake/` (the Lean dependencies with their
build outputs), `tools/` (binaries and the sources they were built from), `bin/` (the
`count-catcher` wrapper and uv 0.12.23) and the Lean toolchain as `.elan/`. Nothing outside the
repository is touched, and nothing is downloaded. Sourcing `env.sh` (which `bin/count-catcher`
does itself) points Lean at the in-tree toolchain; do it in every new shell. The tarball
matches the Lean sources of the release it was built from (`tools/PREBUILT.txt` records their
fingerprint, `smoke.sh` checks it; its line `commit: none` means that it was packed from the
release archive, not from a git checkout). `cd lean && lake build` then finds everything up to date (2 s).

Measured in the VM without network (4 vCPUs, 16 GB): unpacking 100 s, `smoke.sh` 15 s (peak
3.6 GiB), `artifact/reproduce.sh --stage tests axioms handsuite` 161 s (tests 143 s and
4.1 GiB, axioms 3 s, handsuite 12 s), all PASS, and no file written into the home directory.

### Online route (build from source)

```sh
bash artifact/install.sh          # sudo apt-get for m4 and libboost-dev, then everything else
source artifact/env.sh
artifact/smoke.sh                 # 10 to 15 s, ends with OK
```

`install.sh` builds, at pinned commits, d4 (with a static GMP), cpog-gen and cpog-check,
cpog-gen-fwd (cpog-gen with our two patches), CaDiCaL and drat-trim into `tools/`, compiles
`cpog2lrat` with cargo (it installs Rust with rustup only if `cargo` is missing; the VM has
cargo 1.89.0 in `~/.cargo`, on the PATH of a terminal), installs uv 0.12.23 if no uv is
present and the Lean toolchain (elan), fetches Mathlib's prebuilt files, compiles the Lean
libraries and writes `bin/count-catcher`. It needs network access to GitHub, gnu.org,
Mathlib's cache server, astral.sh and, without cargo, rust-lang.org (about 1.5 GB of
downloads). `--no-apt` skips the apt step, `--jobs N` sets the parallelism. The script is
idempotent; a second run takes about 20 s. Each step's log and its time and peak memory go
to `artifact/logs/`.

Measured in the VM (4 vCPUs, 16 GB): 356 s in all, apt 12 s, tools 80 s, cpog2lrat 4 s,
uv 1 s, elan and toolchain 25 s, Mathlib 171 s, Lean build 63 s with a peak of 5.3 GiB
(5,397 MiB PSS, of which 1.1 GiB anonymous memory); `smoke.sh` 10 s;
`artifact/reproduce.sh --stage tests axioms handsuite difftest` 427 s (tests 129 s, axioms 3 s,
handsuite 8 s, difftest 281 s and 1.9 GiB), all PASS. In a container with the VM's packages on
a 2016 Xeon (E5-2640 v4), the installation took 385 s with 4 CPUs and 14 GB and 579 s with 2
CPUs and 4 GB.

## Using the tool

A theorem from a Lean encoder term, with the family's encoding lemma:

```sh
count-catcher queens8 --via 'Queens.card_of_check (n := 8)' --run
```

writes `count-catcher-out/queens8/queens8.lean` with the certificate files next to it. The
file contains one `count_models` line, which names the theorem, the encoding lemma, the
certificate files and the count. `--run` runs Lean on it and outputs the count (92) and the
axioms. A theorem about a DIMACS file:

```sh
count-catcher track1_023 --dimacs inputs/mc2022_subset/mc2022_track1_023.cnf --run
```

(27 models, about 10 s). `count-catcher --help` lists the options (embedded or streamed
refutation, generation modes, no deletions, no inlining). Inside a Lean file,
`import CountCatcher` gives the `count_models` command and every family; the files in
`lean/test/` are small examples, and `cd lean && test/run.sh` runs all of them against
`test/expected/` (about 3 minutes on 4 cores).

## Reproducing the paper's results

`artifact/reproduce.sh --list` names the stages; `artifact/reproduce.sh --all` runs them in
order and ends with a PASS/FAIL table from `artifact/check.py` against `artifact/expected.tsv`,
where every expected value carries its reference in the paper. `--stage NAME [NAME ...]` runs
some stages, `--skip-large` leaves out the two showcases above 10 GB (A358391(6) and
A303210(9)), `--item KEY` runs single items of the stages `tests`, `showcases`, `validation`,
`competition` and `streamed` (`check.py` then reports the stage's other items as NOTRUN, which
does not count as a failure). Logs and results land in `artifact/out/` (`results.tsv`, one line
per item). `results.tsv` accumulates over invocations: a rerun replaces the lines of what it
reruns and keeps the others, while the PASS/FAIL table at the end covers only the stages of
that invocation (`python3 artifact/check.py` checks every stage in the file).

Times and peaks per stage on two machines: "Xeon" is a container with the VM's packages on
4 cores of a 2016 Intel Xeon E5-2640 v4 with 14 GB (2026-10-08; the order-8 items measured
there on 2026-10-11), "VM" the TACAS AE VM with 4 vCPUs of an AMD EPYC 9274F host and 16 GB,
offline (`--all` of this release, 2026-10-12). Peak: summed PSS of the item's processes on the
Xeon, including the about 3 GB of Mathlib that every Lean process maps.

| Stage | What it reproduces | Xeon | VM | Peak (GiB) |
|---|---|---|---|---|
| `tests` | the 37 end-to-end tests | 3 min | 2 min | 4.1 |
| `axioms` | the axioms of the nine soundness theorems (Listing 5, Section 4.5) | 4 s | 3 s | 3.3 |
| `handsuite` | the constructed certificates (Table 11, constructed column) | 11 s | 12 s | 3.6 |
| `showcases` | every theorem of Table 3 except A396728(7); for the order-8 Latin squares the theorem `latin8_all` from the 737 leaf counts as hypotheses and the rerun of one leaf | 73 min (46 min with `--skip-large`) | 47 min | 13.0 (9.5) |
| `validation` | nine of the eleven validation instances (Table 7) | 46 min | 32 min | 8.4 |
| `competition` | the 44 formulas of Table 10 with certificates below 100 MB | 25 min | 13 min | 4.1 |
| `streamed` | embedded against streamed refutation on 11 instances (Table 14) | 15 min | 10 min | 5.7 |
| `difftest` | a seeded sample of the differential test, 98,893 certificates (Table 11, generated column) | 4 min | 5 min | 1.8 |
| `extras` | the wrong count of cpog-check, CPOG's unverified checker, on random cubic 100 (Section A.5), the kernel-only check (Section 6), every number and table of the paper from the shipped result files | 1.5 min | 1 min | 6.4 |

Totals: on the Xeon, `--all` took 2 h 44 min with a peak of 13.0 GiB and `--all --skip-large`
2 h 17 min with a peak of 9.5 GiB (one run each of the version of 2026-10-08, which did not yet
have the two order-8 items; they add about 3.5 minutes there). In the VM (2026-10-12), `--all`
took 1 h 51 min with a peak of 13.0 GiB, and all 191 checks passed (167 PASS, 24 INFO); the
later changes to the reporting scripts (NOTRUN with `--item`) were checked in shorter VM runs.
The item keys of a stage are the first words of its rows in `artifact/expected.tsv`;
`reproduce.sh` rejects an unknown key and lists the valid ones.
The run needs up to 10 GB of disk beyond the installation (5 GB with `--skip-large`). With
less than 14 GB of memory, use `--skip-large`.

Some single items take long and print nothing until they end (their output goes to
`artifact/out/STAGE/ITEM.log` while they run). On the Xeon, with the VM in brackets where
measured: `r35_13` 26 min (18 min; Table 3's 78.9 s is its Lean time only, the item also exports
and certifies all 113 summands, 4 counts and 109 refutations), `q13` 20 min, `krew6` and `td9` 13 min each,
`dom12` 9 min (5 min), `tri10` and `ded7` 7 min each (4 min).

### Where each result of the paper is reproduced

The Data Availability Statement of the paper lists five items; they and the other results map
to commands as follows. "Expected" is what `artifact/out/results.tsv` and the PASS/FAIL
table compare against (`artifact/expected.tsv`).

| Paper | Command | Expected |
|---|---|---|
| (i) the theorems of Table 3 except A396728(7) and order 8 | `artifact/reproduce.sh --stage showcases` | triangle-free graphs 12,172 (19,213,627,145 labelled); Latin squares of order 7 16,942,080 reduced and 61,479,419,904,000 in all (Listings 1 and 2, one file); M(7) 2,414,682,040,998; A358391(6) 206,103,695,057,137,712 (the command of Listing 4); A303210(9) and (10); the (3,5)-Ramsey graph on 13 vertices unique |
| (ii) nine of the eleven validation instances (Table 7) | `artifact/reproduce.sh --stage validation` | the nine counts of Table 7; queens 14 and the 16×16 grid are logs only |
| (iii) the 44 competition formulas with certificates below 100 MB (Table 10) | `artifact/reproduce.sh --stage competition` | the 44 formulas of Table 10 (Table 10 gives their sizes and times, not their counts; the expected counts are in `artifact/expected.tsv`, from the run of 2026-10-02 in `research/eval-2026-10-02/rerun_raw/r3_results.tgz`), and the SHA-256 of each input |
| (iv) the constructed certificates and a sample of the differential test (Table 11) | `artifact/reproduce.sh --stage handsuite difftest` | constructed column `1 1 2 3 1 3 1 4 4 1 3`, 22 accepted, 46 in all; sample: 98,893 records, 12,734 accepted, none with a wrong count, 16 of 16 controls flagged (the sample keeps each formula with all its mutants with probability 100,000 / 12,143,324, so about 100,000 records are expected; with seed 1 it has 98,893) |
| (v) the order-8 Latin squares from the leaf counts, any leaf on request | `artifact/reproduce.sh --stage showcases --item lat8asm --item lat8leaf` (see below) | 108,776,032,459,082,956,800 with only the three standard axioms; leaf 653 count 1,003,520 |
| Listing 5, Section 4.5 | `artifact/reproduce.sh --stage axioms` | `propext`, `Classical.choice`, `Quot.sound` for the nine soundness theorems (`fwdCnfOf_unsat_of_sel` without `Classical.choice`) |
| Table 14 | `artifact/reproduce.sh --stage streamed` | the 11 counts; the median ratios within 30% of 0.90 and 1.9 (single ratios are information only) |
| Section A.5 | `extras` | cpog-check reports success with 8,281,581,627,129,036,755; the theorem's count is 8,281,581,627,129,350,099 |
| Section 6, kernel-only check | `extras` | the 4×4 domino refutation (99 additions) checked by the kernel alone, with only the three standard axioms |
| every number and table, Table 12 | `extras` | all table files identical to `PAPER/tables/`; Table 12 9,054 new and 1,816 reused lines; `numbers.tex` identical except the 30 hybrid-generation macros (see the note at the end) |
| Sections 6 and A.3, the other counters | `artifact/xcheck/xcheck.sh` (see below) | 18 of 18 counts equal |
| Table 5, reverse-check baselines | `cd lean && lake build count-catcher-partc` (see below) | |

### Latin squares (Listings 1 and 2, Table 3)

The theorem file of order 7 is one file `OUT/latin7.lean` with the names and relative paths of
the listings (`count_models latin7_fibre0 ... "c0/fwd.pog"`, `latin7_reduced`, `latin7_all`);
each fiber is certified by the driver (`count_catcher.py latin7_fibreI --via
'Latin.fibre_card_of_check ...'`) in `OUT/cI/`:

```sh
uv run --no-project scripts/showcase/latin_cycles.py --n 7 --out OUT --single     # about 3 minutes
```

Order 8 took 737 leaf certificates (7.9 TB). `artifact/latin8_all.lean` states `latin8_all`
with seven hypotheses, one per fiber class: each says that every leaf of the class has its
count (the statement of the leaf theorems, the hypothesis of `Latin.fibre_card_eq_of_cells`).
Lean checks the rest, that the leaves cover each fiber, the sums and the classes of the second
rows, in about 80 seconds and without certificates; `#print axioms latin8_all` lists the three
standard axioms. The script outputs `proved count 535281401856`: that is `latin8_reduced`, the
number of reduced Latin squares of order 8, and `latin8_all` multiplies it by 8! 7! (with
`Latin.card_latin_eq`) to 108,776,032,459,082,956,800. The file is written from the run's records (`research/latin8-2026-10-04/plan.json`
and `res/LEAF.txt`, which contain each leaf's count, times and `#print axioms`), and any leaf
reruns end to end:

```sh
uv run --no-project scripts/showcase/latin_cycles.py --plan research/latin8-2026-10-04/plan.json \
    --assemble-hyp --hyp-out OUT/latin8_all.lean                          # equals artifact/latin8_all.lean
uv run --no-project scripts/showcase/latin_cycles.py --plan research/latin8-2026-10-04/plan.json \
    --leaf 653 --out OUT                                                  # leaf c6_0025, about 2 minutes
```

The leaf's theorem `latin8_c6_0025` (in `OUT/mod/Latin8Cyc/c6_0025.lean`, result in
`OUT/res/c6_0025.txt`) states the count of one entry of the hypothesis for the fiber of the
second row 12345670; `research/latin8-2026-10-04/plan.tsv` lists the 737 leaves with their
index. Leaf 653 is one of the smallest; the largest certificate of order 8 has 32.7 GB, and the
peak Lean memory of a leaf was 21.6 GB (Table 6).

### Constructed certificates (Table 11)

The `handsuite` stage builds the constructed certificates with the shipped translator
(`research/eval-2026-09-30/contract_audit/contract_cases.py`) and checks them: 41 records
through the audit driver plus the 5 Lean-format cases of `lean/test/Adversarial.lean`, 46
certificates, at least one per condition of Table 11, of which 22 are valid edge cases that the
checker accepts with the count that enumeration gives. The records of the run behind the table
are `research/eval-2026-10-07/contract_audit/contract_lean_2026-10-11.txt`; the stage compares
every verdict with them and outputs the column of Table 11.

The summary line `flagged=1 (flag: c24 STREAMDIFF, known)` is expected. The audit driver checks
each text-format certificate twice, with the refutation embedded (Lean core's LRAT checker) and
streamed (lrat-catcher), and flags STREAMDIFF when the two verdicts differ. Case
`c24_empty_hint_r50` contains an addition with an empty hint list. The embedded check accepts
it with the right count (196, as enumeration gives); the streamed check rejects it, because
lrat-catcher treats a step without hints as a RAT step, which fails here. So the streamed
check is less complete on such steps, never unsound, and cpog-gen does not write them. A flag
that would signal a problem is WRONG (accepted with a count other than the enumerated one),
which no record has.

### Other counters (Sections 6 and A.3)

ganak and SharpSAT-TD are not shipped. `artifact/xcheck/counters.tsv` pins the versions used
(GANAK 2.6.3, commit `0b4881b`, with its dependency commits; sharpSAT-TD `0c234c1`), with the
build flags and the command lines. With the two binaries built,

```sh
GANAK=/path/to/ganak SHARPSAT_DIR=/path/to/sharpsat-td/bin artifact/xcheck/xcheck.sh
```

regenerates the four OEIS formulas (exported from the Lean encoders) and the five graphs and
compares the counts of both counters, ganak in deterministic mode (`--prob 0`), with
`artifact/xcheck/expected.tsv` (about 4 minutes). `artifact/xcheck/runs/` contains the outputs
of the paper's runs (`2026-10-01_oeis`, `2026-10-09_graphs`; the graph run used ganak's default
probabilistic caching, with a stated error probability below 5e-27) and of this script
(`2026-10-11_xcheck`, 18 of 18 counts equal, ganak with `--prob 0`).

### Baselines of the ablation (Table 5)

The two reverse-check baselines are in the Lean sources: the top-down evaluation
(`lean/CountCatcherChecker/RevTD.lean`, unverified, not used by the checker) and the earlier
verified sweep per clause (`checkRev` in `lean/CountCatcherChecker/Rev.lean`).
`cd lean && lake build count-catcher-partc` builds the driver `lean/PartcMain.lean`, which
times every method on a node table and a formula (`.lake/build/bin/count-catcher-partc
FILE.pog FORMULA.cnf all`). Its methods and the rows of Table 5: `m4` is the checker's
bit-parallel reverse check (`checkRevKillFast`); `m2` and `m3` are the top-down evaluation
without and with support signatures, and the row "vs. top-down evaluation" uses the faster of
the two; `m1` is the sweep per clause (`checkRev`), the row "vs. sweep per clause"; the job scripts of the measurement are
`scripts/cluster/td_pog.sbatch` and `td_time.sbatch`, its result
`research/eval-2026-10-01/partc_topdown_table.tsv`. The comparison with CPOG's checkers
(Figure 3, Table 4) reads the results of the run of 2026-10-02 in
`research/eval-2026-10-02/rerun_raw/r4_results*.tgz`.

### CPOG's verified checker (Section 4.5)

`research/upstream/` contains the axiom report of the archived cpog-lean-check build
(`axioms_report.lean`, `.out`), a derivation of `False` from one of the two unproved lemmas
(`setf_false.lean`), the proofs of the two checker lemmas that use them as a patch
(`ppa_patch.diff`), the technical note sent to the authors (`setF_lemmas_note.txt`) and the
issue on cpog-check's count (`issue.md`). They need CPOG's own toolchain (Lean 4.4.0-rc1 and
its pinned LeanSAT).

### Results that need the cluster

The following ship as logs and result files, not as stages: all 737 leaves of the order-8
Latin squares, A396728(7) (18.2 GB of Lean memory), queens 14 and the 16×16 grid, the
competition funnel (Tables 8 and 9), the comparison with CPOG's checkers (Figure 3, Table 4),
the peak memory of CPOG's verified checker beyond the comparison's limits, the ablations of
Table 5 and the unshortened refutation, the full differential test with 12.1 million
certificates, and the rerun of the generation failures of 2026-10-11. Their result files under
`research/` feed `scripts/paper_numbers.py`, so the `extras` stage regenerates their numbers
and tables. The Zenodo record's `logs.tar.gz` contains the cluster logs with commit, machine, time
and memory, one directory per group of runs (listed in its `INDEX.md`): `K2` (CPOG's verified checker), `K11` (the OEIS
cross-check of 2026-10-01), `K16` (the run of 2026-10-02: funnel, showcases, validation,
comparison), `K20` (memory of the verified checker), `K22` (reverse-check methods), `K25_K26`
(embedded against streamed, kernel-only check, 2026-10-04), `ovn` (generation modes and
inlining, 2026-10-02), `rerun_gen_2026-10-11` (the rerun of the generation failures) and `scripts/` (the job scripts, with SHA-256). The order-8 records are
in `research/latin8-2026-10-04/`.

`scripts/paper_numbers.py` can also be run directly; it rewrites `PAPER/numbers.tex` and
`PAPER/tables/` in place (the `extras` stage writes to `artifact/out/extras/paper/` instead):

```sh
uv run --no-project scripts/paper_numbers.py
```

Note: `research/eval-2026-10-02/overnight.md`, behind the hybrid-generation macros that the
paper does not use, is not shipped; a rerun replaces those 30 macros in `numbers.tex` by
placeholders and leaves every other number and table unchanged.

## Provenance

The run records under `research/` cite commits of the private development repository. Their
relation to this release:

| Commit | Cited for | Relation to this release |
|---|---|---|
| `68fc568` | the run of 2026-10-02 (the rows of Table 15 dated 2026-10-02) | the same Lean sources and translator before the rename to count-catcher (`McCert` names) |
| `00049c4` | the rename to count-catcher | the Lean sources of `d097449` |
| `d097449` | the differential test of 2026-10-07 | the Lean sources of this release, except that the release has the comments cleaned (`706fce5`, comments only, line counts kept) and the Dedekind-corner development (`aed133e`, not used by the paper) |

The public history starts with this release. Versions:

| Component | Version |
|---|---|
| Lean | v4.30.0 (elan) |
| Mathlib | `c5ea003` |
| lrat-catcher | `b2e8d59` |
| d4 | `333370c`, with GMP 6.3.0 |
| cpog (cpog-gen, cpog-check) | `a97ed85`, plus `tools-src/*.patch` for cpog-gen-fwd |
| CaDiCaL | 3.0.1 |
| drat-trim | `2e3b2dc` |
| uv | 0.12.23 |

## License

count-catcher is licensed under the Apache License 2.0 (`LICENSE`). The third-party
components and their licenses are listed in `NOTICE`; d4 is LGPL-3.0 and ships with its
source, and d4's bundled PaToH library is free for non-commercial research use only.
