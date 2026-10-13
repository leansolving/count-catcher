# Latin squares of order 8: the certified count, collected 2026-10-04

Run on b501 (EPYC 7402), private copies `lean_latin8/`, `tools_latin8/` (sources of commit
d8512d4), run directory `/home1/szeider/mccert/latin8` (archived to
`/home1archive/szeider/projects/mccert/latin8/` on collection), inlined pipeline
(`cpog-gen-fwd -F -T 500 -G`, `cpog2lrat --delete --keep --binary --inline`), arrays 121333
(368 leaves up to 150 MB .nnf, throttle 2, 20 GB) and 121334 (369 leaves, throttle 6, 48 GB),
assembly 121335 (64 GB). Started 2026-10-02 13:56, last leaf 2026-10-04 before 03:00, assembly
after. The 46 leaves of the earlier non-inlined configuration are in `res_noinline` (record only).

## Result

- `latin8c_reduced : Nat.card {L : Fin 8 → Fin 8 → Fin 8 // IsReducedLatin L} = 535281401856`
- `latin8c_all : Nat.card {L : Fin 8 → Fin 8 → Fin 8 // IsLatin L} = 108776032459082956800`
  (`rw [Latin.card_latin_eq, latin8c_reduced]; decide`)
- Axioms: `propext`, `Classical.choice`, `Quot.sound` and 1,474 `native_decide` axioms (two per
  streamed leaf), no `sorryAx` (`lean.out`).
- Method: 7 fibres by the cycle type of the second row (`Latin.card_eq_of_classes`, side
  conditions by `decide +kernel`), each sub-split by the values of the cells (2,1), (2,2), (2,3)
  of the third row into 93 to 113 parts (`fibre_card_eq_of_cells`), 737 leaves in all; every
  leaf count equals D4's and the plan's, and the per-class sums equal the fibre counts of
  `assemble.txt`. Sum over classes of class size times fibre count = 535,281,401,856, the known
  number of reduced squares (Wells 1967).

## Resources (sums over the 737 leaves unless stated; `res/<leaf>.txt`)

| quantity | value |
|---|---:|
| CPOG certificates (before translation) | 7.93 TB (median leaf 10.1 GB, largest c3_0092 32.7 GB) |
| LRAT (binary, inlined) | 2.42 TB |
| POG node tables | 118 GB |
| D4 | 10.1 h (max 140 s) |
| cpog-gen | 135.1 h (max 1,941 s, 8.2 GB RSS) |
| cpog2lrat | 32.7 h (max 483 s) |
| Lean (leaves) | 90.3 h (median 417 s, max 1,342 s; RSS median 9.3 GB, max 21.6 GB) |
| export | 2.2 h |
| assembly | 80.9 s, 11.5 GB RSS |
| keep mask | median 7.9 percent of the initial clauses loaded |
| oleans of the leaves | 141 GB on b501 `/scratch/szeider/latin8/mod` (needed only to rerun the assembly) |

Files here: `assemble.txt`, `lean.out` (`#print axioms`), `T.lean` (assembly file), `plan.json`,
`plan.tsv`, `assign.tsv`, `classes.tsv`, `res/` (737 leaf result files and Lean outputs). The
cluster bookkeeping of the run (`jobs.txt`, `env.sh`, `status.sh`, `tier_*.txt` and the copy of
the driver as run) is in the archive; the driver is `scripts/cluster/latin_cycles.sbatch`.
Paper macros: `scLatinEight*` in `PAPER/numbers.tex` (`scripts/paper_numbers.py`, `LATIN8_DIR`).
