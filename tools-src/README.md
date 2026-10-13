# tools-src

Licence: `cpog2lrat/` is ours, Apache-2.0 (the repository's `LICENSE`). The two patch files
modify cpog-gen from rebryant/cpog (MIT, Randal E. Bryant); as derived works of that code they
carry cpog's MIT terms, and a cpog-gen built with them stays under cpog's licence.

- `cpog2lrat/`: native translator from a CPOG certificate to the LRAT refutation and POG file
  of the Lean checker (same output as `scripts/cpog2lrat.py`); build with `build.sh`. Option
  `--trim` (default in the drivers) writes only the additions the empty clause depends on, found
  by one backward pass over the certificate; `--keep` (implies `--trim`) also writes OUT.keep, the
  mask of the initial clauses that part B loads (`fwdCnfOfSel`), and numbers the LRAT for it.
  `difftest.sh` checks both against `scripts/lrat_trim.py`. `--inline` (implies `--trim`, works
  with `--keep`) also replaces each addition that only one kept step, at most 4096 kept additions
  later, cites by its own hint list where a replay with Lean core's hint rule accepts it (one
  streaming pass; reference `scripts/lrat_inline.py`, checked by `difftest.sh`). It made Lean's
  part B 1.3x to 2x faster on queens, domino, grid and MC2022 samples (Mac, 2026-10-02); since
  2026-10-02 the drivers turn it on wherever the proof is streamed (`INLINE` defaults to `MASK`
  in e2e.sbatch; `INLINE=0` or `--no-inline` turn it off) and leave embedded certificates alone.
- `cpog-gen-noreverse.patch`: adds option `-F` (forward implication only) to cpog-gen of
  rebryant/cpog a97ed85. With `-F` cpog-gen stops after the root unit: it writes neither the
  deletions of the derived clauses nor the input-clause deletions, and it no longer keeps the
  copy of every hint list that the derived-clause deletions need. Everything before the
  deletions is byte-identical: the `-F` certificate equals the default certificate with its
  `d` lines removed. Without the input-clause deletions cpog-gen no longer detects an
  overcount; count-catcher checks the reverse implication by evaluation (part C), so neither the
  translators nor the Lean checker read any deletion. Default off.
  Build (Mac: `make CC=clang CXX=clang++`, with
  `DEVELOPER_DIR=/Library/Developer/CommandLineTools` if the Xcode license has not been accepted):
  `mkdir tools/cpog-norev && (cd tools/cpog && git archive a97ed85 src) | tar -x -C
  tools/cpog-norev && cd tools/cpog-norev && git apply ../../tools-src/cpog-gen-noreverse.patch
  && cd src && make cpog-gen`, then copy the binary to `tools/bin/cpog-gen-norev` next to
  `cpog-gen` (on our cluster: `/home1/szeider/mccert/tools/bin/cpog-gen-norev`). Measurements:
  `research/eval-2026-09-30/cpoggen_noreverse.md`.
- `cpog-gen-fwd.patch` (on top of the noreverse patch): `cpog-gen-fwd`, new options default off,
  certificates byte-identical to `cpog-gen-norev` without them. `-T LEMS`: a SAT call below the
  `-t` problem size whose CaDiCaL proof has at least LEMS lemmas goes through drat-trim (trimmed,
  hinted) instead of cpog-gen's own re-hinting; `-t` and the BCP bound are unchanged (measured
  choice `-T 500`: MC2022 track1_023 17 s to 1.6 s, queens up to 12 and domino 10x10
  untouched). `-G` (needs `-F`): free the proof clauses that no later step can read (collector
  at each node visit). `-M N` (experimental, 2026-10-02): hybrid generation. A node whose
  subgraph has tree size at most N (children counted with multiplicity) is justified by one SAT
  call on the reduced active clauses plus the subgraph's defining clauses (as a literal
  justification: the proof is lifted into the context) instead of by recursion; a shared entry
  point keeps its lemma, a failed call falls back to recursion, `-G` rebuilds freed defining
  clauses. `-W K` gates it: recursion until K justifications are done and the SAT calls reach
  one per 1000 of them; a POG within the limit as a whole is one call. Mac, `-F -T 500 -G`,
  structural against `-M 10000 -W 100`: 10/11/12-queens 6.6/29.6/167 s to 0.6/3.1/18.7 s and
  11.5/62/406 MB to 2.9/12/70 MB, domino 10x10 31.4 s to 9.5 s, MC2022 track1_087 4.0 s to
  1.1 s (37 to 5.6 MB), track2_023 8.3 s to 8.2 s (64 to 28 MB); grids and track1_037 (no
  SAT call, so the gate stays closed) byte-identical; counts correct everywhere, 12-queens and
  q11, dom10, track2_023 proved in Lean. Not safe in general: MC2022 track2_019 makes SAT calls
  but reuses its 2,365 lemmas 21,174 times, which separate SAT calls cannot, and is 6.5x
  slower and 5x larger at every N (no rule found that predicts this). So the robust use is a
  race against the structural mode (drivers: `GEN=race`, contender `GEN_RACE=hybrid`, run as
  `-M 10000` without the gate); `GEN=hybrid` uses the gated form.
  Unconditional: two leaks fixed (a matched lemma instance in `Pog::apply_lemma`, the saved
  active-clause set of every partitioned product). Build as cpog-gen-norev into `tools/cpog-fwd`,
  applying both patches (`git apply ../../tools-src/cpog-gen-noreverse.patch
  ../../tools-src/cpog-gen-fwd.patch`), then copy `src/cpog-gen` to `tools/bin/cpog-gen-fwd`.
