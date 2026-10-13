# Acceptance contract, trust audit and differential tests (2026-09-30)

What was checked: which certificates the checker accepts (the supported fragment, for example a
negated root `F = ¬x ∨ ¬y`, `u = x ∧ y`, root `¬u`), and what its trust rests on (logical
soundness, native evaluation with `implemented_by`/`extern`, input interpretation). Checker state:
`lean/McCert` with `checkRevKillFast` in `checkAC` (working tree of 2026-09-30, 15:26 build),
lrat-catcher `0991973`, Lean v4.30.0. Translators: `scripts/cpog2lrat.py` and the native
`tools-src/cpog2lrat` (md5 of `src/main.rs` 578da30f on the Mac and the cluster). Supporting
files: `research/eval-2026-09-30/contract_audit/` (section 5). No checker code was changed.

Where it ran. Hand cases on the Mac (`lake env lean --plugin=… --run AuditMain.lean`). The
differential tests were meant for Slurm, but `cpu-fast` was saturated (706 of 744 CPUs held by
one other user's jobs with 11 h left, 322 of their jobs pending), so they ran on gpu01 (24
parallel tasks, scratch `/home/scratch/szeider/mccert_audit`, removed per task). Slurm was used
for the build of the audit driver (job 113549, `/home1/szeider/mccert/lean_audit`, a copy with
symlinked packages and a copied LRATCatcher; the pipeline's `lean/.lake` was checked unchanged
afterwards) and for the scan of the kept certificates on slurm-cpu01 (job 113755).

## 1. Acceptance contract as implemented

### 1.1 Order of the checks

`checkAll V F pogStr lratStr N` (`lean/McCert/Check.lean`) evaluates, in this order:

1. `cnfWFb V F`: every literal of `F` has a variable below `V`.
2. `parsePogCert pogStr` (`McCert/Pog.lean`): lines `V n`, `r lit`, `p lits 0`,
   `s x y node:k* 0`; any other line, or a missing `V` or `r` line, is a parse failure.
3. `c.pog.V == V`.
4. Part A, `checkNode` for each node `i` (extension variable `V+i`): all arguments below
   `V+i`; product: pairwise disjoint supports via bitsets (`prodFold`, polarity ignored);
   sum: every hint names an earlier node and one of its defining clauses (`hintClause`), and
   `rupStrict [x, y]` refutes `x ∧ y` from exactly these clauses (a contradictory start, as
   in `x ∨ ¬x`, passes).
5. Root in range: `r.1 < V + nodes`.
6. Count: `litCount r · 2^(V − |S(r)|) == N`.
7. Part C, `checkRevKillFast`: `negationFree` (no argument `(v, false)` with `v ≥ V`, and the
   root is an input literal or a positive node), then 63-clause batches: every
   non-tautological clause of `F` must kill the root (`isTaut` clauses are skipped).
8. Part B: `LRATCatcher.checkLratCnf (fwdCnf F P r) lratStr`, i.e. Lean core's
   `parseLRATProof` and `check` on `F ++ defs(P) ++ [¬r]`. Clause numbering is the core
   checker's: clauses by position, tautological clauses of the initial formula dropped
   (`CNF.convertLRAT'` uses `filterMap`), additions stored by position (their IDs are ignored),
   tautological additions skipped.

The streamed route `checkAllAC` runs 1 to 7; part B is then `lrat_stream_cnf` on
`fwdCnfOf F pogStr`.

### 1.2 Cases

Evidence: the hand suite (`contract_cases.py`, output `contract_audit/contract_tools.txt` and
`contract_lean.txt`, 39 records) and the differential tests of section 3. "Translator" means
both translators (byte-identical output and exit code on all cases). "cpog-gen" says whether
D4 + cpog-gen produce the shape (section 1.3).

| Case | Test | Translator | Checker | cpog-gen produces it |
|---|---|---|---|---|
| Negative input literal as argument | c01; all 194,942 base certificates | accepts | accepts | yes, everywhere (12.4 M in the 65 kept MC2022 certificates) |
| Negated edge into an internal node | c02: `F = (x∨y)∧z`, `n1 = ¬x∧¬y`, `n2 = ¬n1∧z`, root `n2`, count 3 | accepts | rejects in part C (`negationFree`); parts A and B pass and part A's count 3 is right | never |
| Negated root node | c03, `F = ¬x∨¬y`, `u = x∧y`, root `¬u`, count 3 | accepts | rejects in part C (`negationFree`), count 3 right | never |
| Constant true (empty product `p u 0`) as root | c04 empty CNF (V=3), c05 only `x∨¬x`, c06 V=0 | rejects: "no root unit clause among the additions" (B1) | accepts with a hand LRAT `k 0 <def> <¬r>`: counts 8, 4, 1; c22: accepts when an addition derives the unit | only as root, for exactly the valid formulas (6,164 in section 3, all count `2^V`) |
| Constant true as a product argument | c18 `p 1 t` with `t = p()` | no case | accepts, count 1 | never (`Pog::optimize` drops true arguments) |
| Constant false (negated empty product) | c07 (V=0, `F` = the empty clause), c08 (`F = x ∧ ¬x`) | cpog-gen gives no certificate | rejects in part C (`negationFree`) | never (cpog-gen aborts) |
| False as `x ∧ ¬x` | c08b, adversarial a4 | accepts | rejects in part A (overlap, C3) | never |
| Sum `x ∨ ¬x` | c17 | no case | accepts (count 2) with core numbering; its tautological defining clause has no position, so DIMACS numbering is rejected in part B | never |
| Non-exclusive sum `true ∨ x` | c19 | no case | rejects in part A (`sum-rup`, C4); unchecked count would be 3, true 2 | never |
| Empty CNF | c04, E0 to E3 size-0 formulas | B1 | accepts (hand LRAT) | yes, root true |
| Zero variables | c06 (count 1), c07 (empty clause, count 0) | B1 / none | accepts c06; c07 as constant false | root true for c06, none for c07 |
| Literal root | c09 root `¬x1` (count 2), c10 root `x2` (count 4) | accepts if an addition derives the root unit | accepts (`r.1 < V` passes `negationFree`) | never; a literal root becomes a one-argument product (24,747 of them in section 3, 0 literal roots) |
| Unused variables in the header | c11; E3u (header 4 over 3 variables); R (header `V+1`, `V+2`) | accepts | accepts; count includes the factor `2^unused` | yes |
| Variable above the header | c16 | not tested | rejects at `cnfWFb` | no (D4/cpog-gen take V from the header) |
| Tautological clauses | c05, c12; E sets; R (4% of clauses) | drops them, shifts IDs, drops hints to them | accepts; part C skips them | cpog-gen deletes them (`d id 0`) |
| Duplicate clauses | c13; E sets are multisets; R (5%) | accepts | accepts | yes |
| Repeated literal in a clause | c14; R (4%) | accepts | accepts (core merges; part C masks are per clause) | yes |
| Empty clause in `F` | c15 (tool chain), c25 (hand POG `x`, count 1) | cpog-gen gives none | rejects in part C (`C-clause1`): the empty clause kills no node | never |
| Root not declared / POG universe ≠ V | c20 / c21 | no case | rejects (root range / `V` check) | never |
| Addition without hints | c23, c24 | writes `k lits 0  0` (two spaces), a parse error in part B (B2) | with one space: embedded part B accepts c24, the stream route rejects it (F-S, section 3.4) | never |
| Adversarial suite `lean/test/adversarial` | 12 certificates | a5, a5b (C4), a9 (C2) rejected | h1 to h3 accepted (2, 3, 6); a4, a14 part A; a6, a8, a10 part C; a7 accepted with the right count 1 | n/a |

### 1.3 What cpog-gen produces

- Source (`tools/cpog/src/pog.cpp`, a97ed85, `Pog::optimize`). Nodes are re-created bottom up;
  a child reference is remapped to a new positive node id, an input literal, or the pseudo-node
  `±true_id`. True arguments of products are dropped, a false argument makes the product
  false, a false child of an OR is replaced by the other child. D4's d-DNNF (`o`, `a`, `t`,
  `f` nodes, literals on edges) has no negated node references, so no negated node literal can
  arise. Root: false gives "Compiled formula unsatisfiable. Cannot verify" and exit 1 (no
  certificate); true gives a single `POG_TRUE` node, written as the empty product `p u 0`,
  whose defining clause `[u]` serves as the root unit (`cpog-gen.cpp`, "Tautology"), so no
  addition derives it; an input-literal root becomes a one-argument product.
- D4 on unsatisfiable input: an `f` node, `s 0`, exit 0; cpog-gen then exits 1 (c07, c08, c15,
  and all 38,067 unsatisfiable formulas of section 3).
- Tautological input clauses: cpog-gen deletes them (`d id 0`, no hints).
- Scans for negated internal edges, negated roots, literal roots, empty products
  (`scan_negation.awk`): the 65 certificates kept on slurm-cpu01 (`/scratch/szeider/mccert_certs`,
  MC2022, 3,554,943 nodes): all zero, no one-argument products. The 7 POGs in `lean/test/data`
  (dom08, dom08t, hq5, ind08, jean, q08, qs08_r2): all zero. The 194,942 translated base
  certificates of section 3 (798,045 nodes, 268,188 sums): no negated internal edge, no
  negated root, no literal root, no empty product (the true-root certificates did not
  translate, B1).
- Proved theorems: all family theorems and the 90 proved MC2022 instances (`mc2022.md`) passed
  part C, so their POGs are negation-free with a positive root.

## 2. Trust audit

### 2.1 Axioms

`#print axioms` (`contract_audit/Axioms.lean`, local build of 15:26):

- `McCert.checkAll_sound`, `McCert.checkAllAC_sound`, `McCert.card_models_eq_countRoot`,
  `McCert.checkPog_sound`, `McCert.checkRevKillFast_sound`, `McCert.fwd_of_unsat`,
  `LRATCatcher.checkLratCnf_sound`: `[propext, Classical.choice, Quot.sound]` each.
- A published theorem adds native-evaluation axioms (from the cluster results): embedded
  `jean_indepSets` adds `jean_indepSets._native.native_decide.ax_1_1`; streamed `queens8` adds
  `queens8._native.native_decide.ax_1_1` (parts A and C) and `queens8_fwd._native.native_decide.ax_1`
  (part B). The streamed theorem also depends on the per-theorem `opaque queens8_fwd_feed`
  (`@[implemented_by LRATCatcher.certFeedImpl]`), which is a constant, not an axiom.

### 2.2 Method

Two closures from the evaluated roots, computed in Lean on the compiled environment:

- `IrAudit.lean` (exact): closure over the IR that the compiler emitted (`collectUsedDecls`),
  extern declarations as leaves, tagged with extern symbol, `unsafe`, `partial`, `opaque`,
  `implemented_by`, `@[export]`, and the callers of the panic primitives. Output `ir_audit.txt`.
  `McCert.checkAll`: 541 IR functions, 93 externs. `checkAllAC` with `fwdCnfOf`: 198 functions,
  52 externs. `LRATCatcher.checkStreamCnf` with `certFeedImpl` and `streamReset`: 475
  functions, 93 externs; all roots together 608 functions. No function in any closure carries
  `@[export]`, and `dbgTrace`, `ptrAddrUnsafe` and `unsafeCast` do not occur in the IR closures
  (`unsafeCast` appears only in the expression-level closure, inside core's `Array.*Unsafe`).
- `ExprAudit.lean` (over-approximation): closure over definition values, `implemented_by`
  targets and `@[csimp]` replacements from `McCert.checkAll` (output `expr_audit.txt`). It lists
  the unproved substitutions: `Array.anyM`, `foldlM`, `foldrM`, `mapM`, `modifyM` →
  `…Unsafe` (USize loops with `unsafeCast`), `Nat.repr` → `Nat.reprFast`,
  `WellFounded.extrinsicFix` → `opaqueFix`. The `@[csimp]` replacements (`List.map` → `mapTR`
  and nine more, `Nat.rec`, `Acc.rec`, `WellFounded.fix`, `Array.instDecidableEq`,
  `String.Slice.Pos.next`) carry equality proofs, so they add only the compiler's use of them.

Extern categories for `checkAll`: Nat 13 (`add sub mul div mod pow land lor shiftLeft
shiftRight decEq decLt decLe`, GMP-backed), Int 8, Array 18, ByteArray 4, String 18, UInt8/32/64
and USize 30, `System.Platform.getNumBits`, `panicCore`. The stream route adds `IO.FS.Handle.mk`,
`read`, `getLine`, `IO.getEnv`, `ST.Prim.mkRef`, `Ref.get`, `Ref.set`, `ByteArray.copySlice`,
`emptyWithCapacity`, `validateUTF8`, `String.ofByteArray`, `UInt8.ofNatLT`.

### 2.3 (a) lean/McCert

- Source: no `extern`, `implemented_by`, `@[export]`, `unsafe`, `partial`, `opaque`,
  `panic!`, `dbg_trace`, `IO`, `initialize`, `unsafeCast`, `ptrAddr`, `csimp` (grep over the 8
  files; positive control: 71 `def` matches). All code is ordinary `def`s over `Nat`, `List`,
  `Array`, `String`.
- Implicit panics: `get!`/`[i]!` in `litSupp`, `litSize`, `litCount` (Pog), `litSat`, `nodeSat`,
  `occMask`, `reqMask`, `litKill` (Rev), `addBatchOcc` (`cs[j]!`), `set!` in `clearClauseOcc`
  (RevFast). Logic: out of bounds gives `default`. Native: `lean_array_get_panic` prints a
  message and returns the same `default` (or aborts under `LEAN_ABORT_ON_PANIC`, which yields
  no theorem). In an accepted run no index is out of bounds: arguments are checked `< V+i` before
  part A reads them, part C runs only after part A accepted, and `cnfWFb` bounds `litIdx < 2V`.
  Soundness assumes nothing beyond "native `get!` returns the logical default".
- Arithmetic: all indices, IDs, supports (bitsets), masks and counts are `Nat`; no fixed-width
  parsing or ID arithmetic in McCert. Masks stay below `2^63` by the batch size (performance
  only).
- `parsePogCert` runs natively inside `checkAll`; `checkAll_sound` holds for every parse result,
  so its format fidelity is not trusted, only its compilation (as for all code below).

### 2.4 (b) lrat-catcher (`lean/.lake/packages/LRATCatcher`, read only)

- `checkLratCnf` (Reflect): `parseLRATProof lratStr.toUTF8` then core `check`; theorem
  `checkLratCnf_sound`. No annotations.
- Stream reader (StreamOracle), used by `lrat_stream_cnf`:
  - `certFeedImpl : Nat → Option (Array IntAction)` is `unsafe` and runs `unsafeIO`. State in five
    `initialize`d `IO.Ref`s (handle, path override, block index, leftover bytes, binary flag);
    reads `LRATCATCHER_STREAM_PATH` (unless `streamReset` set a path) and
    `LRATCATCHER_STREAM_BLOCK` (lines per block, default 4096). The first byte selects binary
    (`a`/`d`, core `Parser.Binary.parseAction` per action) or text (`bl` lines by
    `Handle.getLine`, then core `parseLRATProof`). Every action goes through `normalizeAction`.
    An out-of-order block request, a read error or a parse error returns `none`, which makes
    the check false. `first[0]!` and `c[0]!` are guarded by size checks.
  - The theorem is `checkStreamCnf_sound F feed streamFuel (by native_decide)` with a fresh
    `@[implemented_by certFeedImpl] opaque feed` per theorem. `checkStreamCnf_sound`
    quantifies over all feeds, so the reader's output is not trusted. Assumed: the compiled
    `checkStream` asks for each block index once and in order (the index guard turns any other
    access into a rejection), so the observed blocks define a value of the opaque constant
    under which the native axiom is true; per-theorem constants keep the axioms of several
    streamed theorems jointly satisfiable.
  - Completeness only: `normalizeAction` rewrites a hint-less RUP addition into a RAT step with
    no candidates; the core check accepts some hint-less RUP steps, so the stream route can
    reject what the embedded route accepts (F-S, 71 cases in section 3; never on cpog-gen
    output). Block size does not matter (1, 2, 3 and 4096 lines in section 3, 1 and 4096 on the
    hand suite; truncated and corrupted streams are rejected, `test/Queens8Stream.lean`).
- Not on McCert's path: kernel mode, cover and cube composition, snapshots and compaction
  (`checkStreamCnfC`), `validateDimacs` (only in the `lrat_reflect` commands).

### 2.5 (c) Lean core LRAT checker (`Std.Tactic.BVDecide.LRAT`, v4.30.0, read only)

- `check` = `compactLratChecker (CNF.convertLRAT cnf) proof = .success`; `check_sound` is
  proved in core (standard axioms, `LRATCatcher.checkLratCnf_sound` depends on nothing else).
- Parser: `Text.parseActions.go`, `Binary.parseLit.go`, `manyTillZero.go`,
  `manyTillNegOrZero.go` and `Std.Internal.Parsec.ByteArray.digitsCore.go` are `partial`,
  i.e. opaque constants with compiled implementations. Their logical value is unspecified;
  soundness holds for every parse result; the only assumption is that the implementation
  behaves as a function on the given input. Numbers are parsed as `Nat` (no fixed width). The
  text grammar is strict: one space between tokens, a newline after every line, `c` comment
  lines; hence B2.
- Checker internals use `get!`, `set!` and `Array.modify` on the assignment and clause arrays
  (callers of the panic primitives are listed in `ir_audit.txt`); same argument as in 2.3.
- Numbering (completeness): tautological initial clauses are dropped by `filterMap`,
  `intActionToDefaultClauseAction` skips tautological additions and additions with a literal
  out of range; addition IDs are ignored, deletions and hints address positions. The
  translators follow this since the fix of 2026-09-30 (`mc2022.md`).

### 2.6 Classification

Trusted for soundness:

- T1 Lean kernel with `propext`, `Classical.choice`, `Quot.sound`.
- T2 Native evaluation (one axiom per embedded theorem, two per streamed theorem): the compiled
  code of everything in the IR closure computes its logical definition. This covers the Lean
  compiler (LCNF, IR, C, clang), the runtime, the 93 (stream: 93, AC: 52) externs listed in
  `ir_audit.txt` (GMP `Nat`, arrays, strings, fixed-width integers), the unproved
  `implemented_by` substitutions of core (2.2), panics returning `default`, and the IR
  interpreter for code that is not precompiled (the family encoders in McCertMath, the
  auxiliary definition of `native_decide`). Partial parser functions need only functionhood.
- T3 Streamed theorems: a fresh opaque feed per theorem and in-order block requests (2.4).
- T4 Build consistency: the shared libraries passed with `--plugin`
  (`libMcCert_McCert.so`, `libLRATCatcher_LRATCatcher.so`) must come from the same sources as
  the imported `.olean`s; Lake builds both from one content-hashed trace, a hand-copied or
  partially rebuilt library would break T2.
- T5 The statement: `F` and `V` are Lean terms. Family encoders are covered by the family
  lemmas; DIMACS theorems are about `LRATCatcher.parseDimacs D`, whose lenient rules (lines not
  starting with a digit or `-` ignored, non-integer tokens ignored, missing final `0` tolerated)
  are part of what the theorem means.

Not trusted (a fault can only cause a rejection): D4, cpog-gen, both translators,
`theorem_lean.py` and `e2e.sbatch` (the kernel checks the emitted theorem; its statement must be
read), the format fidelity of `parsePogCert` and `parseLRATProof`, the content delivered by the
stream reader, the LRAT and POG files.

Completeness or performance only: partial parsers and the strict text grammar, `normalizeAction`,
tautology numbering, stream block size, panics in rejected runs, the 63-clause batch size, the
`count_models` command's meta-level `evalExpr` (it runs at elaboration time; the kernel checks the
emitted term; the command is work in progress and was not audited here).

Audit list of the checker's design notes: `implemented_by`/`extern` done (2.2); unsafe casts only inside
core's `Array.*Unsafe` implementations; fixed-width parsing and ID arithmetic: none in McCert,
`Nat` in the core parser, bounds-checked `USize` indexing; snapshot renumbering not on the path;
stale build artifacts: T4; stream-reader inputs: 2.4.

## 3. Differential tests

### 3.1 Setup

- Formula sets (`difftest.py`, deterministic): E0 to E3, all multisets of clauses over
  V = 0 to 3 variables, a clause being any set of literals of width at most 2 (V ≤ 2) or 3
  (V = 3), tautologies and the empty clause included: E0 up to 2 clauses (3 formulas), E1 up to 6
  (210), E2 up to 6 (12,376), E3 up to 4 (163,185); E3u, every 8th E3 formula with header 4
  (20,399); R, 40,000 random formulas, V 4 to 8, header `V + {0,1,2}`, m 0 to 4V, widths 0 to 4,
  4% tautologies, 4% repeated literals, 5% duplicate clauses; RB, 3,000 random formulas with
  V 10 to 13 and m 64 to 130, widths 3 to 5 (2,757 certificates need two part-C batches, 159
  three). Total 239,173 formulas.
- Per formula: bit-parallel brute-force count (Lean semantics: variables above the header are
  false), D4 `-dDNNF`, cpog-gen, native translator, each in a private working directory. Every
  translated certificate becomes a record; 5% also with `--delete`; 2% of the certificates and
  CPOG mutants also through `cpog2lrat.py` for comparison.
- Mutants of every translated certificate, one per kind (E sets) or two (R, RB): 9 POG kinds, 7
  LRAT kinds, 4 formula kinds (the certificate checked against a changed formula), 7 CPOG kinds
  (through the translator). Expected value of a record: the brute-force count of the formula it
  is checked against.
- Lean: `mccert-audit` (`AuditMain.lean`), one process per shard, 48 shards. Per record it
  evaluates `checkAll V F pog lrat N` with `N` = part A's count, and the streamed route
  `checkAllAC V F pog N && checkStreamCnf (fwdCnfOf F pog) certFeed streamFuel` through the real
  stream reader (block size 1, 2, 3 or 4096 lines by shard). It replays the stages to name the
  first failing one and computes Lean's `modelCount` (V ≤ 16). Flags: WRONG (accepted, count ≠
  brute force), BFDIFF, DIAGDIFF, STREAMDIFF, CDIFF (per-clause part C ≠ bit-parallel). Positive
  control: a valid certificate with a false expected value is flagged WRONG.
- Cost: 11.3 CPU-hours of tool runs, 27 minutes of Lean for 5.57 M records; 35 minutes wall on
  24 cores of gpu01. Results: `/home1/szeider/mccert/lean_audit/results/` (33 MB gzip; per record
  verdict and stage in `SET_SHARD/lean.out.gz`, tool outcomes in `tools.tsv.gz`).

### 3.2 Base formulas

| Set | Formulas | Certified and accepted | Unsatisfiable (cpog-gen refuses) | Valid, translator rejects (B1) |
|---|---:|---:|---:|---:|
| E0 | 3 | 0 | 2 | 1 |
| E1 | 210 | 42 | 161 | 7 |
| E2 | 12,376 | 4,876 | 7,472 | 28 |
| E3 | 163,185 | 141,220 | 18,089 | 3,876 |
| E3u | 20,399 | 17,642 | 2,268 | 489 |
| R | 40,000 | 28,246 | 9,991 | 1,763 |
| RB | 3,000 | 2,916 | 84 | 0 |
| total | 239,173 | 194,942 | 38,067 | 6,164 |

- D4's count equals the brute-force count on all 239,173 formulas.
- Every satisfiable formula that is not valid got a certificate, and the Lean checker accepted
  all 194,942 of them and the 9,778 `--delete` variants, each with the brute-force count, in both
  routes. No base certificate was rejected, so there is no evidence of a completeness bug of
  the checker on cpog-gen output.
- Every formula the translator rejected is valid (count `2^V`, root = empty product): B1.
- Translator comparison: 28,708 identical outputs and 6,194 identical rejections, no difference.

### 3.3 Mutants

| Kind | Mutation | Records | Accepted | Rejected by stage |
|---|---|---:|---:|---|
| mp_flip_arg | POG: negate one node argument | 222,545 | 0 | C-clause 111,741, A-sum-rup 96,199, C-negation 14,066, B 539 |
| mp_change_arg | POG: random earlier literal as argument | 188,388 | 2 | A-prod-overlap 68,679, A-sum-rup 62,448, C-clause 47,870, C-negation 6,285, B 3,104 |
| mp_drop_arg | POG: drop a product argument | 221,504 | 0 | C-clause 160,492, A-sum-rup 60,227, B 785 |
| mp_add_arg | POG: add a product argument | 225,800 | 0 | A-prod-overlap 171,667, B 42,168, A-sum-rup 11,903, C-negation 62 |
| mp_root_neg | POG: negate the root | 194,942 | 0 | C-negation 194,942 |
| mp_root_change | POG: random root | 187,737 | 3,255 | C-clause 133,426, C-negation 28,988, B 22,068 |
| mp_sum_hint | POG: drop, replace or add a sum hint | 146,677 | 31,356 | A-sum-rup 100,165, A-sum-hint-ref 15,156 |
| mp_kind_swap | POG: sum ↔ binary product | 157,276 | 0 | A-sum-rup 97,958, A-prod-overlap 59,318 |
| mp_dup_node | POG: duplicate a node line | 216,053 | 0 | B 139,313, A-sum-rup 50,846, C-clause 25,097, A-prod-overlap 797 |
| ml_drop_hint | LRAT: drop a hint | 224,602 | 86,538 | B 138,064 |
| ml_change_hint | LRAT: replace a hint | 207,890 | 52,007 | B 155,883 |
| ml_flip_lit | LRAT: negate a literal of an addition | 169,978 | 88 | B 169,890 |
| ml_drop_lit | LRAT: drop a literal of an addition | 169,847 | 58,204 | B 111,643 |
| ml_add_lit | LRAT: add a literal to an addition | 225,713 | 43,824 | B 181,889 |
| ml_drop_line | LRAT: drop an addition | 222,456 | 0 | B 222,456 |
| ml_swap_lines | LRAT: swap two additions | 224,254 | 980 | B 223,274 |
| mf_drop_clause | formula: drop a clause | 226,104 | 60,161 | B 165,943 |
| mf_add_clause | formula: add a random clause | 226,104 | 0 | C-clause 157,116, B 68,988 |
| mf_flip_lit | formula: negate a literal | 226,104 | 41,445 | C-clause 153,535, B 31,124 |
| mf_drop_lit | formula: drop a literal | 225,493 | 75,175 | C-clause 138,039, B 12,279 |
| mc_decl_flip | CPOG: negate a declaration argument | 226,104 | 0 | C-clause 113,500, A-sum-rup 97,587, C-negation 14,445, B 572 |
| mc_decl_change | CPOG: replace a declaration argument | 220,505 | 21,444 | A-prod-overlap 68,824, A-sum-rup 64,323, C-clause 56,446, C-negation 6,363, B 3,105 |
| mc_decl_drop | CPOG: drop a product argument or sum hint | 225,554 | 0 | C-clause 127,785, A-sum-rup 97,769 |
| mc_add_drop_hint | CPOG: drop a hint of an addition | 226,104 | 48,194 | B 177,844, B-parse 66 |
| mc_add_change_hint | CPOG: replace a hint of an addition | 206,542 | 22,677 | B 183,864, B-parse 1 |
| mc_add_flip_lit | CPOG: negate a literal of an addition | 143,443 | 103 | B 143,340 |
| mc_root_change | CPOG: negate or replace the root | 5,780 | 214 | C-clause 5,566 |

B = part B check failed. CPOG mutants rejected by the translator are not Lean records:
`mc_root_change` 211,068 and `mc_add_flip_lit` 82,661 ("no root unit clause"), `mc_decl_drop`
550 ("cites no earlier clause").

### 3.4 Result and classification

- 5,568,219 Lean records, 750,387 accepted (194,942 base, 9,778 delete, 545,667 mutants). **No
  accepted record has a count different from the brute-force count, in either route.** No
  BFDIFF, DIAGDIFF or CDIFF.
- Accepted mutants are harmless variants: redundant hints and literals, a dropped clause that
  the formula implies, a root literal or a sum hint set equivalent to the original, and so on;
  all have the right count by the check above.
- Rejections: every mutant rejection is caused by the mutation. The stages show each
  acceptance condition at work: C3 overlap and C4 exclusion in part A, the negation-free
  restriction and the kill test in part C (7,359 kill rejections at clause index ≥ 63, i.e. in
  a later batch), RUP in part B. Rejections at C-negation are outside the documented fragment
  (a negated edge or root introduced by the mutation); none of the base certificates is.
- F-S (stream route less complete than embedded): 71 records, all `ml_drop_hint` of set R,
  accepted embedded and rejected streamed; none in the other direction. Cause:
  `normalizeAction` (2.4). Example: R:50, step `48 14 1 2 0` after the unit `14` of step 47;
  with the hint dropped the core check accepts the step (asserting `¬14` meets the unit `14`),
  the stream route turns it into a RAT step that fails. Reproduction: hand case c24
  (`contract_audit/cases/c24_r50_nohint.cpog`).
- B-parse (67 records): an addition whose hints were all dropped is written with two spaces
  (B2).

### 3.5 First run with a shared working directory

The first run (5,107,305 records, results kept in `lean_audit/results_run1/`) started the
tools in one shared working directory. cpog-gen writes its SAT-solver files
`reduction-N.cnf` and `reduction-N.lrat` into the working directory with a per-process counter,
so parallel cpog-gen processes read each other's proofs: 369 RB and 3 R formulas failed in
cpog-gen with an error, 46 RB with "Failed to justify root literal", and one certificate (R:835)
passed the translator with hints from another process's proof. The Lean checker rejected it in
part B; rerun alone, the same formula gives a certificate that is accepted. No accepted record of
that run had a wrong count either. The second run (section 3.2 to 3.4) gives every task its own
directory; `e2e.sbatch` already works in a per-job scratch directory.

## 4. Acceptance contract and findings

The checker accepts a formula $F$ over the variables $0,\dots,V-1$, a POG file, an LRAT file and a count $N$ exactly when both files are well-formed and the following conditions hold. Every literal of $F$ lies in the universe; variables that occur in no clause are allowed and counted, and duplicate clauses, tautological clauses and repeated literals need no preprocessing. Node $i$ defines the extension variable $V+i$ as a product of any number of literals or as a sum of two literals, all over earlier variables. The arguments of a product have pairwise disjoint supports, with polarity ignored, so that $x \land \lnot x$ is rejected, and the exclusion $\lnot x \lor \lnot y$ of a sum $x \lor y$ follows by unit propagation from cited defining clauses of earlier nodes alone. No argument of a node is a negated node, and the root $r$ is an input literal of either polarity or an unnegated node. The LRAT file refutes $F \land \mathrm{defs} \land \lnot r$ in the clause numbering of the LRAT checker of Lean's standard library, and every non-tautological clause of $F$ kills the root: propagation through the nodes finds the root unsatisfiable once the literals of the clause are set to false. The count is then $N = c(r) \cdot 2^{V-|S(r)|}$. The constant true, an empty product, belongs to this fragment, which thus covers the empty formula, formulas over no variables and formulas whose clauses are all tautologies. The constant false requires a negation and does not belong to it: no certificate in the fragment yields count 0, and a formula that contains the empty clause fails the reverse check, so count 0 is proved from a plain LRAT refutation of $F$ instead. cpog-gen stays inside the fragment: it writes neither negated edges nor a negated root and produces no certificate for an unsatisfiable formula.

(The paragraph describes the checker. B1 and B2 are fixed since 2026-09-30, so the pipeline
reaches the checker on valid formulas too.)

Findings. No soundness bug was found: every accepted certificate, hand-made, generated or
mutated, gave the brute-force count, and the soundness theorems use the standard axioms only.

- B1 (translator, completeness): valid formulas (count `2^V`: empty CNF, V = 0 without clauses,
  only tautological clauses) are rejected with "no root unit clause among the additions". cpog-gen
  makes the root the empty product `p u 0` and uses its defining clause `[u]` as the root unit, so
  no addition derives it. Minimal reproduction: `p cnf 1 0`, then D4, cpog-gen (CPOG `r 2`,
  `1 p 2 0`), `cpog2lrat` exits 1; both translators. 6,164 formulas in section 3. The checker
  accepts the certificate once the final step is `k 0 <id of [u]> <id of ¬r> 0` (c04 to c06).
  Fix in both translators: when no addition is the root unit and the root is an empty-product
  node, use its defining clause as `root_unit`.
- B2 (translator, completeness): an addition with an empty hint list is written as
  `k lits 0  0` (two spaces; also possible for an empty literal list), which the core text
  parser rejects, so part B fails for the whole file. cpog-gen output never has such steps
  (0 of 194,942). Reproduction: c24. Fix: join tokens with single spaces.
- Status 2026-09-30: B1 and B2 fixed in both translators (Python and native byte-identical;
  old and new native byte-identical on every certificate outside B1). Regression test
  `lean/test/CountValid.lean`: empty formula (8), V = 0 (1), tautology only (4, embedded and
  streamed), c24 with single spaces (196).
- B3 (front end, completeness): `count_models` with a DIMACS file rejects a file without clauses
  (`p cnf 3 0`): lrat-catcher's `validateDimacs` requires the last integer token to be a clause
  terminator. The term form (`count_models n (.empty) (V := 3) ...`) proves it. Fixed in lrat-catcher v0.2.0 (`b2e8d59`, 2026-09-30); mccert pins it, and `lean/test/CountValid.lean` checks both DIMACS files.
- F-S (lrat-catcher, completeness): the stream route rejects hint-less RUP steps that the
  embedded route accepts (`normalizeAction`; its docstring's premise that such steps always fail
  in core is false). Never on cpog-gen output. Reproduction: c24 with single spaces.
- D1 (documentation): the design notes of the time said that part C uses "conditioned
  support-local counts otherwise"; the code rejects every POG outside the negation-free fragment
  (`McCert/Rev.lean` says the fallback is not implemented).
- L1 (fragment, by design): negated edges, negated roots and the constant false are outside the
  fragment (c02, c03, c07, c08); the counts part A computes for them are right, so the
  conditioned-count fallback would be a pure completeness extension. Count 0 needs the LRAT
  route (`McCertMath/Families/Unsat.lean`, `card_eq_zero_of_unsat`).
- O1 (operations): cpog-gen must run in a private working directory (3.5). Parallel runs in one
  directory corrupt proofs; the checker rejects the result, but the cpog-gen failures look like
  tool limits.

## 5. Files

In `research/eval-2026-09-30/contract_audit/`:

- `AuditMain.lean`: the driver `mccert-audit BUNDLE [TMPDIR]` (bundle format in its header);
  on the Mac `lake env lean --plugin=… --run`, on the cluster a `lean_exe` in `lean_audit`.
- `contract_cases.py`, `cases/`: the hand suite; `contract_tools.txt`, `contract_lean.txt`: its
  output.
- `difftest.py`, `audit_task.sh`, `run_gpu01.sh`, `audit.sbatch`, `worklist.txt`,
  `build_audit.sbatch`, `summarize.py`: section 3.
- `IrAudit.lean`, `ir_audit.txt`, `ExprAudit.lean`, `expr_audit.txt`, `Axioms.lean`: section 2.
- `scan_negation.awk`, `scan_certs.sbatch`: section 1.3 (scan output
  `/home1/szeider/mccert/lean_audit/results_scan.txt`).

Reproduce section 3: rsync `lean/` to `lean_audit` (without `.lake`, packages symlinked,
LRATCatcher copied), append the `mccert-audit` exe to its `lakefile.toml`, `sbatch
audit/build_audit.sbatch`, then `run_gpu01.sh audit/worklist.txt 24` on gpu01 or
`sbatch --array=0-47%16 audit/audit.sbatch` on Slurm, then `summarize.py results`.
