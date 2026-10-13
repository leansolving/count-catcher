**Summary.** On some certificates with a large model count (10^18 and above in our runs), `cpog-check` accepts the certificate ("FULL-PROOF SUCCESS. CPOG representation verified") but prints a count that is wrong from about the tenth significant digit on. The certificate is correct: D4, `cpog-lean-check -c` of the same release and an independent exact evaluation of the declared POG agree on the true count. Only the printed count is affected, not the equivalence verdict. The cause is in the normalization of the checker's rational numbers (`src/q25.c`, below), and a one-line change fixes it.

**Versions.** cpog a97ed85 (tagged v1.1.0 and v1.2.0), D4 (crillab/d4) 333370c, CaDiCaL 3.0.1, drat-trim 2e3b2dc; reproduced on macOS arm64 (clang 17) and on Linux x86_64 (GCC 13 and 14).

**Extent.** In a comparison of the two checkers on 91 certificates written by the `cpog-gen` of the same release from D4 outputs (82 formulas of the 2022 Model Counting Competition and 9 instances of our own families), `cpog-lean-check` reported the correct count on all 91 and `cpog-check` on 84; the 7 wrong counts are on large counts only (independent sets of random cubic graphs with 100 and 120 vertices, of the 14 x 14 grid and of the graph homer, and mc2022 track1_031, track2_027, track2_035). On track2_027 the printed count differs from D4's and from `cpog-lean-check`'s in the 31st digit.

**Smallest case** (independent sets of a random cubic graph on 100 vertices, 100 variables, 150 binary clauses; the CNF is below): true count 8,281,581,627,129,350,099 (D4, `cpog-lean-check`, exact POG evaluation); `cpog-check` prints 8,281,581,627,129,036,755 with FULL-PROOF SUCCESS.

<details>
<summary>cub100.cnf</summary>

```
c independent sets of cub100 (cubic 100 1)
p cnf 100 150
-1 -28 0
-1 -33 0
-1 -34 0
-2 -25 0
-2 -72 0
-2 -83 0
-3 -4 0
-3 -11 0
-3 -79 0
-4 -61 0
-4 -95 0
-5 -25 0
-5 -63 0
-5 -91 0
-6 -42 0
-6 -50 0
-6 -69 0
-7 -16 0
-7 -86 0
-7 -93 0
-8 -40 0
-8 -84 0
-8 -94 0
-9 -61 0
-9 -94 0
-9 -97 0
-10 -43 0
-10 -91 0
-10 -94 0
-11 -66 0
-11 -93 0
-12 -95 0
-12 -98 0
-12 -100 0
-13 -32 0
-13 -60 0
-13 -81 0
-14 -24 0
-14 -57 0
-14 -59 0
-15 -46 0
-15 -86 0
-15 -97 0
-16 -53 0
-16 -90 0
-17 -40 0
-17 -49 0
-17 -73 0
-18 -25 0
-18 -44 0
-18 -49 0
-19 -50 0
-19 -55 0
-19 -75 0
-20 -22 0
-20 -51 0
-20 -88 0
-21 -37 0
-21 -70 0
-21 -99 0
-22 -76 0
-22 -84 0
-23 -37 0
-23 -88 0
-23 -89 0
-24 -34 0
-24 -41 0
-26 -35 0
-26 -54 0
-26 -90 0
-27 -30 0
-27 -64 0
-27 -77 0
-28 -38 0
-28 -99 0
-29 -63 0
-29 -68 0
-29 -85 0
-30 -49 0
-30 -82 0
-31 -42 0
-31 -58 0
-31 -60 0
-32 -68 0
-32 -80 0
-33 -56 0
-33 -76 0
-34 -50 0
-35 -37 0
-35 -67 0
-36 -45 0
-36 -54 0
-36 -74 0
-38 -73 0
-38 -81 0
-39 -59 0
-39 -62 0
-39 -78 0
-40 -92 0
-41 -57 0
-41 -59 0
-42 -76 0
-43 -65 0
-43 -72 0
-44 -89 0
-44 -95 0
-45 -61 0
-45 -62 0
-46 -80 0
-46 -96 0
-47 -54 0
-47 -71 0
-47 -87 0
-48 -51 0
-48 -65 0
-48 -84 0
-51 -57 0
-52 -66 0
-52 -79 0
-52 -99 0
-53 -85 0
-53 -89 0
-55 -82 0
-55 -98 0
-56 -75 0
-56 -88 0
-58 -82 0
-58 -87 0
-60 -63 0
-62 -65 0
-64 -75 0
-64 -87 0
-66 -74 0
-67 -83 0
-67 -90 0
-68 -93 0
-69 -78 0
-69 -91 0
-70 -73 0
-70 -78 0
-71 -77 0
-71 -100 0
-72 -85 0
-74 -92 0
-77 -97 0
-79 -100 0
-80 -96 0
-81 -92 0
-83 -98 0
-86 -96 0
```

</details>

**Reproduction from scratch** (independent sets of the 11 x 12 grid, 132 variables, 241 clauses; the clauses per vertex in the order right edge, down edge):

```
python3 - > g.cnf <<'PY'
R, C = 11, 12
v = lambda r, c: r * C + c + 1
cls = []
for r in range(R):
    for c in range(C):
        if c + 1 < C: cls.append([-v(r, c), -v(r, c + 1)])
        if r + 1 < R: cls.append([-v(r, c), -v(r + 1, c)])
print(f"p cnf {R*C} {len(cls)}")
for cl in cls: print(*cl, 0)
PY
d4 g.cnf -dDNNF -out=g.nnf
cpog-gen g.cnf g.nnf g.cpog
cpog-check g.cnf g.cpog
```

Expected count 1142905840646183024996181; printed 1142905840377060093258581. The printed value depends on the clause order (another order changes D4's circuit and the intermediate values); with all horizontal edges before all vertical ones, cpog-check prints 1142905840634729171308373. Further square grids n x n with the order above: n = 11 correct; n = 12 true 162481813349792588536582997, printed 162481813323884485734084437; n = 14 true 338752110195939290445247645371206783, printed 338752110195912947014306924514720895; n = 16 true 18396766424410124752958806046933947217821482942, printed 18396766391538328774546208212373434903889878974.

**Root cause.** `q25_reduce_multiple` in `src/q25.c` (lines 155 to 168), called by `q25_canonize` from every `q25_build`, removes factors 2 and 5 from the digit string by looking only at the lowest radix word (radix 10^9): it divides the whole number by the largest power n^k that divides that word. For a number of two or more words this power can exceed n^9, the largest power of n that divides the radix, and then n^k need not divide the number; the long division in `q25_div_word` truncates, its remainder is discarded (line 164), and the exponent is increased by k. A direct demonstration: `q25_from_64(1001048576)` (10^9 + 2^20) prints 1000341504. The error needs at least two words, which is why only large counts are affected, and only some of them. One-line fix, which caps the power at n^9 so that every division is exact (the outer loop then continues removing factors):

```diff
-	while (scale <= Q25_RADIX && word % (scale * n) == 0) {
+	while (pwr < Q25_DIGITS && word % (scale * n) == 0) {
```

With it, cpog-check prints the true count on every certificate we retested (79, among them the 7 of the comparison and the grids above). The weighted count uses the same functions (`ring_evaluate`); we did not test weighted counts. Unrelated: `q25_clear_digits` (lines 128 to 132) clears `digit_buffer[WID]` instead of `digit_buffer[id]`; all callers pass `WID`.

**Minor, separate.** In a97ed85, `clause_locate` and `clause_locate_within` in `src/cpog-check.c` (lines 692 and 707) print a debug line per clause lookup unconditionally ("Looking for clause ..."), which produces logs of gigabytes (4.9 GB on the 100-vertex instance above, 21.8 GB on the 14 x 14 grid) and slows the check several-fold (about 4-fold on the instances above, 50-fold on a small domino instance whose check takes a tenth of a second); guarding them with `if (verb_level >= 4)` fixes this. Our comparison ran with that guard.

**Context.** We found this while comparing the two CPOG checkers on D4 certificates of our own and of the competition formulas.
