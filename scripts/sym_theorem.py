"""Lean theorem file for the n-queens solutions up to the symmetries of the square.

Reads a manifest with one line per element of DihedralGroup 4 (E in r0 r1 r2 r3 s0 s1 s2 s3
for r 0, ..., r 3, sr 0, ..., sr 3):
  E COUNT cpog POG LRAT    certified count > 0 (cpog2lrat.py output for the fixed-point CNF)
  E 0 unsat LRAT           LRAT refutation of the fixed-point CNF (CaDiCaL)
and writes a theorem file with
  queensN            Nat.card {f : Fin N → Fin N // non-attacking} = COUNT(r0)
                     (the plain queens CNF; Queens.card_of_check / card_of_checkAC)
  queensN_fix_E      Fintype.card {a // (symCnf (cnf N) (N * N) (cellPerm N g)).eval (ext a)} = COUNT
                     (checkAll_sound / checkAllAC_sound)
  queensN_unsat_E    (symCnf (cnf N) (N * N) (cellPerm N g)).Unsat (lrat_reflect_cnf)
  queensN_orbits     Nat.card (MulAction.orbitRel.Quotient (DihedralGroup 4) (Solution N)) = sum / 8
                     (Queens.card_orbits_eq)
A certificate is streamed (part B by lrat_stream_cnf) if its LRAT file exceeds EMBED_MAX bytes
(default 64 MB), else embedded. Paths are made absolute; `#eval` lines print millisecond
stamps around every check.

Usage: uv run scripts/sym_theorem.py N MANIFEST [EMBED_MAX] > T.lean
"""

import os
import sys

STAMP = '#eval show IO Unit from do IO.println s!"stamp {← IO.monoMsNow}"'
ELEMS = {"r0": ".r 0", "r1": ".r 1", "r2": ".r 2", "r3": ".r 3",
         "s0": ".sr 0", "s1": ".sr 1", "s2": ".sr 2", "s3": ".sr 3"}


def main():
    n, manifest = int(sys.argv[1]), sys.argv[2]
    embed_max = int(sys.argv[3]) if len(sys.argv) > 3 else 64 << 20
    rows = {}
    with open(manifest) as f:
        for line in f:
            w = line.split()
            if w:
                rows[w[0]] = w[1:]
    if sorted(rows) != sorted(ELEMS):
        sys.exit(f"manifest must list exactly {' '.join(ELEMS)}")
    counts = {e: int(rows[e][0]) for e in ELEMS}
    total = sum(counts.values())
    if total % 8:
        sys.exit(f"sum of fixed-point counts {total} is not divisible by 8")
    orbits = total // 8
    q = f"queens{n}"
    out = ["import CountCatcherMath.Families.QueensSym", "import LRATCatcher.StreamOracle", "",
           "open CountCatcher CountCatcher.Queens", ""]
    fact = {}
    for e, g in ELEMS.items():
        cnt, kind, *paths = rows[e]
        paths = [os.path.abspath(p) for p in paths]
        cnf = f"(symCnf (cnf {n}) ({n} * {n}) (cellPerm {n} ({g})))"
        if kind == "unsat":
            if cnt != "0":
                sys.exit(f"{e}: an LRAT refutation needs count 0")
            name = f"{q}_unsat_{e}"
            out += [STAMP, f'lrat_reflect_cnf {name} {cnf} "{paths[0]}"']
            fact[e] = f"(card_eq_zero_of_unsat {name})"
            continue
        if kind != "cpog":
            sys.exit(f"{e}: unknown kind {kind}")
        pog, lrat = paths
        stream = os.path.getsize(lrat) > embed_max
        if e == "r0":
            name = q
            stmt = (f"Nat.card {{f : Fin {n} → Fin {n} // ∀ i j, i ≠ j →\n"
                    "      f i ≠ f j ∧ (i : ℕ) + f j ≠ j + f i ∧ (i : ℕ) + f i ≠ j + f j}")
            lemma, lemmaAC, fcnf = "Queens.card_of_check", "Queens.card_of_checkAC", f"(cnf {n})"
        else:
            name = f"{q}_fix_{e}"
            stmt = (f"Fintype.card {{a : Fin ({n} * {n}) → Bool //\n"
                    f"      {cnf}.eval (ext a) = true}}")
            lemma, lemmaAC, fcnf = "checkAll_sound", "checkAllAC_sound", cnf
        if stream:
            out += [f'def {name}_pog : String := include_str "{pog}"', STAMP,
                    f'lrat_stream_cnf {name}_fwd (fwdCnfOf {fcnf} {name}_pog) "{lrat}"', STAMP,
                    f"theorem {name} :", f"    {stmt} = {cnt} :=",
                    f"  {lemmaAC} (pogStr := {name}_pog) (by native_decide) {name}_fwd"]
        else:
            out += [STAMP, f"theorem {name} :", f"    {stmt} = {cnt} :=",
                    f'  {lemma} (pogStr := include_str "{pog}")',
                    f'    (lratStr := include_str "{lrat}") (by native_decide)']
        fact[e] = name
    c = counts
    out += [STAMP, "",
            "/-- The number of n-queens solutions up to rotations and reflections of the board",
            "    (OEIS A002562), by Burnside's lemma from the certified counts above. -/",
            f"theorem {q}_orbits :",
            f"    Nat.card (MulAction.orbitRel.Quotient (DihedralGroup 4) (Solution {n})) = {orbits} :=",
            f"  card_orbits_eq {orbits} " + " ".join(str(c[e]) for e in ELEMS),
            "    " + " ".join(fact[e] for e in ["r0", "r1", "r2", "r3"]),
            "    " + " ".join(fact[e] for e in ["s0", "s1", "s2", "s3"]) + " rfl",
            "", f"#print axioms {q}_orbits"]
    print("\n".join(out))


if __name__ == "__main__":
    main()
