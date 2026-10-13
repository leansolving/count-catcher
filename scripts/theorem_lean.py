"""Lean theorem file for one instance of a family, from a translated certificate.

Families (ARG):
  domino N      Nat.card {M : (pathGraph N □ pathGraph N).Subgraph // M.IsPerfectMatching}
  queens N      Nat.card {f : Fin N → Fin N // non-attacking}
  grid N        Nat.card {s : Finset (Fin N × Fin N) // (pathGraph N □ pathGraph N).IsIndepSet s}
  hypercube N   Nat.card {s : Finset (Fin N → Bool) // (hypercube N).IsIndepSet s}
  edges CNF     Nat.card {s : Finset (Fin k) // (edgeGraph E).IsIndepSet s}, E the edge-list
                literal from the .edges file next to CNF, k from the CNF header
  dimacs CNF    Fintype.card {a : Fin V → Bool // (parseDimacs D).eval (ext a) = true}, D the
                text of CNF (`include_str`), V from its `p cnf` header; any DIMACS file,
                comment lines (`c t wmc`, `c p weight …`) are ignored by the parser
Modes:
  embed         parts A, B, C in one native_decide (`*_card_of_check`, one native axiom)
  stream        part B by lrat_stream_cnf, parts A and C by native_decide
                (`*_card_of_checkAC`, two native axioms)
The CNF in the theorem is the Lean encoder (the certificate must have been produced for its
DIMACS export, identical to scripts/gen_*.py), or for `dimacs` the file itself as parsed by
LRATCatcher.parseDimacs (lemmas `checkAll_sound`, `checkAllAC_sound`). Paths are made
absolute (with --command --base DIR: relative to DIR, the directory of the theorem file, which
count_models resolves them against); `#eval` lines print millisecond stamps around the checks.

Usage: uv run scripts/theorem_lean.py [--command [--base DIR]] [--keep KEEP] FAMILY ARG MODE COUNT
           POG LRAT [DESCRIPTION] > T.lean
       (dimacs: DESCRIPTION is the theorem name prefix, default the CNF file stem)

--keep KEEP (MODE stream only): part B on the initial clauses that the mask file KEEP selects
(`cpog2lrat --keep` writes KEEP and the LRAT numbered for it): `lrat_stream_cnf THM_sel
(fwdCnfOfSel CNF THM_pog THM_keep) "LRAT"`, then the family lemma with
`(fwdCnfOf_unsat_of_sel THM_sel)` (CountCatcherMath/FwdSel.lean); with --command the argument
`(keep := "KEEP")` of count_models.

--command: the file uses the tool front end instead of typing the statement: `import
CountCatcher` and one `count_models +MODE THM via (LEMMA ARGS) "POG" "LRAT" (count := COUNT)`
(`dimacs`: the file form `count_models +MODE THM "CNF" …`). The statement is the family
lemma's conclusion, the same as above; COUNT is only a hint that the verified check checks
(a wrong hint is rejected); COUNT `-` omits the hint. Theorem names are unchanged.
"""

import os
import sys

STAMP = '#eval show IO Unit from do IO.println s!"stamp {← IO.monoMsNow}"'


def main():
    args = sys.argv[1:]
    command, keep, base = False, None, None
    while args and args[0] in ("--command", "--keep", "--base"):
        if args[0] == "--command":
            command, args = True, args[1:]
        elif args[0] == "--base":
            base, args = os.path.abspath(args[1]), args[2:]
        else:
            keep, args = os.path.abspath(args[1]), args[2:]
    if base and not command:
        sys.exit("--base needs --command (count_models resolves relative paths; the other "
                 "commands of the file do not)")
    fam, arg, mode, count, pog, lrat, *desc = args
    if keep and mode != "stream":
        sys.exit("--keep needs MODE stream (the LRAT is numbered for the masked clauses)")
    pog, lrat = os.path.abspath(pog), os.path.abspath(lrat)
    if mode == "embed" and os.path.exists(lrat):
        with open(lrat, "rb") as f:
            if f.read(1) in (b"a", b"d"):
                sys.exit(f"{lrat} is binary LRAT, which cannot be embedded; use MODE stream")
    pre = []
    if fam == "domino":
        n = int(arg)
        imp, thm = "CountCatcherMath.Families.Domino", f"domino_{n}x{n}"
        stmt = f"{{M : (pathGraph {n} □ pathGraph {n}).Subgraph // M.IsPerfectMatching}}"
        cnf, lemma = f"(Domino.cnf {n} {n})", "Domino.card_of_check"
        via = f"Domino.card_of_check (R := {n}) (C := {n})"
    elif fam == "queens":
        n = int(arg)
        imp, thm = "CountCatcherMath.Families.Queens", f"queens{n}"
        stmt = (f"{{f : Fin {n} → Fin {n} // ∀ i j, i ≠ j →\n"
                "      f i ≠ f j ∧ (i : ℕ) + f j ≠ j + f i ∧ (i : ℕ) + f i ≠ j + f j}")
        cnf, lemma = f"(Queens.cnf {n})", "Queens.card_of_check"
        via = f"Queens.card_of_check (n := {n})"
    elif fam == "grid":
        n = int(arg)
        imp, thm = "CountCatcherMath.Families.Grid", f"grid{n}_indepSets"
        stmt = (f"{{s : Finset (Fin {n} × Fin {n}) //\n"
                f"      (pathGraph {n} □ pathGraph {n}).IsIndepSet (s : Set _)}}")
        cnf, lemma = f"(IndepSet.cnf (gridGraph {n}))", "grid_card_of_check"
        via = f"grid_card_of_check (n := {n})"
    elif fam == "hypercube":
        n = int(arg)
        imp, thm = "CountCatcherMath.Families.Graphs", f"hypercube{n}_indepSets"
        stmt = f"{{s : Finset (Fin {n} → Bool) // (hypercube {n}).IsIndepSet (s : Set _)}}"
        cnf, lemma = f"(IndepSet.cnf (hypercubeFin {n}))", "hypercube_card_of_check"
        via = f"hypercube_card_of_check (n := {n})"
    elif fam == "edges":
        name = os.path.splitext(os.path.basename(arg))[0].replace(".", "")
        with open(arg) as f:
            k = next(int(l.split()[2]) for l in f if l.startswith("p cnf"))
        with open(os.path.splitext(arg)[0] + ".edges") as f:
            es = [tuple(map(int, l.split())) for l in f]
        lits = ", ".join(f"s({u}, {v})" for u, v in es)
        doc = desc[0] if desc else name
        # The code generator recurses once per list element (about 4000 edges hit the default).
        pre = ["set_option maxRecDepth 100000 in",
               f"/-- {doc}: {k} vertices, {len(es)} edges. -/",
               f"def {name}Edges : List (Sym2 (Fin {k})) := [{lits}]", ""]
        imp, thm = "CountCatcherMath.Families.Graphs", f"{name}_indepSets"
        stmt = f"{{s : Finset (Fin {k}) // (edgeGraph {name}Edges).IsIndepSet (s : Set _)}}"
        cnf, lemma = f"(edgeCnf {name}Edges)", "edgeGraph_card_of_check"
        via = f"edgeGraph_card_of_check (l := {name}Edges)"
    elif fam == "dimacs":
        name = desc[0] if desc else os.path.splitext(os.path.basename(arg))[0]
        name = "".join(ch if ch.isalnum() else "_" for ch in name)
        path = os.path.abspath(arg)
        with open(path) as f:
            hdr = [l.split() for l in f if l.startswith("p")]
        if len(hdr) != 1 or hdr[0][:2] != ["p", "cnf"]:
            sys.exit(f"{arg}: expected exactly one 'p cnf V M' header")
        v = int(hdr[0][2])
        pre = [f'/-- The DIMACS file `{os.path.basename(arg)}` ({v} variables). -/',
               f'def {name}_dimacs : String := include_str "{path}"', ""]
        imp, thm = "CountCatcherMath.Check", f"{name}_models"
        stmt = (f"{{a : Fin {v} → Bool //\n"
                f"      (LRATCatcher.parseDimacs {name}_dimacs).eval (ext a) = true}}")
        cnf, lemma = f"(LRATCatcher.parseDimacs {name}_dimacs)", "checkAll_sound"
        via = None
    else:
        sys.exit(f"unknown family {fam}")
    if command:
        if mode not in ("embed", "stream"):
            sys.exit(f"unknown mode {mode}")
        if base:
            pog, lrat = os.path.relpath(pog, base), os.path.relpath(lrat, base)
            keep = keep and os.path.relpath(keep, base)
            path = os.path.relpath(path, base) if fam == "dimacs" else None
        subj = f'"{path}"' if fam == "dimacs" else f"via ({via})"
        pre = [] if fam == "dimacs" else pre  # the file form reads the DIMACS file itself
        out = ["import CountCatcher", "", "open CountCatcher SimpleGraph", ""] + pre + [
            STAMP, f'count_models +{mode} {thm} {subj} "{pog}" "{lrat}"'
            + (f' (keep := "{keep}")' if keep else "")
            + ("" if count == "-" else f" (count := {count})"),
            STAMP, "", f"#print axioms {thm}"]
        print("\n".join(out))
        return
    card = "Fintype.card" if fam == "dimacs" else "Nat.card"
    lemmaAC = "checkAllAC_sound" if fam == "dimacs" else lemma + "AC"
    out = [f"import {imp}"]
    if keep:
        out.append("import CountCatcherMath.FwdSel")
    if mode == "stream":
        out.append("import LRATCatcher.StreamOracle")
    out += ["", "open CountCatcher" + ("" if fam == "dimacs" else " SimpleGraph"), ""] + pre
    if mode == "embed":
        out += [STAMP,
                f"theorem {thm} :", f"    {card} {stmt} = {count} :=",
                f'  {lemma} (pogStr := include_str "{pog}")',
                f'    (lratStr := include_str "{lrat}") (by native_decide)']
    elif keep:
        out += [f'def {thm}_pog : String := include_str "{pog}"',
                f'def {thm}_keep : String := include_str "{keep}"', "", STAMP,
                f'lrat_stream_cnf {thm}_sel (fwdCnfOfSel {cnf} {thm}_pog {thm}_keep) "{lrat}"',
                STAMP, f"theorem {thm} :", f"    {card} {stmt} = {count} :=",
                f"  {lemmaAC} (pogStr := {thm}_pog) (by native_decide)",
                f"    (fwdCnfOf_unsat_of_sel {thm}_sel)"]
    elif mode == "stream":
        out += [f'def {thm}_pog : String := include_str "{pog}"', "", STAMP,
                f'lrat_stream_cnf {thm}_fwd (fwdCnfOf {cnf} {thm}_pog) "{lrat}"', STAMP,
                f"theorem {thm} :", f"    {card} {stmt} = {count} :=",
                f"  {lemmaAC} (pogStr := {thm}_pog) (by native_decide) {thm}_fwd"]
    else:
        sys.exit(f"unknown mode {mode}")
    out += [STAMP, "", f"#print axioms {thm}"]
    print("\n".join(out))


if __name__ == "__main__":
    main()
