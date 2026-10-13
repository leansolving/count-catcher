"""Hand-made acceptance-contract cases (contract_audit.md, part 1).

For every case: a DIMACS formula, either a CPOG certificate (hand-written, or produced by
D4 + cpog-gen when CPOG is None) that goes through the translator, and/or a hand-written
POG + LRAT pair that goes to the Lean checker directly (for cases the translator cannot
express). Writes OUT/<case>.* files, OUT/contract.bundle for mccert-audit, and prints one
line per case with the D4 / cpog-gen / translator outcome.

Usage: uv run --no-project contract_cases.py OUTDIR [TOOLBIN] [ADVERSARIAL_DIR]
"""

import itertools
import os
import subprocess
import sys


def bf_count(V, clauses):
    n = 0
    for bits in itertools.product([False, True], repeat=V):
        # Lean semantics (McCert.ext): variables outside the universe are false
        val = lambda v: bits[v - 1] if v <= V else False
        if all(any(val(abs(l)) == (l > 0) for l in c) for c in clauses):
            n += 1
    return n


def cnf_text(V, clauses):
    return f"p cnf {V} {len(clauses)}\n" + "".join(
        " ".join(map(str, c + [0])) + "\n" for c in clauses
    )


# name: (V, clauses, CPOG text or None (= D4 + cpog-gen) or "" (no CPOG), [(tag, POG, LRAT)])
CASES = {
    "c01_neg_input_literal": (2, [[-1]], None, []),
    # F = (x ∨ y) ∧ z; n1 = ¬x ∧ ¬y, n2 = ¬n1 ∧ z (negated edge into an internal node)
    "c02_neg_internal_edge": (
        3,
        [[1, 2], [3]],
        "r 5\n3 p 4 -1 -2 0\n6 p 5 -4 3 0\n9 a 5 0 2 6 4 5 1 0\n",
        [],
    ),
    # negated root: F = ¬x ∨ ¬y, u = x ∧ y, root ¬u
    "c03_neg_root": (2, [[-1, -2]], "r -3\n2 p 3 1 2 0\n5 a -3 0 3 4 1 0\n", []),
    # constants: true = empty product; the root unit is its defining clause, not an addition
    "c04_empty_cnf": (3, [], None, [("hand", "V 3\nr 4\np 0\n", "3 0 1 2 0\n")]),
    "c05_taut_only": (
        2,
        [[1, -1]],
        None,
        [
            ("hand_ids_shifted", "V 2\nr 3\np 0\n", "3 0 1 2 0\n"),
            ("hand_ids_dimacs", "V 2\nr 3\np 0\n", "4 0 2 3 0\n"),
        ],
    ),
    "c06_zero_vars": (0, [], None, [("hand", "V 0\nr 1\np 0\n", "3 0 1 2 0\n")]),
    # count 0: false = negated empty product (a negated root)
    "c07_zero_vars_empty_clause": (
        0,
        [[]],
        None,
        [("hand_false_root", "V 0\nr -1\np 0\n", "4 0 1 0\n")],
    ),
    "c08_unsat": (
        1,
        [[1], [-1]],
        None,
        [
            ("hand_false_root", "V 1\nr -2\np 0\n", "5 0 1 2 0\n"),
            ("hand_x_and_notx", "V 1\nr 2\np 1 -1 0\n", "6 0 1 2 0\n"),
        ],
    ),
    # literal roots (cpog-gen wraps them in a one-argument product)
    "c09_literal_root_neg": (2, [[-1]], "r -1\n2 a -1 0 1 0\n", []),
    "c10_literal_root_pos": (3, [[2], [2, 3]], "r 2\n3 a 2 0 1 0\n", []),
    "c11_unused_header_vars": (3, [[2]], None, []),
    "c12_taut_plus_clause": (3, [[1, -1], [2, 3]], None, []),
    "c13_duplicate_clause": (2, [[1, 2], [1, 2]], None, []),
    "c14_duplicate_literal": (2, [[1, 1, 2]], None, []),
    "c15_empty_clause_plus": (2, [[1], []], None, []),
    # variable outside the header universe
    "c16_var_outside_header": (1, [[2]], "", [("hand", "V 1\nr 3\np 2 0\n", "4 0 1 2 3 0\n")]),
    # sum x ∨ ¬x: exclusion holds with no hints (contradictory start); first defining clause
    # of the sum is tautological
    "c17_sum_x_or_notx": (
        1,
        [],
        "",
        [
            ("hand_ids_shifted", "V 1\nr 2\ns 1 -1 0\n", "4 0 3 1 2 0\n"),
            ("hand_ids_dimacs", "V 1\nr 2\ns 1 -1 0\n", "5 0 4 2 3 0\n"),
        ],
    ),
    # product with an empty-product (true) child
    "c18_true_child": (
        1,
        [[1]],
        "",
        [("hand", "V 1\nr 3\np 0\np 1 2 0\n", "7 0 6 1 2 3 0\n")],
    ),
    # sum true ∨ x is not exclusive: C4 must reject it (unchecked count would be 3, true 2)
    "c19_sum_true_or_x": (1, [], "", [("hand", "V 1\nr 3\np 0\ns 2 1 0\n", "5 0 4 2 3 0\n")]),
    "c20_root_undeclared": (2, [[1]], "", [("hand", "V 2\nr 5\n", "3 0 1 2 0\n")]),
    "c21_pog_V_mismatch": (2, [[1]], "", [("hand", "V 3\nr 1\n", "3 0 1 2 0\n")]),
    # an addition with an empty hint list, valid for the core checker because its clause
    # contains a literal that is already a unit ([2] is an input clause): the translator writes
    # "4 2 0  0" (two spaces), which the core LRAT text parser rejects; the same step with one
    # space is accepted by the embedded check
    "c23_empty_hint_addition": (
        3,
        [[2], [2, 3]],
        "r 2\n3 a 2 0 0\n",
        [("hand_single_space", "V 3\nr 2\n", "4 2 0 0\n5 0 4 3 0\n")],
    ),
    # R:50 of the random set (count 196) with the hint of step 47 (clause 14 1 2, implied by
    # the unit 14 derived in step 46) dropped: the translator writes "48 14 1 2 0  0", a parse
    # error for the core parser; with one space the embedded part B accepts, the streamed part
    # B rejects (lrat-catcher's normalizeAction turns the hint-less RUP step into RAT)
    "c24_empty_hint_r50": (
        8,
        [[-3, 7, 4, -5], [-2, 1, -3], [8, 1, -2]],
        "@cases/c24_r50_nohint.cpog",
        [],
    ),
    # an empty clause in F: parts A and B accept the POG x (count 1), part C must reject
    # (the empty clause kills no node), otherwise the count 1 of an unsatisfiable F would pass
    "c25_empty_clause_in_F": (1, [[1], []], "", [("hand", "V 1\nr 2\np 1 0\n", "6 0 2 0\n")]),
    # malformed LRAT (added 2026-10-11): the certificate of c18 (valid POG, count 1) with the
    # terminating 0 of the addition's hint list left out; parts A and C accept, the LRAT text
    # parser rejects the refutation (condition "the refutation is well-formed LRAT")
    "c26_lrat_missing_zero": (
        1,
        [[1]],
        "",
        [("hand", "V 1\nr 3\np 0\np 1 2 0\n", "7 0 6 1 2 3\n")],
    ),
    # zero variables, empty CNF, literal root impossible; true root via a derived unit
    "c22_true_root_derived_unit": (
        2,
        [],
        "r 3\n1 p 3 0\n2 a 3 0 1 0\n",
        [],
    ),
}

ADV_TRUE = {
    "h1_unused": 2, "h2_or": 3, "h3_nand": 6, "a4_prod_overlap": 0, "a14_prod_self": 1,
    "a5_sum_input_hint": 1, "a5b_sum_derived_hint": 1, "a6_self_delete": 1,
    "a7_delete_def": 1, "a8_leftover_derived": 1, "a9_ext_collision": 2, "a10_reused_id": 1,
}


def run(cmd, log):
    with open(log, "w") as f:
        return subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, timeout=60).returncode


def last_line(path):
    try:
        lines = [l for l in open(path).read().splitlines() if l.strip()]
        return lines[-1] if lines else ""
    except OSError:
        return ""


def main():
    out = sys.argv[1]
    tb = sys.argv[2] if len(sys.argv) > 2 else os.path.join(os.path.dirname(__file__), "../../../tools/bin")
    adv = sys.argv[3] if len(sys.argv) > 3 else None
    os.makedirs(out, exist_ok=True)
    env = dict(os.environ, PATH=tb + os.pathsep + os.environ["PATH"])
    bundle = []
    rows = []

    def add(name, expected, cnf, pog, lrat):
        bundle.append(f"@inst {name} {expected}\n@cnf\n{cnf}@pog\n{pog}@lrat\n{lrat}@end\n")

    def translate(name, cnfp, cpogp, expected, cnf):
        base = os.path.join(out, name)
        e = run([os.path.join(tb, "cpog2lrat"), cnfp, cpogp, base + ".fwd"], base + ".c2l")
        py = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../scripts/cpog2lrat.py")
        ep = run(["uv", "run", "-q", "--no-project", py, cnfp, cpogp, base + ".pyfwd"], base + ".pyc2l")
        msg = last_line(base + ".c2l")
        if e == 0:
            lrat = open(base + ".fwd.lrat").read()
            add(name + "/c2l", expected, cnf, open(base + ".fwd.pog").read(), lrat)
            if "  " in lrat:  # the same certificate with single spaces
                add(name + "/c2l_single_space", expected, cnf, open(base + ".fwd.pog").read(),
                    "".join(" ".join(l.split()) + "\n" for l in lrat.splitlines()))
        return e, ep, msg

    for name, (V, cls, cpog, hand) in CASES.items():
        base = os.path.join(out, name)
        cnf = cnf_text(V, cls)
        open(base + ".cnf", "w").write(cnf)
        N = bf_count(V, cls)
        d4 = gen = "-"
        c2l = ""
        if cpog is None:
            e = subprocess.run(
                [os.path.join(tb, "d4"), base + ".cnf", "-dDNNF", f"-out={base}.nnf"],
                stdout=open(base + ".d4log", "w"), stderr=subprocess.STDOUT, env=env, timeout=60,
            ).returncode
            cnt = [l.split()[1] for l in open(base + ".d4log") if l.startswith("s ")]
            d4 = f"exit{e}:s={cnt[0] if cnt else '?'}"
            g = subprocess.run(
                [os.path.join(tb, "cpog-gen"), base + ".cnf", base + ".nnf", base + ".cpog"],
                stdout=open(base + ".genlog", "w"), stderr=subprocess.STDOUT, env=env, timeout=60,
            ).returncode
            gen = f"exit{g}"
        elif cpog and cpog.startswith("@"):
            src = os.path.join(os.path.dirname(os.path.abspath(__file__)), cpog[1:])
            open(base + ".cpog", "w").write(open(src).read())
        elif cpog:
            open(base + ".cpog", "w").write(cpog)
        if cpog != "" and os.path.exists(base + ".cpog"):
            e, ep, msg = translate(name, base + ".cnf", base + ".cpog", N, cnf)
            c2l = f"native=exit{e} py=exit{ep}" + (f" [{msg}]" if e else "")
        for tag, pog, lrat in hand:
            add(f"{name}/{tag}", N, cnf, pog, lrat)
        rows.append(f"{name} count={N} d4={d4} cpog-gen={gen} translator={c2l or '-'} hand={len(hand)}")
    if adv:
        for name, N in ADV_TRUE.items():
            cnfp, cpogp = os.path.join(adv, name + ".cnf"), os.path.join(adv, name + ".cpog")
            cnf = open(cnfp).read()
            e, ep, msg = translate("adv_" + name, cnfp, cpogp, N, cnf)
            rows.append(f"adv_{name} count={N} translator=native=exit{e} py=exit{ep}" + (f" [{msg}]" if e else ""))
    open(os.path.join(out, "contract.bundle"), "w").write("".join(bundle))
    print("\n".join(rows))


if __name__ == "__main__":
    main()
