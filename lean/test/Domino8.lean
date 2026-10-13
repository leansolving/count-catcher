import CountCatcherMath.Families.Domino

/-! Domino tilings of the 8 × 8 board, stated as Mathlib's perfect matchings of
    `pathGraph 8 □ pathGraph 8` (OEIS A004003). The CNF is the Lean encoder `Domino.cnf 8 8`;
    the edge and vertex listing is proved for all boards (`Domino.listing`). -/

open CountCatcher SimpleGraph

theorem domino8x8 :
    Nat.card {M : (pathGraph 8 □ pathGraph 8).Subgraph // M.IsPerfectMatching} = 12988816 :=
  Domino.card_of_check
    (pogStr := include_str "data/dom08.pog") (lratStr := include_str "data/dom08.lrat")
    (by native_decide)

#print axioms domino8x8
