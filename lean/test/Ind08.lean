import CountCatcherMath.Families.Grid

/-! Independent sets of the 8 × 8 grid graph (OEIS A006506), as a statement about Mathlib's
    `pathGraph 8 □ pathGraph 8`. The CNF is the Lean encoder `IndepSet.cnf (gridGraph 8)`
    itself (its DIMACS export `data/ind08.dimacs` only fed D4 and cpog-gen). -/

open CountCatcher SimpleGraph

theorem grid8_indepSets :
    Nat.card {s : Finset (Fin 8 × Fin 8) // (pathGraph 8 □ pathGraph 8).IsIndepSet (s : Set _)} =
      660647962955 :=
  grid_card_of_check (pogStr := include_str "data/ind08.pog")
    (lratStr := include_str "data/ind08.lrat") (by native_decide)

#print axioms grid8_indepSets
