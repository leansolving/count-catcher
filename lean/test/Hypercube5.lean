import CountCatcherMath.Families.Graphs

/-! Independent sets of the hypercube Q_5: bit vectors of length 5, adjacent iff
    their Hamming distance is one. The CNF is the Lean encoder `IndepSet.cnf (hypercubeFin 5)`. -/

open CountCatcher SimpleGraph

theorem hypercube5_indepSets :
    Nat.card {s : Finset (Fin 5 → Bool) // (hypercube 5).IsIndepSet (s : Set _)} = 254475 :=
  hypercube_card_of_check (pogStr := include_str "data/hq5.pog")
    (lratStr := include_str "data/hq5.lrat") (by native_decide)

#print axioms hypercube5_indepSets
