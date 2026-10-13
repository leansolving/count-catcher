import CountCatcher

/-! Count 0. cpog-gen refuses unsatisfiable formulas, so `count_models` takes one LRAT
    refutation of the encoder (CaDiCaL on the exported CNF) and uses lrat-catcher's check with
    `card_eq_zero_of_unsat`, or a family's `card_of_unsat`. -/

open CountCatcher SimpleGraph

/-- No three queens on the 3 × 3 board. -/
count_models queens3 via (Queens.card_of_check (n := 3)) "data/q03_unsat.lrat"

/-- `K_7` has no perfect matching (odd order), through the generic matching layer. -/
count_models k7 via (Matching.card_of_check (Complete.listing 7)) "data/k7_unsat.lrat"

/-- Streamed refutation: the separate theorem `k7_stream.unsat`. -/
count_models +stream k7_stream via (Matching.card_of_check (Complete.listing 7)) "data/k7_unsat.lrat"

count_models queens3_models (Queens.cnf 3) "data/q03_unsat.lrat"

count_models queens3_dimacs "data/q03.cnf" "data/q03_unsat.lrat"

example : Nat.card {f : Fin 3 → Fin 3 // Queens.Safe f} = 0 := queens3
example : Nat.card {M : (⊤ : SimpleGraph (Fin 7)).Subgraph // M.IsPerfectMatching} = 0 := k7

#print axioms queens3
#print axioms k7
#print axioms k7_stream
#print axioms queens3_models
#print axioms queens3_dimacs
