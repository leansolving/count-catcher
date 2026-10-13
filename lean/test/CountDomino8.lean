import CountCatcher

/-! Domino tilings of the 8 × 8 board through `count_models` (compare `Domino8.lean`, where the
    count is typed by hand). Certificate `data/dom08.{pog,lrat}`: D4, cpog-gen and the translator
    on the DIMACS export of `Domino.cnf 8 8`. -/

open CountCatcher SimpleGraph

count_models domino8x8 via (Domino.card_of_check (R := 8) (C := 8)) "data/dom08.pog" "data/dom08.lrat"

/-- The generated statement (OEIS A004003). -/
example : Nat.card {M : (pathGraph 8 □ pathGraph 8).Subgraph // M.IsPerfectMatching} = 12988816 :=
  domino8x8

/-- Downstream use: an ordinary theorem, rewritten like any other. -/
theorem domino8x8_factored :
    Nat.card {M : (pathGraph 8 □ pathGraph 8).Subgraph // M.IsPerfectMatching} = 2 ^ 4 * 901 ^ 2 := by
  rw [domino8x8]; norm_num

#print axioms domino8x8
#print axioms domino8x8_factored
