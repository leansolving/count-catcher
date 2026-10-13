import CountCatcherMath.Families.Queens

/-! The 8-queens problem (OEIS A000170): placements of eight queens on the 8 × 8 board, the
    queen of row `i` in column `f i`, no two in a common column or diagonal. The CNF is the
    Lean encoder `Queens.cnf 8` (its DIMACS export equals `scripts/gen_queens.py 8`). -/

open CountCatcher

theorem queens8 :
    Nat.card {f : Fin 8 → Fin 8 // ∀ i j, i ≠ j →
      f i ≠ f j ∧ (i : ℕ) + f j ≠ j + f i ∧ (i : ℕ) + f i ≠ j + f j} = 92 :=
  Queens.card_of_check
    (pogStr := include_str "data/q08.pog") (lratStr := include_str "data/q08.lrat")
    (by native_decide)

#print axioms queens8
