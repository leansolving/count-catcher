import CountCatcherMath.Families.QueensSym

/-! The 8-queens solutions up to the symmetries of the square (OEIS A002562: 12), by
    Burnside's lemma from certified counts: the 92 placements (the certificate of
    `test/Queens8.lean`), the 4 solutions fixed by the half turn `r 2` (a CPOG certificate for
    the fixed-point formula `symCnf (cnf 8) 64 (cellPerm 8 (r 2))`), and no solution fixed by a
    quarter turn or a reflection (CaDiCaL's LRAT refutations of the other fixed-point
    formulas, checked by lrat-catcher). The formulas are exported by
    `test/QueensSymExport.lean`. -/

open CountCatcher CountCatcher.Queens

theorem queens8 :
    Nat.card {f : Fin 8 → Fin 8 // ∀ i j, i ≠ j →
      f i ≠ f j ∧ (i : ℕ) + f j ≠ j + f i ∧ (i : ℕ) + f i ≠ j + f j} = 92 :=
  Queens.card_of_check
    (pogStr := include_str "data/q08.pog") (lratStr := include_str "data/q08.lrat")
    (by native_decide)

theorem queens8_fix_r2 : Fintype.card {a : Fin (8 * 8) → Bool //
    (symCnf (cnf 8) (8 * 8) (cellPerm 8 (.r 2))).eval (ext a) = true} = 4 :=
  checkAll_sound
    (pogStr := include_str "data/qs08_r2.pog") (lratStr := include_str "data/qs08_r2.lrat")
    (by native_decide)

lrat_reflect_cnf queens8_unsat_r1 (symCnf (cnf 8) (8 * 8) (cellPerm 8 (.r 1))) "test/data/qs08_r1.lrat"
lrat_reflect_cnf queens8_unsat_r3 (symCnf (cnf 8) (8 * 8) (cellPerm 8 (.r 3))) "test/data/qs08_r3.lrat"
lrat_reflect_cnf queens8_unsat_s0 (symCnf (cnf 8) (8 * 8) (cellPerm 8 (.sr 0))) "test/data/qs08_s0.lrat"
lrat_reflect_cnf queens8_unsat_s1 (symCnf (cnf 8) (8 * 8) (cellPerm 8 (.sr 1))) "test/data/qs08_s1.lrat"
lrat_reflect_cnf queens8_unsat_s2 (symCnf (cnf 8) (8 * 8) (cellPerm 8 (.sr 2))) "test/data/qs08_s2.lrat"
lrat_reflect_cnf queens8_unsat_s3 (symCnf (cnf 8) (8 * 8) (cellPerm 8 (.sr 3))) "test/data/qs08_s3.lrat"

/-- The number of 8-queens solutions up to rotations and reflections of the board. -/
theorem queens8_orbits :
    Nat.card (MulAction.orbitRel.Quotient (DihedralGroup 4) (Solution 8)) = 12 :=
  card_orbits_eq 12 92 0 4 0 0 0 0 0 queens8
    (card_eq_zero_of_unsat queens8_unsat_r1) queens8_fix_r2
    (card_eq_zero_of_unsat queens8_unsat_r3) (card_eq_zero_of_unsat queens8_unsat_s0)
    (card_eq_zero_of_unsat queens8_unsat_s1) (card_eq_zero_of_unsat queens8_unsat_s2)
    (card_eq_zero_of_unsat queens8_unsat_s3) rfl

#print axioms queens8_orbits
