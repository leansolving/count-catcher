import CountCatcher
import CountCatcherMath.Families.GraphIso

/-! Triangle-free graphs on 5 vertices up to isomorphism (OEIS A006785: 14), by Burnside's lemma
    over `Perm (Fin 5)` grouped by cycle type: one
    certified count per cycle type, the identity term being the labelled count 388. Certificates
    from `scripts/graph_orbits.py --family clique:3 --n 5` (`cpog-gen-norev -F`). -/

open CountCatcher CountCatcher.GraphIso CountCatcher.CycleType

count_models tri5_fix_5 via (CliqueFreeFam.fix_card_of_check (n := 5) (s := 3) (l := [5])) "data/tri05_5.pog" "data/tri05_5.lrat" (count := 3)
count_models tri5_fix_4 via (CliqueFreeFam.fix_card_of_check (n := 5) (s := 3) (l := [4])) "data/tri05_4.pog" "data/tri05_4.lrat" (count := 4)
count_models tri5_fix_3_2 via (CliqueFreeFam.fix_card_of_check (n := 5) (s := 3) (l := [3, 2])) "data/tri05_3_2.pog" "data/tri05_3_2.lrat" (count := 3)
count_models tri5_fix_3 via (CliqueFreeFam.fix_card_of_check (n := 5) (s := 3) (l := [3])) "data/tri05_3.pog" "data/tri05_3.lrat" (count := 7)
count_models tri5_fix_2_2 via (CliqueFreeFam.fix_card_of_check (n := 5) (s := 3) (l := [2, 2])) "data/tri05_2_2.pog" "data/tri05_2_2.lrat" (count := 28)
count_models tri5_fix_2 via (CliqueFreeFam.fix_card_of_check (n := 5) (s := 3) (l := [2])) "data/tri05_2.pog" "data/tri05_2.lrat" (count := 48)
count_models tri5 via (CliqueFreeFam.card_of_check (n := 5) (s := 3)) "data/tri05_id.pog" "data/tri05_id.lrat" (count := 388)

/-- Triangle-free graphs on 5 vertices up to relabelling. -/
theorem tri5_orbits :
    Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin 5))
      {G : SimpleGraph (Fin 5) // G.CliqueFree 3}) = 14 :=
  CliqueFreeFam.card_orbits_eq 14
    [([5], 3), ([4], 4), ([3, 2], 3), ([3], 7), ([2, 2], 28), ([2], 48), ([], 388)]
    (List.forall_mem_cons.2 ⟨tri5_fix_5, List.forall_mem_cons.2 ⟨tri5_fix_4,
      List.forall_mem_cons.2 ⟨tri5_fix_3_2, List.forall_mem_cons.2 ⟨tri5_fix_3,
      List.forall_mem_cons.2 ⟨tri5_fix_2_2, List.forall_mem_cons.2 ⟨tri5_fix_2,
      List.forall_mem_cons.2 ⟨CliqueFreeFam.fix_nil tri5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide)

/-- The same as isomorphism classes, a statement without the action. -/
theorem tri5_isoClasses :
    Nat.card (Quot fun G H : {G : SimpleGraph (Fin 5) // G.CliqueFree 3} =>
      Nonempty (G.1 ≃g H.1)) = 14 :=
  CliqueFreeFam.card_isoClasses_eq tri5_orbits

/-! The side conditions reject a wrong orbit count, a missing cycle type, a duplicated cycle
    type (the class sizes then exceed `5!`), and an unsorted cycle type. -/

example : checkClasses 5 15
    [([5], 3), ([4], 4), ([3, 2], 3), ([3], 7), ([2, 2], 28), ([2], 48), ([], 388)] = false := by
  decide
example : checkClasses 5 14
    [([4], 4), ([3, 2], 3), ([3], 7), ([2, 2], 28), ([2], 48), ([], 388)] = false := by
  decide
example : checkClasses 5 14
    [([5], 3), ([5], 3), ([4], 4), ([3, 2], 3), ([3], 7), ([2, 2], 28), ([2], 48),
      ([], 388)] = false := by
  decide
example : checkClasses 5 14
    [([5], 3), ([4], 4), ([2, 3], 3), ([3], 7), ([2, 2], 28), ([2], 48), ([], 388)] = false := by
  decide

/-! A certificate for the wrong fixed-point formula is rejected: the certificate of the
    transposition `[2]` offered for the 3-cycle `[3]`. -/

/--
error: count_models: the verified check rejected the certificate for 'tri5_bad':
  part B (LRAT refutation of F, the defining clauses and ¬root): step 1 (line 1 of a text LRAT file): clause 118 (11 2 3 4 0) does not follow by RUP from its 2 hints
  part C (every input clause implied by the POG): input clause 11 (-1 5 0) is not implied by the POG: the assignment -2 -5 -3 -6 -4 -7 -8 1 satisfies the POG root 36 and falsifies the clause (the circuit has models that are not models of the formula)
'tri5_bad' was not declared (the reports come from unverified diagnostics).
-/
#guard_msgs in
count_models tri5_bad via (CliqueFreeFam.fix_card_of_check (n := 5) (s := 3) (l := [3])) "data/tri05_2.pog" "data/tri05_2.lrat" (count := 48)

/-! The labelled count split by the neighbourhood of vertex `0` (as for n = 11):
    `388 = Σ_k C(4, k) · #{G | N(0) = {1, …, k}} = 41 + 4·41 + 6·25 + 4·8 + 1`. -/

count_models tri5_nbr_0 via (CliqueFreeFam.nbr_card_of_check (n := 5) (s := 3) (k := 0)) "data/tri05_nbr0.pog" "data/tri05_nbr0.lrat" (count := 41)
count_models tri5_nbr_1 via (CliqueFreeFam.nbr_card_of_check (n := 5) (s := 3) (k := 1)) "data/tri05_nbr1.pog" "data/tri05_nbr1.lrat" (count := 41)
count_models tri5_nbr_2 via (CliqueFreeFam.nbr_card_of_check (n := 5) (s := 3) (k := 2)) "data/tri05_nbr2.pog" "data/tri05_nbr2.lrat" (count := 25)
count_models tri5_nbr_3 via (CliqueFreeFam.nbr_card_of_check (n := 5) (s := 3) (k := 3)) "data/tri05_nbr3.pog" "data/tri05_nbr3.lrat" (count := 8)
count_models tri5_nbr_4 via (CliqueFreeFam.nbr_card_of_check (n := 5) (s := 3) (k := 4)) "data/tri05_nbr4.pog" "data/tri05_nbr4.lrat" (count := 1)

theorem tri5_split : Nat.card {G : SimpleGraph (Fin 5) // G.CliqueFree 3} = 388 :=
  CliqueFreeFam.card_eq_of_split 388 [(0, 41), (1, 41), (2, 25), (3, 8), (4, 1)]
    (List.forall_mem_cons.2 ⟨tri5_nbr_0, List.forall_mem_cons.2 ⟨tri5_nbr_1,
      List.forall_mem_cons.2 ⟨tri5_nbr_2, List.forall_mem_cons.2 ⟨tri5_nbr_3,
      List.forall_mem_cons.2 ⟨tri5_nbr_4, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide)

/-- A missing neighbourhood size is rejected. -/
example : checkSplit 5 387 [(0, 41), (1, 41), (2, 25), (3, 8)] = false := by decide

#print axioms tri5_orbits
#print axioms tri5_isoClasses
#print axioms tri5_split
