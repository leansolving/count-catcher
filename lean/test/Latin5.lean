import CountCatcherMath.Command
import CountCatcherMath.Families.LatinAll

/-! Reduced Latin squares of order 5 (OEIS A000315: 56), monolithic and split by the second row.
    Certificates from
    `scripts/showcase/latin_fibres.py --n 5` (fibres, `data/lat5_rNNN.{pog,lrat}`) and from the
    plain encoder `Latin.cnf 5` (`data/lat5.{pog,lrat}`), both with `cpog-gen-norev -F` and
    `cpog2lrat --delete`. -/

open CountCatcher CountCatcher.Latin

/-- Monolithic: one certificate for the encoder. -/
count_models latin5 via (Latin.card_of_check (n := 5)) "data/lat5.pog" "data/lat5.lrat"

example : Nat.card {L : Fin 5 → Fin 5 → Fin 5 // IsReducedLatin L} = 56 := latin5

/-! One certificate per admissible second row `r` (fibre `L 1 = r`). -/

count_models latin5_r000 via (Latin.fibre_card_of_check (n := 5) (r := ![1, 0, 3, 4, 2])) "data/lat5_r000.pog" "data/lat5_r000.lrat" (count := 4)
count_models latin5_r001 via (Latin.fibre_card_of_check (n := 5) (r := ![1, 0, 4, 2, 3])) "data/lat5_r001.pog" "data/lat5_r001.lrat" (count := 4)
count_models latin5_r002 via (Latin.fibre_card_of_check (n := 5) (r := ![1, 2, 0, 4, 3])) "data/lat5_r002.pog" "data/lat5_r002.lrat" (count := 4)
count_models latin5_r003 via (Latin.fibre_card_of_check (n := 5) (r := ![1, 2, 3, 4, 0])) "data/lat5_r003.pog" "data/lat5_r003.lrat" (count := 6)
count_models latin5_r004 via (Latin.fibre_card_of_check (n := 5) (r := ![1, 2, 4, 0, 3])) "data/lat5_r004.pog" "data/lat5_r004.lrat" (count := 6)
count_models latin5_r005 via (Latin.fibre_card_of_check (n := 5) (r := ![1, 3, 0, 4, 2])) "data/lat5_r005.pog" "data/lat5_r005.lrat" (count := 6)
count_models latin5_r006 via (Latin.fibre_card_of_check (n := 5) (r := ![1, 3, 4, 0, 2])) "data/lat5_r006.pog" "data/lat5_r006.lrat" (count := 4)
count_models latin5_r007 via (Latin.fibre_card_of_check (n := 5) (r := ![1, 3, 4, 2, 0])) "data/lat5_r007.pog" "data/lat5_r007.lrat" (count := 6)
count_models latin5_r008 via (Latin.fibre_card_of_check (n := 5) (r := ![1, 4, 0, 2, 3])) "data/lat5_r008.pog" "data/lat5_r008.lrat" (count := 6)
count_models latin5_r009 via (Latin.fibre_card_of_check (n := 5) (r := ![1, 4, 3, 0, 2])) "data/lat5_r009.pog" "data/lat5_r009.lrat" (count := 6)
count_models latin5_r010 via (Latin.fibre_card_of_check (n := 5) (r := ![1, 4, 3, 2, 0])) "data/lat5_r010.pog" "data/lat5_r010.lrat" (count := 4)

/-- The same fibre streamed: part B is the separate theorem `latin5_r000s.fwd`. -/
count_models +stream latin5_r000s via (Latin.fibre_card_of_check (n := 5) (r := ![1, 0, 3, 4, 2])) "data/lat5_r000.pog" "data/lat5_r000.lrat"

/-- Split: the fibres of the 11 admissible second rows (`Latin.card_eq_of_rows`; the row list
    is checked against the enumeration `Latin.rows 5` and the sum by `decide +kernel`). -/
theorem latin5_reduced : Nat.card {L : Fin 5 → Fin 5 → Fin 5 // IsReducedLatin L} = 56 :=
  Latin.card_eq_of_rows (n := 5) (by norm_num) 56
    [(![1, 0, 3, 4, 2], 4),
     (![1, 0, 4, 2, 3], 4),
     (![1, 2, 0, 4, 3], 4),
     (![1, 2, 3, 4, 0], 6),
     (![1, 2, 4, 0, 3], 6),
     (![1, 3, 0, 4, 2], 6),
     (![1, 3, 4, 0, 2], 4),
     (![1, 3, 4, 2, 0], 6),
     (![1, 4, 0, 2, 3], 6),
     (![1, 4, 3, 0, 2], 6),
     (![1, 4, 3, 2, 0], 4)]
    (List.forall_mem_cons.2 ⟨latin5_r000,
      List.forall_mem_cons.2 ⟨latin5_r001,
      List.forall_mem_cons.2 ⟨latin5_r002,
      List.forall_mem_cons.2 ⟨latin5_r003,
      List.forall_mem_cons.2 ⟨latin5_r004,
      List.forall_mem_cons.2 ⟨latin5_r005,
      List.forall_mem_cons.2 ⟨latin5_r006,
      List.forall_mem_cons.2 ⟨latin5_r007,
      List.forall_mem_cons.2 ⟨latin5_r008,
      List.forall_mem_cons.2 ⟨latin5_r009,
      List.forall_mem_cons.2 ⟨latin5_r010,
      List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel)
    (by decide +kernel)

/-- All Latin squares of order 5 (OEIS A002860: 161280 = 5! · 4! · 56), by the normalization
    bijection `Latin.normEquiv` (`Latin.card_latin_eq`). -/
theorem latin5_all : Nat.card {L : Fin 5 → Fin 5 → Fin 5 // IsLatin L} = 161280 := by
  rw [Latin.card_latin_eq, latin5_reduced]; decide

/-! The enumeration of admissible second rows: 11, 53 and 309 rows for n = 5, 6, 7. -/

example : rows 5 = [[1, 0, 3, 4, 2], [1, 0, 4, 2, 3], [1, 2, 0, 4, 3], [1, 2, 3, 4, 0],
    [1, 2, 4, 0, 3], [1, 3, 0, 4, 2], [1, 3, 4, 0, 2], [1, 3, 4, 2, 0], [1, 4, 0, 2, 3],
    [1, 4, 3, 0, 2], [1, 4, 3, 2, 0]] := by decide +kernel
example : (rows 6).length = 53 := by decide +kernel
example : (rows 7).length = 309 := by decide +kernel

/-! The side condition rejects a row list with a row missing (and a duplicated one in its place). -/

example : ([(![1, 0, 3, 4, 2], 4), (![1, 0, 4, 2, 3], 4), (![1, 2, 0, 4, 3], 4), (![1, 2, 3, 4, 0], 6), (![1, 2, 4, 0, 3], 6), (![1, 3, 0, 4, 2], 6), (![1, 3, 4, 0, 2], 4), (![1, 3, 4, 2, 0], 6), (![1, 4, 0, 2, 3], 6), (![1, 4, 3, 0, 2], 6), (![1, 0, 3, 4, 2], 4)] :
    List ((Fin 5 → Fin 5) × ℕ)).map (fun p => rowList p.1) ≠ rows 5 := by decide +kernel

/-! A wrong count hint and a certificate for another fibre are rejected; the theorem is not
    declared. -/

/--
error: count_models: the verified check rejected the certificate for 'latin5_bad':
  part A (count): the certificate's count is 4, not the hinted (count := 5)
'latin5_bad' was not declared (the reports come from unverified diagnostics).
-/
#guard_msgs in
count_models latin5_bad via (Latin.fibre_card_of_check (n := 5) (r := ![1, 0, 3, 4, 2])) "data/lat5_r000.pog" "data/lat5_r000.lrat" (count := 5)

/--
error: count_models: the verified check rejected the certificate for 'latin5_bad2':
  part B (LRAT refutation of F, the defining clauses and ¬root): step 57 (line 57 of a text LRAT file): clause 1085 (-36 0) does not follow by RUP from its 2 hints
  part C (every input clause implied by the POG): input clause 837 (40 0) is not implied by the POG: the assignment 1 -2 -3 -4 -5 -6 7 -8 -9 -10 -11 -12 13 -14 -15 -16 -17 -18 19 -20 -21 -22 -23 -24 … (101 more) satisfies the POG root 136 and falsifies the clause (the circuit has models that are not models of the formula)
'latin5_bad2' was not declared (the reports come from unverified diagnostics).
-/
#guard_msgs in
count_models latin5_bad2 via (Latin.fibre_card_of_check (n := 5) (r := ![1, 0, 4, 2, 3])) "data/lat5_r000.pog" "data/lat5_r000.lrat"

#print axioms latin5_reduced
#print axioms latin5_all
#print axioms latin5
