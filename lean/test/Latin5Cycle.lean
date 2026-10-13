import CountCatcherMath.Command
import CountCatcherMath.Families.LatinCycle

/-! Reduced Latin squares of order 5 (56) through the cycle types of the second row
    (`CountCatcherMath/Families/LatinCycle.lean`): the 11 admissible second rows fall into two classes,
    `[3, 2]` (5 rows, representative `10342`) and `[5]` (6 rows, representative `12340`). The first
    fibre is certified directly; the second is split by the cells `(2, 1), (2, 2)` of the third row
    into 7 parts, three of them empty (CaDiCaL refutations). Certificates from
    `scripts/showcase/latin_cycles.py --n 5 --k 2 --split 5` (`data/lat5c_*`). -/

open CountCatcher CountCatcher.Latin

count_models latin5c_c0_fibre via (Latin.fibre_card_of_check (n := 5) (r := ![1, 0, 3, 4, 2])) "data/lat5c_c0_fibre.pog" "data/lat5c_c0_fibre.lrat" (count := 4)
count_models latin5c_c1_0000 via (Latin.cell_card_of_check (n := 5) (r := ![1, 2, 3, 4, 0]) (t := [0, 1])) "data/lat5c_c1_0000.lrat"
count_models latin5c_c1_0001 via (Latin.cell_card_of_check (n := 5) (r := ![1, 2, 3, 4, 0]) (t := [0, 4])) "data/lat5c_c1_0001.pog" "data/lat5c_c1_0001.lrat" (count := 2)
count_models latin5c_c1_0002 via (Latin.cell_card_of_check (n := 5) (r := ![1, 2, 3, 4, 0]) (t := [3, 0])) "data/lat5c_c1_0002.lrat"
count_models latin5c_c1_0003 via (Latin.cell_card_of_check (n := 5) (r := ![1, 2, 3, 4, 0]) (t := [3, 1])) "data/lat5c_c1_0003.lrat"
count_models latin5c_c1_0004 via (Latin.cell_card_of_check (n := 5) (r := ![1, 2, 3, 4, 0]) (t := [3, 4])) "data/lat5c_c1_0004.pog" "data/lat5c_c1_0004.lrat" (count := 1)
count_models latin5c_c1_0005 via (Latin.cell_card_of_check (n := 5) (r := ![1, 2, 3, 4, 0]) (t := [4, 0])) "data/lat5c_c1_0005.pog" "data/lat5c_c1_0005.lrat" (count := 1)
count_models latin5c_c1_0006 via (Latin.cell_card_of_check (n := 5) (r := ![1, 2, 3, 4, 0]) (t := [4, 1])) "data/lat5c_c1_0006.pog" "data/lat5c_c1_0006.lrat" (count := 2)

/-- The parts of the fibre of `12340`: the admissible fillings of the cells `(2, 1), (2, 2)`. -/
def parts : List (List ℕ × ℕ) :=
  [([0, 1], 0), ([0, 4], 2), ([3, 0], 0), ([3, 1], 0), ([3, 4], 1), ([4, 0], 1), ([4, 1], 2)]

/-- The fibre of the representative `12340` (cycle type `[5]`) from its 7 parts. -/
theorem latin5c_fibre1 :
    Nat.card {L : Fin 5 → Fin 5 → Fin 5 // IsReducedLatin L ∧ L 1 = ![1, 2, 3, 4, 0]} = 6 :=
  Latin.fibre_card_eq_of_cells (by norm_num) ![1, 2, 3, 4, 0] 2 (by norm_num) 6 parts
    (List.forall_mem_cons.2 ⟨latin5c_c1_0000, List.forall_mem_cons.2 ⟨latin5c_c1_0001,
      List.forall_mem_cons.2 ⟨latin5c_c1_0002, List.forall_mem_cons.2 ⟨latin5c_c1_0003,
      List.forall_mem_cons.2 ⟨latin5c_c1_0004, List.forall_mem_cons.2 ⟨latin5c_c1_0005,
      List.forall_mem_cons.2 ⟨latin5c_c1_0006, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel)
    (by decide +kernel)

/-- Every admissible second row with a permutation onto its representative and the class. -/
def assign : List (List ℕ × List ℕ × ℕ) :=
  [([1, 0, 3, 4, 2], [0, 1, 2, 3, 4], 0),
   ([1, 0, 4, 2, 3], [0, 1, 2, 4, 3], 0),
   ([1, 2, 0, 4, 3], [2, 3, 4, 0, 1], 0),
   ([1, 2, 3, 4, 0], [0, 1, 2, 3, 4], 1),
   ([1, 2, 4, 0, 3], [0, 1, 2, 4, 3], 1),
   ([1, 3, 0, 4, 2], [0, 1, 4, 2, 3], 1),
   ([1, 3, 4, 0, 2], [2, 3, 0, 4, 1], 0),
   ([1, 3, 4, 2, 0], [0, 1, 3, 2, 4], 1),
   ([1, 4, 0, 2, 3], [0, 1, 4, 3, 2], 1),
   ([1, 4, 3, 0, 2], [0, 1, 3, 4, 2], 1),
   ([1, 4, 3, 2, 0], [2, 3, 0, 1, 4], 0)]

/-- The reduced Latin squares of order 5 from the two class representatives: 5 · 4 + 6 · 6. -/
theorem latin5c_reduced : Nat.card {L : Fin 5 → Fin 5 → Fin 5 // IsReducedLatin L} = 56 :=
  Latin.card_eq_of_classes (by norm_num) 56 [(![1, 0, 3, 4, 2], 4), (![1, 2, 3, 4, 0], 6)]
    (List.forall_mem_cons.2 ⟨latin5c_c0_fibre,
      List.forall_mem_cons.2 ⟨latin5c_fibre1, List.forall_mem_nil _⟩⟩)
    assign (by decide +kernel) (by decide +kernel)

/-- All Latin squares of order 5 (OEIS A002860). -/
theorem latin5c_all : Nat.card {L : Fin 5 → Fin 5 → Fin 5 // IsLatin L} = 161280 := by
  rw [Latin.card_latin_eq, latin5c_reduced]; decide

#print axioms latin5c_reduced
#print axioms latin5c_all

/-! The side conditions reject a wrong permutation, a missing class (an index without a
    representative), a missing row (the class of `[5]` one row short), a wrong representative
    (a row of type `[3, 2]` sent to the `[5]` class), an incomplete list of parts and a wrong
    total. -/

def reps : List (List ℕ) := [[1, 0, 3, 4, 2], [1, 2, 3, 4, 0]]

example : classCheck 5 reps assign = true := by decide
example : classCheck 5 reps (assign.set 4 ([1, 2, 4, 0, 3], [0, 1, 2, 3, 4], 1)) = false := by
  decide
example : classCheck 5 [[1, 0, 3, 4, 2]] assign = false := by decide
example : classCheck 5 reps (assign.eraseIdx 9) = false := by decide
example : classCheck 5 reps (assign.set 1 ([1, 0, 4, 2, 3], [0, 1, 2, 4, 3], 1)) = false := by
  decide
example : parts.map Prod.fst = thirdRows 5 [1, 2, 3, 4, 0] 2 := by decide
example : (parts.eraseIdx 4).map Prod.fst ≠ thirdRows 5 [1, 2, 3, 4, 0] 2 := by decide
example : (assign.map fun a => ([4, 6].getD a.2.2 0)).sum ≠ 55 := by decide
