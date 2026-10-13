import CountCatcherMath.Command
import CountCatcherMath.Families.DedekindCorner

/-! The Dedekind number M(5) = 7581 by the 10 S_3-classes of the lower
    corner (`CountCatcherMath/Families/DedekindCorner.lean`), the shape of the M(8) run:
    side data and side checks by `decide +kernel`, one `count_models` leaf per class
    (`cube (Dedekind.cnf (n + 2)) (lits n r)`), split classes by a `SplitTree` of
    sub-cubes, the assembly `card_eq_of_classes` with the certified M(n). Data from
    `scripts/showcase/dedekind_corner.py --n 3 --emit-test` (`data/ded5c_*`). -/

open CountCatcher CountCatcher.DedekindCorner

set_option maxRecDepth 100000

namespace Ded5C

/-- Delta-swap table: shift and mask per adjacent transposition. -/
def T : List (ℕ × ℕ) := [
    (1, 34),
    (2, 12)]
/-- Monotonicity table: shift and mask per coordinate. -/
def Ls : List (ℕ × ℕ) := [
    (1, 85),
    (2, 51),
    (4, 15)]
/-- The walk through all 6 permutations (SJT). -/
def P : List ℕ := [
    1, 0, 1, 0, 1]

theorem hT : tableOk 3 T = true := by decide +kernel
theorem hL : monoTableOk 3 Ls = true := by decide +kernel
theorem hP : pathOk 3 P = true := by decide +kernel

/-- Classes 0 to 3: (representative, orbit size). -/
def Q000 : List (ℕ × ℕ) := [
    (0, 1), (128, 1), (136, 3), (168, 3)]
/-- Classes 4 to 7: (representative, orbit size). -/
def Q001 : List (ℕ × ℕ) := [
    (170, 3), (232, 1), (234, 3), (238, 3)]
/-- Classes 8 to 9: (representative, orbit size). -/
def Q002 : List (ℕ × ℕ) := [
    (254, 1), (255, 1)]

theorem chk000 : Q000.all (repOk 3 T Ls P) = true := by decide +kernel
theorem chk001 : Q001.all (repOk 3 T Ls P) = true := by decide +kernel
theorem chk002 : Q002.all (repOk 3 T Ls P) = true := by decide +kernel

end Ded5C

count_models Ded5C.dedekind3 via (Dedekind.card_of_check (n := 3)) "data/ded5c_m3.pog" "data/ded5c_m3.lrat" (count := 20)

count_models Ded5C.l_c00000_00 via (CountCatcher.DedekindCorner.leaf_card_of_check (n := 3) (ls := (23, false) :: (15, false) :: lits 3 0)) "data/ded5c_c00000_00.pog" "data/ded5c_c00000_00.lrat" (count := 20)
count_models Ded5C.l_c00000_01 via (CountCatcher.DedekindCorner.leaf_card_of_check (n := 3) (ls := (23, true) :: (15, false) :: lits 3 0)) "data/ded5c_c00000_01.pog" "data/ded5c_c00000_01.lrat" (count := 148)
count_models Ded5C.l_c00000_10 via (CountCatcher.DedekindCorner.leaf_card_of_check (n := 3) (ls := (23, false) :: (15, true) :: lits 3 0)) "data/ded5c_c00000_10.pog" "data/ded5c_c00000_10.lrat" (count := 148)
count_models Ded5C.l_c00000_11 via (CountCatcher.DedekindCorner.leaf_card_of_check (n := 3) (ls := (23, true) :: (15, true) :: lits 3 0)) "data/ded5c_c00000_11.pog" "data/ded5c_c00000_11.lrat" (count := 1692)
count_models Ded5C.l_c00001 via (CountCatcher.DedekindCorner.leaf_card_of_check (n := 3) (ls := lits 3 128)) "data/ded5c_c00001.pog" "data/ded5c_c00001.lrat" (count := 1692)
count_models Ded5C.l_c00002 via (CountCatcher.DedekindCorner.leaf_card_of_check (n := 3) (ls := lits 3 136)) "data/ded5c_c00002.pog" "data/ded5c_c00002.lrat" (count := 714)
count_models Ded5C.l_c00003 via (CountCatcher.DedekindCorner.leaf_card_of_check (n := 3) (ls := lits 3 168)) "data/ded5c_c00003.pog" "data/ded5c_c00003.lrat" (count := 361)
count_models Ded5C.l_c00004 via (CountCatcher.DedekindCorner.leaf_card_of_check (n := 3) (ls := lits 3 170)) "data/ded5c_c00004.pog" "data/ded5c_c00004.lrat" (count := 84)
count_models Ded5C.l_c00005 via (CountCatcher.DedekindCorner.leaf_card_of_check (n := 3) (ls := lits 3 232)) "data/ded5c_c00005.pog" "data/ded5c_c00005.lrat" (count := 206)
count_models Ded5C.l_c00006 via (CountCatcher.DedekindCorner.leaf_card_of_check (n := 3) (ls := lits 3 234)) "data/ded5c_c00006.pog" "data/ded5c_c00006.lrat" (count := 50)
count_models Ded5C.l_c00007 via (CountCatcher.DedekindCorner.leaf_card_of_check (n := 3) (ls := lits 3 238)) "data/ded5c_c00007.pog" "data/ded5c_c00007.lrat" (count := 14)
count_models Ded5C.l_c00008 via (CountCatcher.DedekindCorner.leaf_card_of_check (n := 3) (ls := lits 3 254)) "data/ded5c_c00008.pog" "data/ded5c_c00008.lrat" (count := 5)
count_models Ded5C.l_c00009 via (CountCatcher.DedekindCorner.leaf_card_of_check (n := 3) (ls := lits 3 255)) "data/ded5c_c00009.pog" "data/ded5c_c00009.lrat" (count := 1)

/-- Class 0 (0x0), split into 4 sub-cubes. -/
theorem Ded5C.cls00000 : leafCount 3 0 = 2008 :=
  leafCount_of_tree (n := 3) (m := 0) (SplitTree.node 15 (SplitTree.node 23 (SplitTree.leaf 1692) (SplitTree.leaf 148)) (SplitTree.node 23 (SplitTree.leaf 148) (SplitTree.leaf 20)))
    (SplitTree.Holds.mk_node (SplitTree.Holds.mk_node (SplitTree.Holds.mk_leaf Ded5C.l_c00000_11) (SplitTree.Holds.mk_leaf Ded5C.l_c00000_10)) (SplitTree.Holds.mk_node (SplitTree.Holds.mk_leaf Ded5C.l_c00000_01) (SplitTree.Holds.mk_leaf Ded5C.l_c00000_00)))
    rfl

theorem Ded5C.sum000 :
    (Ded5C.Q000.map fun p => p.2 * leafCount 3 p.1).sum = 6925 :=
  Eq.trans (chunkSum_cons (n := 3) Ded5C.cls00000
    (chunkSum_cons (n := 3) Ded5C.l_c00001
    (chunkSum_cons (n := 3) Ded5C.l_c00002
    (chunkSum_cons (n := 3) Ded5C.l_c00003
    (chunkSum_nil))))) (by decide +kernel)

theorem Ded5C.sum001 :
    (Ded5C.Q001.map fun p => p.2 * leafCount 3 p.1).sum = 650 :=
  Eq.trans (chunkSum_cons (n := 3) Ded5C.l_c00004
    (chunkSum_cons (n := 3) Ded5C.l_c00005
    (chunkSum_cons (n := 3) Ded5C.l_c00006
    (chunkSum_cons (n := 3) Ded5C.l_c00007
    (chunkSum_nil))))) (by decide +kernel)

theorem Ded5C.sum002 :
    (Ded5C.Q002.map fun p => p.2 * leafCount 3 p.1).sum = 6 :=
  Eq.trans (chunkSum_cons (n := 3) Ded5C.l_c00008
    (chunkSum_cons (n := 3) Ded5C.l_c00009
    (chunkSum_nil))) (by decide +kernel)

/-- The Dedekind number M(5) by the 10 classes of the lower corner (S_3-classes of D_3). -/
theorem dedekind5c : Nat.card {f : (Fin 5 → Bool) → Bool // Monotone f} = 7581 :=
  (card_eq_of_classes 3 Ded5C.T Ded5C.Ls Ded5C.hT Ded5C.hL Ded5C.P Ded5C.hP
    [(Ded5C.Q000, 6925), (Ded5C.Q001, 650), (Ded5C.Q002, 6)]
    (List.forall_mem_cons.2 ⟨Ded5C.chk000,
    List.forall_mem_cons.2 ⟨Ded5C.chk001,
    List.forall_mem_cons.2 ⟨Ded5C.chk002,
    List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel)
    (Ded5C.dedekind3.trans (by decide +kernel))
    (List.forall_mem_cons.2 ⟨Ded5C.sum000,
    List.forall_mem_cons.2 ⟨Ded5C.sum001,
    List.forall_mem_cons.2 ⟨Ded5C.sum002,
    List.forall_mem_nil _⟩⟩⟩)).trans
    (by decide +kernel)

#print axioms dedekind5c

/-! The side check rejects a wrong orbit size, an orbit element that is not the
    smallest, and a non-monotone mask; the representatives must increase strictly. -/

example : repOk 3 Ded5C.T Ded5C.Ls Ded5C.P (136, 4) = false := by decide +kernel
example : repOk 3 Ded5C.T Ded5C.Ls Ded5C.P (192, 3) = false := by decide +kernel
example : repOk 3 Ded5C.T Ded5C.Ls Ded5C.P (1, 1) = false := by decide +kernel
example : sortedB [128, 0] = false := by decide

