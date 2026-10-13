import CountCatcher
import CountCatcherMath.Families.GraphIso

/-! Graphs on 5 vertices without a 4-clique: 958 labelled, 29 up to isomorphism. The
    labelled count comes from a tree of cell
    splits (`GraphIso.card_eq_of_cell`): the root is the neighbourhood of vertex `0` in
    `[1, 2, 3, 4]`, the child `N(0) = {1, 2, 3}` is refined inside `{1, 2, 3}` (vertex 1, then
    vertex 2), two leaves are relabellings of others (`card_sat_iso`), one leaf (a triangle in
    `N(0)`) is an LRAT refutation; the tree replaces the identity term of Burnside's sum.
    Certificates from `scripts/graph_orbits.py --family clique:4 --n 5 --tree 3 --sat-first 30`. -/

open SimpleGraph CountCatcher CountCatcher.GraphIso CountCatcher.CycleType

set_option maxRecDepth 100000



def clique4_5_p0 : GraphIso.Pattern 5 := []
def clique4_5_p1 : GraphIso.Pattern 5 := clique4_5_p0 ++ GraphIso.star 0 [1, 2, 3, 4] 0
def clique4_5_p2 : GraphIso.Pattern 5 := clique4_5_p0 ++ GraphIso.star 0 [1, 2, 3, 4] 1
def clique4_5_p3 : GraphIso.Pattern 5 := clique4_5_p0 ++ GraphIso.star 0 [1, 2, 3, 4] 2
def clique4_5_p4 : GraphIso.Pattern 5 := clique4_5_p0 ++ GraphIso.star 0 [1, 2, 3, 4] 3
def clique4_5_p5 : GraphIso.Pattern 5 := clique4_5_p0 ++ GraphIso.star 0 [1, 2, 3, 4] 4
def clique4_5_p6 : GraphIso.Pattern 5 := clique4_5_p4 ++ GraphIso.star 1 [2, 3] 0
def clique4_5_p7 : GraphIso.Pattern 5 := clique4_5_p4 ++ GraphIso.star 1 [2, 3] 1
def clique4_5_p8 : GraphIso.Pattern 5 := clique4_5_p4 ++ GraphIso.star 1 [2, 3] 2
def clique4_5_p9 : GraphIso.Pattern 5 := clique4_5_p6 ++ GraphIso.star 2 [3] 0
def clique4_5_p10 : GraphIso.Pattern 5 := clique4_5_p6 ++ GraphIso.star 2 [3] 1
def clique4_5_p11 : GraphIso.Pattern 5 := clique4_5_p7 ++ GraphIso.star 2 [3] 0
def clique4_5_p12 : GraphIso.Pattern 5 := clique4_5_p7 ++ GraphIso.star 2 [3] 1
def clique4_5_p13 : GraphIso.Pattern 5 := clique4_5_p8 ++ GraphIso.star 2 [3] 0
def clique4_5_p14 : GraphIso.Pattern 5 := clique4_5_p8 ++ GraphIso.star 2 [3] 1

count_models clique4_5_t1 via (CliqueFreeFam.cube_card_of_check (n := 5) (s := 4) (α := clique4_5_p1)) "data/k4_05_t1.pog" "data/k4_05_t1.lrat" (count := 63)
count_models clique4_5_t2 via (CliqueFreeFam.cube_card_of_check (n := 5) (s := 4) (α := clique4_5_p2)) "data/k4_05_t2.pog" "data/k4_05_t2.lrat" (count := 63)
count_models clique4_5_t3 via (CliqueFreeFam.cube_card_of_check (n := 5) (s := 4) (α := clique4_5_p3)) "data/k4_05_t3.pog" "data/k4_05_t3.lrat" (count := 63)
count_models clique4_5_t5 via (CliqueFreeFam.cube_card_of_check (n := 5) (s := 4) (α := clique4_5_p5)) "data/k4_05_t5.pog" "data/k4_05_t5.lrat" (count := 41)
count_models clique4_5_t9 via (CliqueFreeFam.cube_card_of_check (n := 5) (s := 4) (α := clique4_5_p9)) "data/k4_05_t9.pog" "data/k4_05_t9.lrat" (count := 8)
count_models clique4_5_t10 via (CliqueFreeFam.cube_card_of_check (n := 5) (s := 4) (α := clique4_5_p10)) "data/k4_05_t10.pog" "data/k4_05_t10.lrat" (count := 8)
count_models clique4_5_t12 via (CliqueFreeFam.cube_card_of_check (n := 5) (s := 4) (α := clique4_5_p12)) "data/k4_05_t12.pog" "data/k4_05_t12.lrat" (count := 8)
count_models clique4_5_t14 via (CliqueFreeFam.cube_card_of_check (n := 5) (s := 4) (α := clique4_5_p14)) "data/k4_05_t14_unsat.lrat"

theorem clique4_5_t11 : Nat.card {x : {G : SimpleGraph (Fin 5) // G.CliqueFree 4} // GraphIso.Sat x.1 clique4_5_p11} = 8 :=
  CliqueFreeFam.card_sat_iso (n := 5) (s := 4) (GraphIso.swaps [(1, 3), (1, 2)]) (by decide +kernel) clique4_5_t10

theorem clique4_5_t13 : Nat.card {x : {G : SimpleGraph (Fin 5) // G.CliqueFree 4} // GraphIso.Sat x.1 clique4_5_p13} = 8 :=
  CliqueFreeFam.card_sat_iso (n := 5) (s := 4) (GraphIso.swaps [(1, 2)]) (by decide +kernel) clique4_5_t12

theorem clique4_5_t8 : Nat.card {x : {G : SimpleGraph (Fin 5) // G.CliqueFree 4} // GraphIso.Sat x.1 clique4_5_p8} = 8 :=
  CliqueFreeFam.card_eq_of_cell (n := 5) (s := 4) clique4_5_p8 2 [3] 8
    [(0, 8), (1, 0)]
    (List.forall_mem_cons.2 ⟨clique4_5_t13,
      List.forall_mem_cons.2 ⟨clique4_5_t14,
      List.forall_mem_nil _⟩⟩)
    (by decide +kernel)

theorem clique4_5_t7 : Nat.card {x : {G : SimpleGraph (Fin 5) // G.CliqueFree 4} // GraphIso.Sat x.1 clique4_5_p7} = 16 :=
  CliqueFreeFam.card_eq_of_cell (n := 5) (s := 4) clique4_5_p7 2 [3] 16
    [(0, 8), (1, 8)]
    (List.forall_mem_cons.2 ⟨clique4_5_t11,
      List.forall_mem_cons.2 ⟨clique4_5_t12,
      List.forall_mem_nil _⟩⟩)
    (by decide +kernel)

theorem clique4_5_t6 : Nat.card {x : {G : SimpleGraph (Fin 5) // G.CliqueFree 4} // GraphIso.Sat x.1 clique4_5_p6} = 16 :=
  CliqueFreeFam.card_eq_of_cell (n := 5) (s := 4) clique4_5_p6 2 [3] 16
    [(0, 8), (1, 8)]
    (List.forall_mem_cons.2 ⟨clique4_5_t9,
      List.forall_mem_cons.2 ⟨clique4_5_t10,
      List.forall_mem_nil _⟩⟩)
    (by decide +kernel)

theorem clique4_5_t4 : Nat.card {x : {G : SimpleGraph (Fin 5) // G.CliqueFree 4} // GraphIso.Sat x.1 clique4_5_p4} = 56 :=
  CliqueFreeFam.card_eq_of_cell (n := 5) (s := 4) clique4_5_p4 1 [2, 3] 56
    [(0, 16), (1, 16), (2, 8)]
    (List.forall_mem_cons.2 ⟨clique4_5_t6,
      List.forall_mem_cons.2 ⟨clique4_5_t7,
      List.forall_mem_cons.2 ⟨clique4_5_t8,
      List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel)

theorem clique4_5_t0 : Nat.card {x : {G : SimpleGraph (Fin 5) // G.CliqueFree 4} // GraphIso.Sat x.1 clique4_5_p0} = 958 :=
  CliqueFreeFam.card_eq_of_cell (n := 5) (s := 4) clique4_5_p0 0 [1, 2, 3, 4] 958
    [(0, 63), (1, 63), (2, 63), (3, 56), (4, 41)]
    (List.forall_mem_cons.2 ⟨clique4_5_t1,
      List.forall_mem_cons.2 ⟨clique4_5_t2,
      List.forall_mem_cons.2 ⟨clique4_5_t3,
      List.forall_mem_cons.2 ⟨clique4_5_t4,
      List.forall_mem_cons.2 ⟨clique4_5_t5,
      List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel)

/-- The labelled count, from the tree of cell splits. -/
theorem clique4_5 : Nat.card {G : SimpleGraph (Fin 5) // G.CliqueFree 4} = 958 :=
  CliqueFreeFam.card_of_root (n := 5) (s := 4) clique4_5_t0

count_models clique4_5_fix_5 via (CliqueFreeFam.fix_card_of_check (n := 5) (s := 4) (l := [5])) "data/k4_05_5.pog" "data/k4_05_5.lrat" (count := 3)
count_models clique4_5_fix_4 via (CliqueFreeFam.fix_card_of_check (n := 5) (s := 4) (l := [4])) "data/k4_05_4.pog" "data/k4_05_4.lrat" (count := 6)
count_models clique4_5_fix_3_2 via (CliqueFreeFam.fix_card_of_check (n := 5) (s := 4) (l := [3, 2])) "data/k4_05_3_2.pog" "data/k4_05_3_2.lrat" (count := 6)
count_models clique4_5_fix_3 via (CliqueFreeFam.fix_card_of_check (n := 5) (s := 4) (l := [3])) "data/k4_05_3.pog" "data/k4_05_3.lrat" (count := 10)
count_models clique4_5_fix_2_2 via (CliqueFreeFam.fix_card_of_check (n := 5) (s := 4) (l := [2, 2])) "data/k4_05_2_2.pog" "data/k4_05_2_2.lrat" (count := 58)
count_models clique4_5_fix_2 via (CliqueFreeFam.fix_card_of_check (n := 5) (s := 4) (l := [2])) "data/k4_05_2.pog" "data/k4_05_2.lrat" (count := 108)

/-- The number of graphs on 5 vertices without a 4-clique, up to relabelling (orbits of `Perm (Fin 5)`), by
    Burnside's lemma over the cycle types from the certified counts above. -/
theorem clique4_5_orbits :
    Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin 5))
      {G : SimpleGraph (Fin 5) // G.CliqueFree 4}) = 29 :=
  CliqueFreeFam.card_orbits_eq 29
    [([5], 3),
     ([4], 6),
     ([3, 2], 6),
     ([3], 10),
     ([2, 2], 58),
     ([2], 108),
     ([], 958)]
    (List.forall_mem_cons.2 ⟨clique4_5_fix_5,
      List.forall_mem_cons.2 ⟨clique4_5_fix_4,
      List.forall_mem_cons.2 ⟨clique4_5_fix_3_2,
      List.forall_mem_cons.2 ⟨clique4_5_fix_3,
      List.forall_mem_cons.2 ⟨clique4_5_fix_2_2,
      List.forall_mem_cons.2 ⟨clique4_5_fix_2,
      List.forall_mem_cons.2 ⟨CliqueFreeFam.fix_nil clique4_5,
      List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide)

/-- The number of isomorphism classes of graphs on 5 vertices without a 4-clique. -/
theorem clique4_5_isoClasses :
    Nat.card (Quot fun G H : {G : SimpleGraph (Fin 5) // G.CliqueFree 4} => Nonempty (G.1 ≃g H.1)) = 29 :=
  CliqueFreeFam.card_isoClasses_eq clique4_5_orbits


/-! The side conditions reject a wrong count, a list that is not a cell of the pattern (after
    `N(1) ∩ {2, 3} = {2}` the vertices 2 and 3 differ), a split vertex inside the cell, and a
    permutation that does not map one leaf onto the other. -/

example : checkCell clique4_5_p4 1 [2, 3] 57 [(0, 16), (1, 16), (2, 8)] = false := by decide +kernel
example : cellOk clique4_5_p7 [2, 3] = false := by decide +kernel
example : checkCell clique4_5_p4 2 [2, 3] 56 [(0, 16), (1, 16), (2, 8)] = false := by decide +kernel
example : patEquiv (relabel (swaps [(1, 2)]) clique4_5_p11) clique4_5_p10 = false := by decide +kernel

/-! A certificate for another cube is rejected: the certificate of leaf 9 (no edge in
    `{1, 2, 3}`) offered for leaf 10 (the edge 2–3), with the same count. -/

/--
error: count_models: the verified check rejected the certificate for 'clique4_5_bad':
  part B (LRAT refutation of F, the defining clauses and ¬root): step 1 (line 1 of a text LRAT file): clause 22 (11 0) does not follow by RUP from its 8 hints
  part C (every input clause implied by the POG): input clause 12 (8 0) is not implied by the POG: the assignment 1 2 3 -4 -5 -6 -8 satisfies the POG root 11 and falsifies the clause (the circuit has models that are not models of the formula)
'clique4_5_bad' was not declared (the reports come from unverified diagnostics).
-/
#guard_msgs in
count_models clique4_5_bad via (CliqueFreeFam.cube_card_of_check (n := 5) (s := 4) (α := clique4_5_p10)) "data/k4_05_t9.pog" "data/k4_05_t9.lrat" (count := 8)

/-- The requested form of the relabelling lemma: with `N(0) = {1, 2, 3}`, the graphs whose
    induced graph on `{1, 2, 3}` is `H` and those where it is `swap 1 3 • H` are equinumerous. -/
example (H : SimpleGraph (Fin 5)) :
    Nat.card {x : {G : SimpleGraph (Fin 5) // G.CliqueFree 4} //
        nbrs x.1 0 = {1, 2, 3} ∧ ∀ a ∈ ({1, 2, 3} : Finset (Fin 5)), ∀ b ∈ ({1, 2, 3} : Finset (Fin 5)),
          (x.1.Adj a b ↔ H.Adj a b)} =
      Nat.card {x : {G : SimpleGraph (Fin 5) // G.CliqueFree 4} //
        nbrs x.1 0 = {1, 2, 3} ∧ ∀ a ∈ ({1, 2, 3} : Finset (Fin 5)), ∀ b ∈ ({1, 2, 3} : Finset (Fin 5)),
          (x.1.Adj a b ↔ (Equiv.swap (1 : Fin 5) 3 • H).Adj a b)} :=
  card_nbrs_induce_eq CliqueFreeFam.hact 0 {1, 2, 3} (by decide) (Equiv.swap 1 3)
    (fun x hx => Equiv.swap_apply_of_ne_of_ne (by rintro rfl; simp at hx)
      (by rintro rfl; simp at hx)) H

#print axioms clique4_5_orbits
#print axioms clique4_5_isoClasses
#print axioms clique4_5
