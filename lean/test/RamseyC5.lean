import CountCatcher

/-! Every graph on 5 vertices without a triangle and without an independent 3-set is a 5-cycle:
    Burnside over `Perm (Fin 5)` from certified counts
    gives one isomorphism class, and the 5-cycle is checked to lie in the family by evaluating the
    encoder (`decide +kernel`). Four of the seven cycle types fix no such graph (CaDiCaL LRAT
    refutations, the count-0 route). Certificates from `scripts/graph_orbits.py --family
    ramsey:3:3 --n 5`. -/

open SimpleGraph CountCatcher CountCatcher.GraphIso CountCatcher.CycleType

count_models ramsey33_5_fix_5 via (RamseyFam.fix_card_of_check (n := 5) (s := 3) (t := 3) (l := [5])) "data/r33_05_5.pog" "data/r33_05_5.lrat" (count := 2)
count_models ramsey33_5_fix_4 via (RamseyFam.fix_card_of_check (n := 5) (s := 3) (t := 3) (l := [4])) "data/r33_05_4_unsat.lrat"
count_models ramsey33_5_fix_3_2 via (RamseyFam.fix_card_of_check (n := 5) (s := 3) (t := 3) (l := [3, 2])) "data/r33_05_3_2_unsat.lrat"
count_models ramsey33_5_fix_3 via (RamseyFam.fix_card_of_check (n := 5) (s := 3) (t := 3) (l := [3])) "data/r33_05_3_unsat.lrat"
count_models ramsey33_5_fix_2_2 via (RamseyFam.fix_card_of_check (n := 5) (s := 3) (t := 3) (l := [2, 2])) "data/r33_05_2_2.pog" "data/r33_05_2_2.lrat" (count := 4)
count_models ramsey33_5_fix_2 via (RamseyFam.fix_card_of_check (n := 5) (s := 3) (t := 3) (l := [2])) "data/r33_05_2_unsat.lrat"
count_models ramsey33_5 via (RamseyFam.card_of_check (n := 5) (s := 3) (t := 3)) "data/r33_05_id.pog" "data/r33_05_id.lrat" (count := 12)

theorem ramsey33_5_orbits :
    Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin 5))
      {G : SimpleGraph (Fin 5) // G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3}) = 1 :=
  RamseyFam.card_orbits_eq 1
    [([5], 2), ([4], 0), ([3, 2], 0), ([3], 0), ([2, 2], 4), ([2], 0), ([], 12)]
    (List.forall_mem_cons.2 ⟨ramsey33_5_fix_5, List.forall_mem_cons.2 ⟨ramsey33_5_fix_4,
      List.forall_mem_cons.2 ⟨ramsey33_5_fix_3_2, List.forall_mem_cons.2 ⟨ramsey33_5_fix_3,
      List.forall_mem_cons.2 ⟨ramsey33_5_fix_2_2, List.forall_mem_cons.2 ⟨ramsey33_5_fix_2,
      List.forall_mem_cons.2 ⟨RamseyFam.fix_nil ramsey33_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide)

theorem ramsey33_5_isoClasses :
    Nat.card (Quot fun G H : {G : SimpleGraph (Fin 5) // G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3} =>
      Nonempty (G.1 ≃g H.1)) = 1 :=
  RamseyFam.card_isoClasses_eq ramsey33_5_orbits

/-- Every graph on 5 vertices without a triangle and without an independent 3-set is
    isomorphic to the 5-cycle. -/
theorem ramsey33_5_unique (G : SimpleGraph (Fin 5)) (h : G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3) :
    Nonempty (G ≃g cycleGraph 5) :=
  iso_of_card_isoClasses_eq_one ramsey33_5_isoClasses ⟨G, h⟩
    ⟨cycleGraph 5, ⟨cliqueFree_of_check _ 3 (by decide +kernel),
      compl_cliqueFree_of_check _ 3 (by decide +kernel)⟩⟩

/-- The membership check rejects a graph outside the family: the empty graph has an
    independent 3-set. -/
example : (cliqueClauses 5 3 true).all
    (fun c => c.eval (ext (modelOfDec (⊥ : SimpleGraph (Fin 5))))) = false := by
  decide +kernel

#print axioms ramsey33_5_unique
