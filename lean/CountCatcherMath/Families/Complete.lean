import CountCatcherMath.Families.Matching

/-!
# New-family example: perfect matchings of the complete graph `K_n`

Through the generic matching layer (`Matching.cnf`, `Matching.Listing`): the family needs only
the edge list (all pairs `i < j`, lexicographic) and the proof that it lists every edge of `⊤`
once. `count_models … via (Matching.card_of_check (Complete.listing n))` then states
`Nat.card {M : (⊤ : SimpleGraph (Fin n)).Subgraph // M.IsPerfectMatching} = (n - 1)!!`.
-/

open SimpleGraph

namespace CountCatcher.Complete

/-- All edges `(i, j)` with `i < j`, lexicographic. -/
def edges (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i => ((List.finRange n).filter (i < ·)).map (i, ·)

theorem mem_edges {n : ℕ} {e : Fin n × Fin n} : e ∈ edges n ↔ e.1 < e.2 := by
  obtain ⟨i, j⟩ := e
  simp [edges]

theorem listing (n : ℕ) : Matching.Listing (⊤ : SimpleGraph (Fin n)) (edges n) (List.finRange n) where
  adj e he := (mem_edges.1 he).ne
  nodup := by
    refine List.Nodup.map_on (fun e he e' he' h => ?_) ?_
    · have k := mem_edges.1 he
      have k' := mem_edges.1 he'
      rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · rw [h1, h2] at k
        exact absurd k' (lt_asymm k)
    · refine List.nodup_flatMap.2 ⟨fun i _ => ?_, (List.nodup_finRange n).imp fun hij => ?_⟩
      · exact ((List.nodup_finRange n).filter _).map fun _ _ h => (Prod.mk.inj h).2
      · simp only [Function.onFun, List.disjoint_left, List.mem_map]
        rintro _ ⟨_, _, rfl⟩ ⟨_, _, h⟩
        exact hij (Prod.mk.inj h).1.symm
  complete u v h := by
    rcases lt_or_gt_of_ne h with h | h
    · exact List.mem_map.2 ⟨(u, v), mem_edges.2 h, rfl⟩
    · exact List.mem_map.2 ⟨(v, u), mem_edges.2 h, Sym2.eq_swap⟩
  verts := List.mem_finRange

end CountCatcher.Complete
