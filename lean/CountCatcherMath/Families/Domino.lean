import CountCatcherMath.Families.Matching
import CountCatcherMath.Families.Grid

/-!
# Domino tilings of the R × C board = perfect matchings of Mathlib's grid graph

Vertices row-major; per cell the right edge, then the down edge (the order of
`scripts/gen_domino.py`, so its DIMACS files and certificates apply unchanged).
-/

open SimpleGraph

namespace CountCatcher.Domino

def verts (R C : ℕ) : List (Fin R × Fin C) :=
  (List.finRange R).flatMap fun r => (List.finRange C).map fun c => (r, c)

def edges (R C : ℕ) : List ((Fin R × Fin C) × (Fin R × Fin C)) :=
  (verts R C).flatMap fun v =>
    (if h : v.2.val + 1 < C then [(v, (v.1, ⟨v.2.val + 1, h⟩))] else []) ++
    (if h : v.1.val + 1 < R then [(v, (⟨v.1.val + 1, h⟩, v.2))] else [])

/-- The domino CNF of the R × C board. -/
def cnf (R C : ℕ) : Std.Sat.CNF ℕ := Matching.cnf (edges R C) (verts R C)

variable {R C : ℕ}

theorem verts_eq (R C : ℕ) : verts R C = List.finRange R ×ˢ List.finRange C := rfl

theorem mem_verts (v : Fin R × Fin C) : v ∈ verts R C := by
  rw [verts_eq]; exact List.mem_product.2 ⟨List.mem_finRange _, List.mem_finRange _⟩

theorem verts_nodup : (verts R C).Nodup := by
  rw [verts_eq]; exact (List.nodup_finRange R).product (List.nodup_finRange C)

theorem mem_edges {e : (Fin R × Fin C) × (Fin R × Fin C)} :
    e ∈ edges R C ↔ (e.1.1 = e.2.1 ∧ e.1.2.val + 1 = e.2.2.val) ∨
      (e.1.1.val + 1 = e.2.1.val ∧ e.1.2 = e.2.2) := by
  obtain ⟨⟨r, c⟩, ⟨r', c'⟩⟩ := e
  simp only [edges, List.mem_flatMap, List.mem_append]
  constructor
  · rintro ⟨v, -, h | h⟩
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
        exact Or.inl ⟨rfl, rfl⟩
      · simp at h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
        exact Or.inr ⟨rfl, rfl⟩
      · simp at h
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨(r, c), mem_verts _, Or.inl ?_⟩
      have : c.val + 1 < C := h2 ▸ c'.isLt
      rw [dif_pos this]
      simp only [List.mem_singleton, Prod.mk.injEq, true_and]
      exact ⟨h1.symm, Fin.ext h2.symm⟩
    · refine ⟨(r, c), mem_verts _, Or.inr ?_⟩
      have : r.val + 1 < R := h1 ▸ r'.isLt
      rw [dif_pos this]
      simp only [List.mem_singleton, Prod.mk.injEq, true_and]
      exact ⟨Fin.ext h1.symm, h2.symm⟩

theorem edges_adj {u v : Fin R × Fin C} :
    (pathGraph R □ pathGraph C).Adj u v ↔ (u, v) ∈ edges R C ∨ (v, u) ∈ edges R C := by
  rw [boxProd_adj, pathGraph_adj, pathGraph_adj, mem_edges, mem_edges]
  obtain ⟨r, c⟩ := u
  obtain ⟨r', c'⟩ := v
  simp only [Fin.ext_iff]
  omega

theorem edges_nodup : (edges R C).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun v _ => ?_, verts_nodup.imp fun {v w} hvw => ?_⟩
  · split <;> split <;> simp [Fin.ext_iff]
  · simp only [Function.onFun, List.disjoint_left, List.mem_append]
    intro e he he'
    have h1 : e.1 = v := by
      rcases he with he | he <;> split at he <;> simp_all
    have h2 : e.1 = w := by
      rcases he' with he' | he' <;> split at he' <;> simp_all
    exact hvw (h1.symm.trans h2)

/-- The edge and vertex lists of the board satisfy the listing condition of the family lemma. -/
theorem listing (R C : ℕ) :
    Matching.Listing (pathGraph R □ pathGraph C) (edges R C) (verts R C) where
  adj e he := edges_adj.2 (Or.inl he)
  nodup := by
    refine edges_nodup.map_on fun e he e' he' h => ?_
    have k := mem_edges.1 he
    have k' := mem_edges.1 he'
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := e
      obtain ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ := e'
      simp only [Prod.mk.injEq, Fin.ext_iff] at h1 h2 k k'
      omega
  complete u v h := by
    rcases edges_adj.1 h with h | h
    · exact List.mem_map.2 ⟨_, h, rfl⟩
    · exact List.mem_map.2 ⟨_, h, Sym2.eq_swap⟩
  verts := mem_verts

theorem card_of_check {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (edges R C).length (cnf R C) pogStr lratStr N = true) :
    Nat.card {M : (pathGraph R □ pathGraph C).Subgraph // M.IsPerfectMatching} = N :=
  Matching.card_of_check (listing R C) h

/-- The same with part B as a separate (streamed) refutation, for large certificates. -/
theorem card_of_checkAC {pogStr : String} {N : ℕ}
    (h : checkAllAC (edges R C).length (cnf R C) pogStr N = true)
    (hB : (fwdCnfOf (cnf R C) pogStr).Unsat) :
    Nat.card {M : (pathGraph R □ pathGraph C).Subgraph // M.IsPerfectMatching} = N :=
  Matching.card_of_checkAC (listing R C) h hB

end CountCatcher.Domino
