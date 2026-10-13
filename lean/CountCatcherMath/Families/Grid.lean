import CountCatcherMath.Families.IndepSet
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The n × n grid graph (Mathlib's `pathGraph n □ pathGraph n`) on `Fin (n * n)`

Vertex `(r, c)` is variable `finProdFinEquiv (r, c) = r * n + c` (row-major, as in
`scripts/gen_indep.py`). Independent sets of the grid are counted through
`IndepSet.card_of_check` and transported back to `Fin n × Fin n`.
-/

open SimpleGraph

namespace CountCatcher

instance gridDecidable (n : ℕ) : DecidableRel (pathGraph n □ pathGraph n).Adj := fun x y =>
  decidable_of_iff ((x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val) ∧ x.2 = y.2 ∨
      (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val) ∧ x.1 = y.1)
    (by simp [boxProd_adj, pathGraph_adj])

/-- The grid graph on `Fin (n * n)`. -/
def gridGraph (n : ℕ) : SimpleGraph (Fin (n * n)) :=
  (pathGraph n □ pathGraph n).comap finProdFinEquiv.symm

instance (n : ℕ) : DecidableRel (gridGraph n).Adj := fun u v =>
  (inferInstance : Decidable ((pathGraph n □ pathGraph n).Adj
    (finProdFinEquiv.symm u) (finProdFinEquiv.symm v)))

/-- Independent sets are preserved by relabelling vertices along an equivalence. -/
def indepSetsComapEquiv {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (G : SimpleGraph α) :
    {s : Finset β // (G.comap e.symm).IsIndepSet (s : Set β)} ≃
      {s : Finset α // G.IsIndepSet (s : Set α)} where
  toFun s := ⟨s.1.map e.symm.toEmbedding, by
    intro u hu v hv huv hadj
    simp only [Finset.coe_map, Equiv.coe_toEmbedding, Set.mem_image, Finset.mem_coe] at hu hv
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    exact s.2 hu' hv' (fun h => huv (by rw [h])) (by simpa using hadj)⟩
  invFun s := ⟨s.1.map e.toEmbedding, by
    intro u hu v hv huv hadj
    simp only [Finset.coe_map, Equiv.coe_toEmbedding, Set.mem_image, Finset.mem_coe] at hu hv
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    exact s.2 hu' hv' (fun h => huv (by rw [h])) (by simpa using hadj)⟩
  left_inv s := by ext x; simp
  right_inv s := by ext x; simp

/-- A certificate for the grid encoder counts the independent sets of Mathlib's grid. -/
theorem grid_card_of_check {n : ℕ} {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (n * n) (IndepSet.cnf (gridGraph n)) pogStr lratStr N = true) :
    Nat.card {s : Finset (Fin n × Fin n) // (pathGraph n □ pathGraph n).IsIndepSet (s : Set _)} = N := by
  rw [← Nat.card_congr (indepSetsComapEquiv finProdFinEquiv _)]
  exact IndepSet.card_of_check (gridGraph n) h

/-- The same with part B as a separate (streamed) refutation, for large certificates. -/
theorem grid_card_of_checkAC {n : ℕ} {pogStr : String} {N : ℕ}
    (h : checkAllAC (n * n) (IndepSet.cnf (gridGraph n)) pogStr N = true)
    (hB : (fwdCnfOf (IndepSet.cnf (gridGraph n)) pogStr).Unsat) :
    Nat.card {s : Finset (Fin n × Fin n) // (pathGraph n □ pathGraph n).IsIndepSet (s : Set _)} = N := by
  rw [← Nat.card_congr (indepSetsComapEquiv finProdFinEquiv _)]
  exact IndepSet.card_of_checkAC (gridGraph n) h hB

end CountCatcher
