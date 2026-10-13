import CountCatcherMath.Family
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Family: total dominating sets (OEIS A303210 for the torus grid)

A vertex set `S` of a graph is totally dominating if every vertex has a neighbour in `S` (open
neighbourhoods; vertices of `S` included).

Generic encoder over neighbour lists `N : Fin k → List (Fin k)`: one positive clause
`⋁_{u ∈ N v} x_u` per vertex `v`, in the order of `v`, literals in the order of `N v`. No auxiliary
variables. Family lemma (`equiv`): models ≃ sets `s` with `∀ v, ∃ u ∈ s, u ∈ N v`. A graph `G` on
any `α` enters through a numbering `e : α ≃ Fin k` and a proof `hN` that the lists are its
neighbourhoods (`graphEquiv`, `card_of_check`); `hN` can be a general lemma or, for one instance,
`decide`.

Instance: the n × n torus `cycleGraph n □ cycleGraph n` of Mathlib, `n = m + 2`. Vertex `(r, c)`
is variable `r * n + c` (`finProdFinEquiv`, row-major), and the neighbour lists are sorted, as in
`scripts/showcase/oeis/gen_A303210.py`, so the exported CNF is the generator's clause for clause.
`hN` holds for every `n ≥ 2` (`torusNbrs_spec`, from Mathlib's `cycleGraph_neighborSet`), so no
per-instance check is needed.
-/

open Std.Sat SimpleGraph

namespace CountCatcher.TotalDom

variable {k : ℕ}

/-- One clause per vertex `v`: some vertex of the list `N v` is chosen. -/
def clauses (N : Fin k → List (Fin k)) : List (CNF.Clause ℕ) :=
  (List.finRange k).map fun v => (N v).map fun u => (u.val, true)

/-- The CNF whose models are the sets meeting every list `N v`. -/
def cnf (N : Fin k → List (Fin k)) : CNF ℕ := ⟨(clauses N).toArray⟩

theorem eval_iff (N : Fin k → List (Fin k)) (a : Fin k → Bool) :
    (cnf N).eval (ext a) = true ↔ ∀ v, ∃ u ∈ N v, a u = true := by
  have hext : ∀ u : Fin k, ext a u.val = a u := fun u => by simp [ext]
  unfold CNF.eval
  rw [Array.all_eq_true_iff_forall_mem]
  simp [cnf, clauses, CNF.Clause.eval, hext]

/-- Family lemma on `Fin k`: models of the encoder are the sets meeting every list. -/
def equiv (N : Fin k → List (Fin k)) :
    {a : Fin k → Bool // (cnf N).eval (ext a) = true} ≃
      {s : Finset (Fin k) // ∀ v, ∃ u ∈ s, u ∈ N v} where
  toFun a := ⟨Finset.univ.filter (fun i => a.1 i = true), fun v => by
    obtain ⟨u, hu, hau⟩ := (eval_iff N a.1).1 a.2 v
    exact ⟨u, by simp [hau], hu⟩⟩
  invFun s := ⟨fun i => decide (i ∈ s.1), by
    rw [eval_iff]
    intro v
    obtain ⟨u, hus, hu⟩ := s.2 v
    exact ⟨u, hu, by simpa using hus⟩⟩
  left_inv a := by ext i; simp
  right_inv s := by ext i; simp

/-- Transport to a graph `G` on `α`, numbered by `e`, whose neighbourhoods are the lists. -/
def graphEquiv {α : Type*} [DecidableEq α] (G : SimpleGraph α) (e : α ≃ Fin k)
    (N : Fin k → List (Fin k)) (hN : ∀ v w, G.Adj v w ↔ e w ∈ N (e v)) :
    {s : Finset (Fin k) // ∀ v, ∃ u ∈ s, u ∈ N v} ≃
      {S : Finset α // ∀ v, ∃ u ∈ S, G.Adj v u} where
  toFun s := ⟨s.1.map e.symm.toEmbedding, fun v => by
    obtain ⟨u, hus, hu⟩ := s.2 (e v)
    refine ⟨e.symm u, by simpa using hus, ?_⟩
    rw [hN]; simpa using hu⟩
  invFun S := ⟨S.1.map e.toEmbedding, fun v => by
    obtain ⟨u, huS, hu⟩ := S.2 (e.symm v)
    refine ⟨e u, by simpa using huS, ?_⟩
    have := (hN _ _).1 hu
    simpa using this⟩
  left_inv s := by ext x; simp
  right_inv S := by ext x; simp

/-- A certificate for the encoder counts the total dominating sets of any graph `G` whose
    neighbourhoods are the lists `N` under the numbering `e`. -/
theorem card_of_check {α : Type*} [DecidableEq α] (G : SimpleGraph α) (e : α ≃ Fin k)
    (N : Fin k → List (Fin k)) (hN : ∀ v w, G.Adj v w ↔ e w ∈ N (e v))
    {pogStr lratStr : String} {C : ℕ} (h : checkAll k (cnf N) pogStr lratStr C = true) :
    Nat.card {S : Finset α // ∀ v, ∃ u ∈ S, G.Adj v u} = C :=
  Family.card_of_check ((equiv N).trans (graphEquiv G e N hN)) h

/-- The same with part B as a separate (streamed) refutation, for large certificates. -/
theorem card_of_checkAC {α : Type*} [DecidableEq α] (G : SimpleGraph α) (e : α ≃ Fin k)
    (N : Fin k → List (Fin k)) (hN : ∀ v w, G.Adj v w ↔ e w ∈ N (e v))
    {pogStr : String} {C : ℕ} (h : checkAllAC k (cnf N) pogStr C = true)
    (hB : (fwdCnfOf (cnf N) pogStr).Unsat) :
    Nat.card {S : Finset α // ∀ v, ∃ u ∈ S, G.Adj v u} = C :=
  Family.card_of_checkAC ((equiv N).trans (graphEquiv G e N hN)) h hB

/-! ## The n × n torus `cycleGraph n □ cycleGraph n`, `n = m + 2` -/

/-- The four torus neighbours of `(r, c)`. -/
def torusNb (m : ℕ) (x : Fin (m + 2) × Fin (m + 2)) : List (Fin (m + 2) × Fin (m + 2)) :=
  [(x.1 - 1, x.2), (x.1 + 1, x.2), (x.1, x.2 - 1), (x.1, x.2 + 1)]

theorem cycleGraph_adj_iff {m : ℕ} (a b : Fin (m + 2)) :
    (cycleGraph (m + 2)).Adj a b ↔ b = a - 1 ∨ b = a + 1 := by
  rw [← mem_neighborSet, cycleGraph_neighborSet]; simp

theorem torus_adj_iff (m : ℕ) (v w : Fin (m + 2) × Fin (m + 2)) :
    (cycleGraph (m + 2) □ cycleGraph (m + 2)).Adj v w ↔ w ∈ torusNb m v := by
  obtain ⟨r, c⟩ := v
  obtain ⟨r', c'⟩ := w
  simp only [boxProd_adj, cycleGraph_adj_iff, torusNb, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq]
  constructor
  · rintro (⟨h | h, rfl⟩ | ⟨h | h, rfl⟩) <;> simp [h]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

/-- Neighbour lists of the torus on `Fin (n * n)`, row-major numbering, sorted increasingly. -/
def torusNbrs (m : ℕ) (i : Fin ((m + 2) * (m + 2))) : List (Fin ((m + 2) * (m + 2))) :=
  ((torusNb m (finProdFinEquiv.symm i)).map finProdFinEquiv).mergeSort fun a b => decide (a ≤ b)

/-- The lists are the torus neighbourhoods, for every `n = m + 2`. -/
theorem torusNbrs_spec (m : ℕ) (v w : Fin (m + 2) × Fin (m + 2)) :
    (cycleGraph (m + 2) □ cycleGraph (m + 2)).Adj v w ↔
      finProdFinEquiv w ∈ torusNbrs m (finProdFinEquiv v) := by
  rw [torus_adj_iff]
  simp [torusNbrs, List.mem_mergeSort]

/-- A certificate for the torus encoder counts the total dominating sets of the torus. -/
theorem torus_card_of_check {m : ℕ} {pogStr lratStr : String} {C : ℕ}
    (h : checkAll ((m + 2) * (m + 2)) (cnf (torusNbrs m)) pogStr lratStr C = true) :
    Nat.card {S : Finset (Fin (m + 2) × Fin (m + 2)) //
      ∀ v, ∃ u ∈ S, (cycleGraph (m + 2) □ cycleGraph (m + 2)).Adj v u} = C :=
  card_of_check _ finProdFinEquiv _ (torusNbrs_spec m) h

/-- The same with part B as a separate (streamed) refutation, for large certificates. -/
theorem torus_card_of_checkAC {m : ℕ} {pogStr : String} {C : ℕ}
    (h : checkAllAC ((m + 2) * (m + 2)) (cnf (torusNbrs m)) pogStr C = true)
    (hB : (fwdCnfOf (cnf (torusNbrs m)) pogStr).Unsat) :
    Nat.card {S : Finset (Fin (m + 2) × Fin (m + 2)) //
      ∀ v, ∃ u ∈ S, (cycleGraph (m + 2) □ cycleGraph (m + 2)).Adj v u} = C :=
  card_of_checkAC _ finProdFinEquiv _ (torusNbrs_spec m) h hB

end CountCatcher.TotalDom
