import CountCatcherMath.Families.Grid
import CountCatcherChecker.EdgeCnf
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Fin

/-!
# Independent sets of graphs without grid structure

Two ways to state the graph: an explicit edge list (`edgeGraph`, for random and benchmark
graphs), and the hypercube `Q_n` on bit vectors `Fin n → Bool` (Hamming distance one),
numbered in binary on `Fin (2 ^ n)` for the encoder (as in `scripts/gen_t5.py`).

For an edge list the family lemmas take the CNF as `edgeCnf l`, computed by the precompiled
`CountCatcher.edgeListCnf` from the pairs of `l`; `edgeCnf_eq` proves it equal to
`IndepSet.cnf (edgeGraph l)`, whose `k²` interpreted adjacency tests took 58 s on homer.
-/

open SimpleGraph Std.Sat

namespace CountCatcher

/-- The graph on `Fin k` whose edges are the entries of `l`. -/
def edgeGraph {k : ℕ} (l : List (Sym2 (Fin k))) : SimpleGraph (Fin k) :=
  fromEdgeSet {e | e ∈ l}

instance {k : ℕ} (l : List (Sym2 (Fin k))) : DecidableRel (edgeGraph l).Adj := fun u v =>
  inferInstanceAs (Decidable ((fromEdgeSet {e | e ∈ l}).Adj u v))

/-! ### The compiled encoder of an edge list -/

theorem getElem!_modify_list (t : Array (List Nat)) (i x : Nat) (f : List Nat → List Nat) :
    (t.modify i f)[x]! = if i = x ∧ x < t.size then f t[x]! else t[x]! := by
  by_cases hx : x < t.size
  · rw [getElem!_pos _ _ (by simpa [Array.size_modify] using hx), Array.getElem_modify,
      getElem!_pos t x hx]
    by_cases hix : i = x <;> simp [hix, hx]
  · rw [getElem!_neg _ _ (by simpa [Array.size_modify] using hx), getElem!_neg t x hx]
    simp [hx]

private theorem size_foldl_modify (es : List (Nat × Nat)) (t : Array (List Nat)) :
    (es.foldl (fun t e => t.modify e.1 (e.2 :: ·)) t).size = t.size := by
  induction es generalizing t with
  | nil => rfl
  | cons e es ih => rw [List.foldl_cons, ih, Array.size_modify]

private theorem mem_foldl_modify (es : List (Nat × Nat)) (t : Array (List Nat)) {a : Nat}
    (ha : a < t.size) (b : Nat) :
    b ∈ (es.foldl (fun t e => t.modify e.1 (e.2 :: ·)) t)[a]! ↔ b ∈ t[a]! ∨ (a, b) ∈ es := by
  induction es generalizing t with
  | nil => simp
  | cons e es ih =>
    rw [List.foldl_cons, ih _ (by rwa [Array.size_modify]), getElem!_modify_list]
    by_cases he : e.1 = a
    · rw [if_pos ⟨he, ha⟩, List.mem_cons]
      obtain ⟨e1, e2⟩ := e
      simp only at he
      subst he
      constructor
      · rintro ((rfl | h) | h)
        · exact Or.inr List.mem_cons_self
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact Or.inl (Or.inr h)
        · rcases List.mem_cons.1 h with h | h
          · cases h; exact Or.inl (Or.inl rfl)
          · exact Or.inr h
    · rw [if_neg (fun h => he h.1)]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact Or.inl h
        · rcases List.mem_cons.1 h with h | h
          · exact absurd (by rw [← h]) he
          · exact Or.inr h

theorem mem_upperAdj {k : Nat} (es : List (Nat × Nat)) {a : Nat} (ha : a < k) (b : Nat) :
    b ∈ (upperAdj k es)[a]! ↔ (a, b) ∈ es := by
  unfold upperAdj
  rw [mem_foldl_modify _ _ (by simpa using ha)]
  simp [getElem!_pos (Array.replicate k ([] : List Nat)) a (by simpa using ha)]

/-- An edge as the pair (smaller endpoint, larger endpoint) of naturals. -/
def sym2Pair {k : ℕ} : Sym2 (Fin k) → ℕ × ℕ :=
  Sym2.lift ⟨fun a b => ((min a b : Fin k).val, (max a b : Fin k).val), fun a b => by
    simp [min_comm, max_comm]⟩

/-- The encoder of `IndepSet.cnf (edgeGraph l)`, computed by the compiled `edgeListCnf`. -/
def edgeCnf {k : ℕ} (l : List (Sym2 (Fin k))) : CNF ℕ := edgeListCnf k (l.map sym2Pair)

theorem mem_map_sym2Pair {k : ℕ} (l : List (Sym2 (Fin k))) {u v : Fin k} (huv : u < v) :
    (u.val, v.val) ∈ l.map sym2Pair ↔ s(u, v) ∈ l := by
  rw [List.mem_map]
  constructor
  · rintro ⟨e, he, hp⟩
    induction e using Sym2.ind with
    | h a b =>
      simp only [sym2Pair, Sym2.lift_mk, Prod.mk.injEq] at hp
      obtain ⟨h1, h2⟩ := hp
      have h1 : min a b = u := Fin.ext h1
      have h2 : max a b = v := Fin.ext h2
      rcases le_total a b with hab | hab
      · rw [min_eq_left hab] at h1; rw [max_eq_right hab] at h2
        subst h1; subst h2; exact he
      · rw [min_eq_right hab] at h1; rw [max_eq_left hab] at h2
        subst h1; subst h2; rw [Sym2.eq_swap]; exact he
  · intro h
    exact ⟨_, h, by simp [sym2Pair, huv.le]⟩

theorem edgeListClauses_eq {k : ℕ} (l : List (Sym2 (Fin k))) :
    edgeListClauses k (l.map sym2Pair) = IndepSet.edgeClauses (edgeGraph l) := by
  unfold edgeListClauses IndepSet.edgeClauses
  simp only
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  apply List.flatMap_congr
  intro u _
  rw [List.filterMap_map]
  apply List.filterMap_congr
  intro v _
  simp only [Function.comp_apply]
  have hadj : (u.val < v.val ∧ ((upperAdj k (l.map sym2Pair))[u.val]!).contains v.val = true) ↔
      (u < v ∧ (edgeGraph l).Adj u v) := by
    rw [List.contains_iff_mem, mem_upperAdj _ u.isLt]
    simp only [edgeGraph, fromEdgeSet_adj, Set.mem_setOf_eq, Fin.lt_def]
    constructor
    · rintro ⟨huv, h⟩
      exact ⟨huv, (mem_map_sym2Pair l huv).1 h, Fin.ne_of_lt huv⟩
    · rintro ⟨huv, h, -⟩
      exact ⟨huv, (mem_map_sym2Pair l huv).2 h⟩
  by_cases h : u < v ∧ (edgeGraph l).Adj u v
  · rw [if_pos (hadj.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hadj.1 h')), if_neg h]

/-- The compiled encoder computes the same CNF as `IndepSet.cnf (edgeGraph l)`. -/
theorem edgeCnf_eq {k : ℕ} (l : List (Sym2 (Fin k))) : edgeCnf l = IndepSet.cnf (edgeGraph l) := by
  unfold edgeCnf edgeListCnf IndepSet.cnf
  rw [edgeListClauses_eq]

/-- A certificate for an edge-list graph counts its independent sets. -/
theorem edgeGraph_card_of_check {k : ℕ} {l : List (Sym2 (Fin k))} {pogStr lratStr : String}
    {N : ℕ} (h : checkAll k (edgeCnf l) pogStr lratStr N = true) :
    Nat.card {s : Finset (Fin k) // (edgeGraph l).IsIndepSet (s : Set (Fin k))} = N :=
  IndepSet.card_of_check _ (by rwa [edgeCnf_eq] at h)

/-- The same with part B as a separate (streamed) refutation, for large certificates. -/
theorem edgeGraph_card_of_checkAC {k : ℕ} {l : List (Sym2 (Fin k))} {pogStr : String} {N : ℕ}
    (h : checkAllAC k (edgeCnf l) pogStr N = true) (hB : (fwdCnfOf (edgeCnf l) pogStr).Unsat) :
    Nat.card {s : Finset (Fin k) // (edgeGraph l).IsIndepSet (s : Set (Fin k))} = N :=
  IndepSet.card_of_checkAC _ (by rwa [edgeCnf_eq] at h) (by rwa [edgeCnf_eq] at hB)

/-- The hypercube `Q_n`: bit vectors of length `n`, adjacent iff they differ in one bit. -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj x y := hammingDist x y = 1
  symm x y h := (hammingDist_comm y x).trans h
  loopless := ⟨fun x (h : hammingDist x x = 1) => by simp at h⟩

instance (n : ℕ) : DecidableRel (hypercube n).Adj := fun x y =>
  inferInstanceAs (Decidable (hammingDist x y = 1))

/-- Binary numbering of bit vectors: coordinate `i` has weight `2 ^ i`. -/
def binEquiv (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- The hypercube on `Fin (2 ^ n)`, the vertex set of the encoder. -/
def hypercubeFin (n : ℕ) : SimpleGraph (Fin (2 ^ n)) :=
  (hypercube n).comap (binEquiv n).symm

instance (n : ℕ) : DecidableRel (hypercubeFin n).Adj := fun u v =>
  inferInstanceAs (Decidable ((hypercube n).Adj ((binEquiv n).symm u) ((binEquiv n).symm v)))

/-- A certificate for the hypercube encoder counts the independent sets of `Q_n`. -/
theorem hypercube_card_of_check {n : ℕ} {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (2 ^ n) (IndepSet.cnf (hypercubeFin n)) pogStr lratStr N = true) :
    Nat.card {s : Finset (Fin n → Bool) // (hypercube n).IsIndepSet (s : Set _)} = N := by
  rw [← Nat.card_congr (indepSetsComapEquiv (binEquiv n) _)]
  exact IndepSet.card_of_check (hypercubeFin n) h

/-- The same with part B as a separate (streamed) refutation, for large certificates. -/
theorem hypercube_card_of_checkAC {n : ℕ} {pogStr : String} {N : ℕ}
    (h : checkAllAC (2 ^ n) (IndepSet.cnf (hypercubeFin n)) pogStr N = true)
    (hB : (fwdCnfOf (IndepSet.cnf (hypercubeFin n)) pogStr).Unsat) :
    Nat.card {s : Finset (Fin n → Bool) // (hypercube n).IsIndepSet (s : Set _)} = N := by
  rw [← Nat.card_congr (indepSetsComapEquiv (binEquiv n) _)]
  exact IndepSet.card_of_checkAC (hypercubeFin n) h hB

end CountCatcher
