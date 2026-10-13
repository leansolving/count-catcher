import CountCatcherMath.Check
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Perfect matchings of a finite graph

Encoder: one variable per edge of an edge list `es`; for every vertex of a vertex list `vs`
(in order), an at-least-one clause over its incident edges and pairwise at-most-one clauses
(the order of `scripts/gen_domino.py`). Family lemma: the models correspond to Mathlib's
perfect matchings `{M : G.Subgraph // M.IsPerfectMatching}`, given that `es` lists every edge
of `G` exactly once and `vs` lists every vertex.
-/

open Std.Sat

namespace CountCatcher.Matching

variable {V : Type*} [DecidableEq V] (es : List (V × V))

/-- Indices of the edges incident to `v`, ascending. -/
def incident (v : V) : List ℕ :=
  (List.range es.length).filter fun i =>
    match es[i]? with
    | some e => e.1 == v || e.2 == v
    | none => false

/-- All pairs `(i, j)` with `i` before `j` (as Python's `combinations(l, 2)`). -/
def pairs : List ℕ → List (ℕ × ℕ)
  | [] => []
  | i :: is => is.map (fun j => (i, j)) ++ pairs is

def vertexClauses (v : V) : List (CNF.Clause ℕ) :=
  ((incident es v).map fun i => (i, true)) ::
    (pairs (incident es v)).map fun p => [(p.1, false), (p.2, false)]

/-- The encoder: exactly one selected edge at every vertex of `vs`. -/
def cnf (vs : List V) : CNF ℕ := ⟨(vs.flatMap (vertexClauses es)).toArray⟩

theorem mem_incident {v : V} {i : ℕ} :
    i ∈ incident es v ↔ ∃ h : i < es.length, es[i].1 = v ∨ es[i].2 = v := by
  simp only [incident, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hi, h⟩
    rw [List.getElem?_eq_getElem hi] at h
    exact ⟨hi, by simpa using h⟩
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    rw [List.getElem?_eq_getElem hi]
    simpa using h

theorem incident_nodup (v : V) : (incident es v).Nodup :=
  (List.nodup_range).filter _

theorem mem_pairs : ∀ {l : List ℕ} {p : ℕ × ℕ}, p ∈ pairs l →
    p.1 ∈ l ∧ p.2 ∈ l ∧ p.1 ≠ p.2 ∨ ¬ l.Nodup := by
  intro l
  induction l with
  | nil => simp [pairs]
  | cons i is ih =>
    intro p hp
    simp only [pairs, List.mem_append, List.mem_map] at hp
    by_cases hnd : (i :: is).Nodup
    · left
      rcases hp with ⟨j, hj, rfl⟩ | hp
      · refine ⟨List.mem_cons_self, List.mem_cons_of_mem _ hj, fun h => ?_⟩
        simp only at h
        exact (List.nodup_cons.1 hnd).1 (h ▸ hj)
      · rcases ih hp with ⟨h1, h2, h3⟩ | h
        · exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2, h3⟩
        · exact absurd (List.nodup_cons.1 hnd).2 h
    · exact Or.inr hnd

theorem pairs_complete : ∀ {l : List ℕ} {i j : ℕ}, i ∈ l → j ∈ l → i ≠ j →
    (i, j) ∈ pairs l ∨ (j, i) ∈ pairs l := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro i j hi hj hij
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq]
    rcases List.mem_cons.1 hi with hia | hil
    · rcases List.mem_cons.1 hj with hja | hjl
      · exact absurd (hia.trans hja.symm) hij
      · exact Or.inl (Or.inl ⟨j, hjl, hia.symm, rfl⟩)
    · rcases List.mem_cons.1 hj with hja | hjl
      · exact Or.inr (Or.inl ⟨i, hil, hja.symm, rfl⟩)
      · rcases ih hil hjl hij with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

/-- Semantics of the encoder on assignments of the edge variables. -/
theorem eval_iff (vs : List V) (a : Fin es.length → Bool) :
    (cnf es vs).eval (ext a) = true ↔
      ∀ v ∈ vs, ∃ i ∈ incident es v, ext a i = true ∧
        ∀ j ∈ incident es v, ext a j = true → j = i := by
  unfold CNF.eval
  rw [Array.all_eq_true_iff_forall_mem]
  simp only [cnf, List.mem_toArray, List.mem_flatMap]
  constructor
  · intro h v hv
    have halo := h _ ⟨v, hv, List.mem_cons_self⟩
    simp only [CNF.Clause.eval, List.any_map, List.any_eq_true, Function.comp, beq_true] at halo
    obtain ⟨i, hi, hai⟩ := halo
    refine ⟨i, hi, hai, fun j hj haj => ?_⟩
    by_contra hji
    rcases pairs_complete hi hj (Ne.symm hji) with hp | hp
    · have := h [(i, false), (j, false)] ⟨v, hv, List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, hp, rfl⟩)⟩
      simp [CNF.Clause.eval, hai, haj] at this
    · have := h [(j, false), (i, false)] ⟨v, hv, List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, hp, rfl⟩)⟩
      simp [CNF.Clause.eval, hai, haj] at this
  · rintro h c ⟨v, hv, hc⟩
    obtain ⟨i, hi, hai, huniq⟩ := h v hv
    simp only [vertexClauses, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨p, hp, rfl⟩
    · simp only [CNF.Clause.eval, List.any_map, List.any_eq_true, Function.comp, beq_true]
      exact ⟨i, hi, hai⟩
    · rcases mem_pairs hp with ⟨h1, h2, h3⟩ | hnd
      · simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
          beq_iff_eq]
        by_contra hboth
        simp only [not_or] at hboth
        have e1 := huniq p.1 h1 (by simpa using hboth.1)
        have e2 := huniq p.2 h2 (by simpa using hboth.2)
        exact h3 (e1.trans e2.symm)
      · exact absurd (incident_nodup es v) hnd

/-- `es` lists every edge of `G` exactly once and `vs` lists every vertex. -/
structure Listing (G : SimpleGraph V) (es : List (V × V)) (vs : List V) : Prop where
  adj : ∀ e ∈ es, G.Adj e.1 e.2
  nodup : (es.map fun e => s(e.1, e.2)).Nodup
  complete : ∀ u v, G.Adj u v → s(u, v) ∈ es.map fun e => s(e.1, e.2)
  verts : ∀ v, v ∈ vs

variable {es} {G : SimpleGraph V} {vs : List V}

omit [DecidableEq V] in
theorem Listing.complete_idx (hL : Listing G es vs) {u v : V} (h : G.Adj u v) :
    ∃ i, ∃ hi : i < es.length, s(es[i].1, es[i].2) = s(u, v) := by
  obtain ⟨e, he, heq⟩ := List.mem_map.1 (hL.complete u v h)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  exact ⟨i, hi, heq⟩

omit [DecidableEq V] in
theorem Listing.inj (hL : Listing G es vs) {i j : ℕ} (hi : i < es.length) (hj : j < es.length)
    (h : s(es[i].1, es[i].2) = s(es[j].1, es[j].2)) : i = j := by
  have := (List.Nodup.getElem_inj_iff hL.nodup (i := i) (j := j) (hi := by simpa using hi)
    (hj := by simpa using hj)).1
  simp only [List.getElem_map] at this
  exact this h

omit [DecidableEq V] in
theorem ext_fin {a : Fin es.length → Bool} {i : ℕ} (hi : i < es.length) :
    ext a i = a ⟨i, hi⟩ := by simp [ext, hi]

/-- The subgraph of selected edges. -/
def selAdj (a : Fin es.length → Bool) (u v : V) : Prop :=
  ∃ i, ∃ h : i < es.length, a ⟨i, h⟩ = true ∧ s(es[i].1, es[i].2) = s(u, v)

omit [DecidableEq V] in
theorem selAdj_symm {a : Fin es.length → Bool} {u v : V} (h : selAdj a u v) : selAdj a v u := by
  obtain ⟨i, hi, ha, he⟩ := h
  exact ⟨i, hi, ha, he.trans Sym2.eq_swap⟩

def toSub (hL : Listing G es vs) (a : Fin es.length → Bool) : G.Subgraph where
  verts := Set.univ
  Adj := selAdj a
  adj_sub := by
    rintro u v ⟨i, hi, -, he⟩
    have hadj := hL.adj _ (List.getElem_mem hi)
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hadj
    · rw [← h1, ← h2]; exact hadj.symm
  edge_vert := fun _ => Set.mem_univ _
  symm := fun _ _ h => selAdj_symm h

/-- Selected edges at `v` and neighbours in the selected subgraph correspond. -/
theorem selAdj_iff_incident {a : Fin es.length → Bool} {v w : V} :
    selAdj a v w ↔ ∃ i ∈ incident es v, ∃ h : i < es.length, a ⟨i, h⟩ = true ∧
      s(es[i].1, es[i].2) = s(v, w) := by
  constructor
  · rintro ⟨i, hi, ha, he⟩
    refine ⟨i, (mem_incident es).2 ⟨hi, ?_⟩, hi, ha, he⟩
    have : v ∈ s(es[i].1, es[i].2) := by rw [he]; exact Sym2.mem_mk_left v w
    simpa [Sym2.mem_iff, eq_comm] using this
  · rintro ⟨i, -, hi, ha, he⟩; exact ⟨i, hi, ha, he⟩

theorem toSub_perfect (hL : Listing G es vs) {a : Fin es.length → Bool}
    (ha : (cnf es vs).eval (ext a) = true) : (toSub hL a).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  obtain ⟨i, hi, hai, huniq⟩ := (eval_iff es vs a).1 ha v (hL.verts v)
  obtain ⟨hlt, hv⟩ := (mem_incident es).1 hi
  rw [ext_fin hlt] at hai
  -- the other endpoint of the selected edge at v
  have hw : ∃ w, s(es[i].1, es[i].2) = s(v, w) := by
    rcases hv with h | h
    · exact ⟨es[i].2, by rw [h]⟩
    · exact ⟨es[i].1, by rw [h, Sym2.eq_swap]⟩
  obtain ⟨w, hw⟩ := hw
  refine ⟨w, ⟨i, hlt, hai, hw⟩, fun w' hw' => ?_⟩
  obtain ⟨j, hj, hjlt, haj, hwj⟩ := selAdj_iff_incident.1 hw'
  have := huniq j hj (by rw [ext_fin hjlt]; exact haj)
  subst this
  rw [hw] at hwj
  exact (Sym2.congr_right.1 hwj).symm

open Classical in
/-- Edge variables of a subgraph. -/
noncomputable def fromSub (M : G.Subgraph) : Fin es.length → Bool :=
  fun i => decide (M.Adj es[i.1].1 es[i.1].2)

omit [DecidableEq V] in
theorem adj_of_sym2 {M : G.Subgraph} {a b u v : V} (h : s(a, b) = s(u, v)) :
    M.Adj a b ↔ M.Adj u v := by
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem fromSub_model (hL : Listing G es vs) {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    (cnf es vs).eval (ext (fromSub (es := es) M)) = true := by
  rw [eval_iff]
  intro v _
  obtain ⟨w, hvw, hw⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.1 hM v
  obtain ⟨i, hi, he⟩ := hL.complete_idx (M.adj_sub hvw)
  refine ⟨i, (mem_incident es).2 ⟨hi, ?_⟩, ?_, fun j hj haj => ?_⟩
  · have : v ∈ s(es[i].1, es[i].2) := by rw [he]; exact Sym2.mem_mk_left v w
    simpa [Sym2.mem_iff, eq_comm] using this
  · rw [ext_fin hi]; simp only [fromSub, decide_eq_true_eq]; exact (adj_of_sym2 he).2 hvw
  · obtain ⟨hjlt, hvj⟩ := (mem_incident es).1 hj
    rw [ext_fin hjlt] at haj
    simp only [fromSub, decide_eq_true_eq] at haj
    -- the other endpoint of edge j is also a neighbour of v, hence w
    have hj' : ∃ w', s(es[j].1, es[j].2) = s(v, w') := by
      rcases hvj with h | h
      · exact ⟨es[j].2, by rw [h]⟩
      · exact ⟨es[j].1, by rw [h, Sym2.eq_swap]⟩
    obtain ⟨w', hw'⟩ := hj'
    have := hw w' ((adj_of_sym2 hw').1 haj)
    subst this
    exact hL.inj hjlt hi (hw'.trans he.symm)

open Classical in
/-- Family lemma: models of the encoder are the perfect matchings of `G`. -/
noncomputable def equiv (hL : Listing G es vs) :
    {a : Fin es.length → Bool // (cnf es vs).eval (ext a) = true} ≃
      {M : G.Subgraph // M.IsPerfectMatching} where
  toFun a := ⟨toSub hL a.1, toSub_perfect hL a.2⟩
  invFun M := ⟨fromSub M.1, fromSub_model hL M.2⟩
  left_inv a := by
    ext ⟨i, hi⟩
    simp only [fromSub, toSub]
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    constructor
    · rintro ⟨j, hj, haj, he⟩
      have := hL.inj hj hi he
      subst this; exact haj
    · intro ha; exact ⟨i, hi, ha, rfl⟩
  right_inv M := by
    apply Subtype.ext
    apply SimpleGraph.Subgraph.ext
    · simp only [toSub]
      exact (M.2.2.verts_eq_univ).symm
    · funext u v
      apply propext
      simp only [toSub]
      constructor
      · rintro ⟨i, hi, ha, he⟩
        simp only [fromSub, decide_eq_true_eq] at ha
        exact (adj_of_sym2 he).1 ha
      · intro huv
        obtain ⟨i, hi, he⟩ := hL.complete_idx (M.1.adj_sub huv)
        exact ⟨i, hi, by simp only [fromSub, decide_eq_true_eq]; exact (adj_of_sym2 he).2 huv, he⟩

/-- A certificate for the encoder counts the perfect matchings of `G`. -/
theorem card_of_check (hL : Listing G es vs) {pogStr lratStr : String} {N : ℕ}
    (h : checkAll es.length (cnf es vs) pogStr lratStr N = true) :
    Nat.card {M : G.Subgraph // M.IsPerfectMatching} = N := by
  rw [← Nat.card_congr (equiv hL), Nat.card_eq_fintype_card, checkAll_sound h]

/-- The same with part B as a separate (streamed) refutation, for large certificates. -/
theorem card_of_checkAC (hL : Listing G es vs) {pogStr : String} {N : ℕ}
    (h : checkAllAC es.length (cnf es vs) pogStr N = true)
    (hB : (fwdCnfOf (cnf es vs) pogStr).Unsat) :
    Nat.card {M : G.Subgraph // M.IsPerfectMatching} = N := by
  rw [← Nat.card_congr (equiv hL), Nat.card_eq_fintype_card, checkAllAC_sound h hB]

end CountCatcher.Matching
