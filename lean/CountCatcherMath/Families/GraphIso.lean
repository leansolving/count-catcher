import CountCatcherMath.Symmetry
import CountCatcherMath.CycleType
import CountCatcherMath.Family
import CountCatcherMath.Families.Complete
import CountCatcherChecker.CliqueCnf
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Graphs up to isomorphism: Burnside over `Perm (Fin n)` on certified counts

Generic layer for counting graphs on `Fin n` with an isomorphism-invariant property `P`, up to
isomorphism.

* Action: `Perm V` acts on `SimpleGraph V` by relabelling, `(σ • G).Adj u v ↔ G.Adj (σ⁻¹ u)
  (σ⁻¹ v)`; `subAction` restricts it to `{G // P G}` for an invariant `P`. The orbits are the
  isomorphism classes (`orbitRel_iff_iso`, `card_isoClasses`).
* Encoding: one variable per edge of `K_n`, in the order of `Complete.edges n` (`edgeVar`), no
  auxiliary variables. `graphOf a` is the graph of an assignment; a CNF `F` encodes `P` when
  `F.eval (ext a) = true ↔ P (graphOf a)` for every `a`, and then `equiv` maps `{G // P G}` onto
  the models of `F`.
* Symmetry: `σ` acts on the edge variables as `edgePerm n σ`; the graphs fixed by `σ` are the
  models of `symCnf F (numEdges n) (edgePerm n σ)` (`fix_card_of_check` and variants).
* Families: `cliqueCnfN n s` (no `s`-clique, one clause per `s`-set) and `ramseyCnfN n s t` (no
  `s`-clique and no independent `t`-set), the compiled forms of `cliqueCnf n s` and
  `ramseyCnf n s t` (`cliqueCnfN_eq`, `ramseyCnfN_eq`), with the statements
  `{G // G.CliqueFree s}` and `{G // G.CliqueFree s ∧ Gᶜ.CliqueFree t}` (`CliqueFreeFam`,
  `RamseyFam`).

* Cubes (section `Cube`): counts of the graphs that satisfy a pattern of fixed edges (`Sat`,
  `cubeCnf`), relabelling (`card_sat_iso`, `card_nbrs_induce_eq`) and cell splits
  (`card_eq_of_cell`): a tree of cubes that refines the neighbourhood split of vertex `0`.

With `CountCatcherMath.CycleType.card_orbits_eq`, one certified count per cycle type (the identity
term is the labelled count) gives the number of isomorphism classes.
-/

open Std.Sat Equiv MulAction SimpleGraph

namespace CountCatcher.GraphIso

/-! ## The symmetric group acts on graphs -/

section Action

variable {V : Type*}

/-- Relabelling: `σ` moves the edge `uv` to `σ u σ v`. -/
instance instMulActionPerm : MulAction (Perm V) (SimpleGraph V) where
  smul σ G := G.comap ⇑σ⁻¹
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem smul_adj (σ : Perm V) (G : SimpleGraph V) (u v : V) :
    (σ • G).Adj u v ↔ G.Adj (σ⁻¹ u) (σ⁻¹ v) := Iff.rfl

theorem smul_adj_apply (σ : Perm V) (G : SimpleGraph V) (u v : V) :
    (σ • G).Adj (σ u) (σ v) ↔ G.Adj u v := by
  simp [smul_adj]

/-- `G` and its relabelling are isomorphic. -/
def smulIso (σ : Perm V) (G : SimpleGraph V) : σ • G ≃g G :=
  SimpleGraph.Iso.comap σ⁻¹ G

theorem cliqueFree_smul {s : ℕ} (σ : Perm V) {G : SimpleGraph V} (h : G.CliqueFree s) :
    (σ • G).CliqueFree s :=
  h.comap (smulIso σ G).isContained

theorem compl_smul (σ : Perm V) (G : SimpleGraph V) : (σ • G)ᶜ = σ • Gᶜ := by
  ext u v
  simp only [compl_adj, smul_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq]

/-- The action on the graphs with an isomorphism-invariant property `P`. -/
abbrev subAction (P : SimpleGraph V → Prop) (hP : ∀ (σ : Perm V) G, P G → P (σ • G)) :
    MulAction (Perm V) {G // P G} where
  smul σ G := ⟨σ • G.1, hP σ G.1 G.2⟩
  one_smul G := Subtype.ext (one_smul _ G.1)
  mul_smul σ τ G := Subtype.ext (mul_smul σ τ G.1)

instance instCliqueFree (s : ℕ) : MulAction (Perm V) {G : SimpleGraph V // G.CliqueFree s} :=
  subAction _ fun σ _ h => cliqueFree_smul σ h

instance instRamsey (s t : ℕ) :
    MulAction (Perm V) {G : SimpleGraph V // G.CliqueFree s ∧ Gᶜ.CliqueFree t} :=
  subAction _ fun σ G h => ⟨cliqueFree_smul σ h.1, by rw [compl_smul]; exact cliqueFree_smul σ h.2⟩

variable {P : SimpleGraph V → Prop} [MulAction (Perm V) {G // P G}]

/-- Two graphs lie in the same orbit iff they are isomorphic. -/
theorem orbitRel_iff_iso (hact : ∀ (σ : Perm V) (x : {G // P G}), (σ • x).1 = σ • x.1)
    (x y : {G // P G}) : orbitRel (Perm V) {G // P G} x y ↔ Nonempty (x.1 ≃g y.1) := by
  rw [orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨σ, rfl⟩
    rw [hact]
    exact ⟨smulIso σ y.1⟩
  · rintro ⟨φ⟩
    refine ⟨φ.toEquiv⁻¹, Subtype.ext ?_⟩
    rw [hact]
    ext u v
    rw [smul_adj, inv_inv]
    exact φ.map_rel_iff'

/-- The number of orbits is the number of isomorphism classes. -/
theorem card_isoClasses (hact : ∀ (σ : Perm V) (x : {G // P G}), (σ • x).1 = σ • x.1) :
    Nat.card (Quot fun x y : {G // P G} => Nonempty (x.1 ≃g y.1)) =
      Nat.card (orbitRel.Quotient (Perm V) {G // P G}) :=
  Nat.card_congr (Quot.congr (Equiv.refl _) fun a b => (orbitRel_iff_iso hact a b).symm)

/-- If the graphs with property `P` form a single isomorphism class, each of them is isomorphic
    to any given one (for example an explicit graph that has `P`). -/
theorem iso_of_card_isoClasses_eq_one {P : SimpleGraph V → Prop}
    (h : Nat.card (Quot fun x y : {G // P G} => Nonempty (x.1 ≃g y.1)) = 1)
    (x y : {G // P G}) : Nonempty (x.1 ≃g y.1) := by
  have hs := (Nat.card_eq_one_iff_unique.1 h).1
  have hxy : Quot.mk (fun x y : {G // P G} => Nonempty (x.1 ≃g y.1)) x = Quot.mk _ y :=
    Subsingleton.elim _ _
  refine (Equivalence.eqvGen_iff ?_).1 (Quot.eqvGen_exact hxy)
  exact ⟨fun _ => ⟨SimpleGraph.Iso.refl⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

end Action

/-! ## Edge variables -/

variable {n : ℕ}

/-- The number of variables: the edges of `K_n`. -/
abbrev numEdges (n : ℕ) : ℕ := (Complete.edges n).length

/-- The variable of the edge `uv`: the position of `(min u v, max u v)` in `Complete.edges n`. -/
def edgeVar (u v : Fin n) : ℕ := (Complete.edges n).idxOf (min u v, max u v)

theorem edgeVar_comm (u v : Fin n) : edgeVar u v = edgeVar v u := by
  simp only [edgeVar, min_comm, max_comm]

theorem edges_nodup (n : ℕ) : (Complete.edges n).Nodup :=
  List.Nodup.of_map _ (Complete.listing n).nodup

theorem edgeVar_lt {u v : Fin n} (h : u ≠ v) : edgeVar u v < numEdges n :=
  List.idxOf_lt_length_iff.2 (Complete.mem_edges.2 (min_lt_max.2 h))

theorem getElem_edgeVar {u v : Fin n} (h : u ≠ v) :
    (Complete.edges n)[edgeVar u v]'(edgeVar_lt h) = (min u v, max u v) :=
  List.getElem_idxOf _

theorem lt_of_getElem (x : ℕ) (hx : x < numEdges n) :
    (Complete.edges n)[x].1 < (Complete.edges n)[x].2 :=
  Complete.mem_edges.1 (List.getElem_mem hx)

theorem edgeVar_getElem (x : ℕ) (hx : x < numEdges n) :
    edgeVar (Complete.edges n)[x].1 (Complete.edges n)[x].2 = x := by
  have h := lt_of_getElem x hx
  rw [edgeVar, min_eq_left h.le, max_eq_right h.le]
  exact (edges_nodup n).idxOf_getElem x hx

/-- The graph of an assignment of the edge variables. -/
def graphOf (a : Fin (numEdges n) → Bool) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ext a (edgeVar u v) = true
  symm u v h := ⟨h.1.symm, by rw [edgeVar_comm]; exact h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem graphOf_adj (a : Fin (numEdges n) → Bool) (u v : Fin n) :
    (graphOf a).Adj u v ↔ u ≠ v ∧ ext a (edgeVar u v) = true := Iff.rfl

open Classical in
/-- The assignment of a graph: variable `x` is the edge `(Complete.edges n)[x]`. -/
noncomputable def modelOf (G : SimpleGraph (Fin n)) (x : Fin (numEdges n)) : Bool :=
  decide (G.Adj (Complete.edges n)[x.1].1 (Complete.edges n)[x.1].2)

theorem ext_modelOf (G : SimpleGraph (Fin n)) {u v : Fin n} (h : u ≠ v) :
    ext (modelOf G) (edgeVar u v) = true ↔ G.Adj u v := by
  classical
  simp only [ext, edgeVar_lt h, dite_true, modelOf, getElem_edgeVar h, decide_eq_true_eq]
  rcases lt_or_gt_of_ne h with h' | h'
  · simp [min_eq_left h'.le, max_eq_right h'.le]
  · simp [min_eq_right h'.le, max_eq_left h'.le, G.adj_comm]

theorem graphOf_modelOf (G : SimpleGraph (Fin n)) : graphOf (modelOf G) = G := by
  ext u v
  rw [graphOf_adj]
  by_cases h : u = v
  · simp [h]
  · rw [ext_modelOf G h]
    simp [h]

theorem modelOf_graphOf (a : Fin (numEdges n) → Bool) : modelOf (graphOf a) = a := by
  funext ⟨x, hx⟩
  have h := lt_of_getElem x hx
  simp only [modelOf, graphOf_adj, h.ne, ne_eq, not_false_eq_true, true_and, edgeVar_getElem x hx,
    ext, hx, dite_true, Bool.decide_eq_true]

/-! ## Encoders and the action on the variables -/

section Encoding

variable {P : SimpleGraph (Fin n) → Prop} {F : CNF ℕ}

/-- Family lemma for a CNF that encodes `P` over the edge variables. -/
noncomputable def equiv (hF : ∀ a : Fin (numEdges n) → Bool, F.eval (ext a) = true ↔ P (graphOf a)) :
    {G // P G} ≃ {a : Fin (numEdges n) → Bool // F.eval (ext a) = true} where
  toFun G := ⟨modelOf G.1, (hF _).2 (by rw [graphOf_modelOf]; exact G.2)⟩
  invFun a := ⟨graphOf a.1, (hF a.1).1 a.2⟩
  left_inv G := Subtype.ext (graphOf_modelOf G.1)
  right_inv a := Subtype.ext (modelOf_graphOf a.1)

/-- The permutation of the edge variables induced by `σ`. -/
def edgePerm (n : ℕ) (σ : Perm (Fin n)) (x : ℕ) : ℕ :=
  if h : x < numEdges n then edgeVar (σ (Complete.edges n)[x].1) (σ (Complete.edges n)[x].2)
  else x

theorem edgePerm_edgeVar (σ : Perm (Fin n)) {u v : Fin n} (h : u ≠ v) :
    edgePerm n σ (edgeVar u v) = edgeVar (σ u) (σ v) := by
  rw [edgePerm, dif_pos (edgeVar_lt h)]
  simp only [getElem_edgeVar h]
  rcases lt_or_gt_of_ne h with h' | h'
  · simp [min_eq_left h'.le, max_eq_right h'.le]
  · simp [min_eq_right h'.le, max_eq_left h'.le, edgeVar_comm]

theorem edgePerm_onto (σ : Perm (Fin n)) : ∀ j < numEdges n, ∃ i < numEdges n, edgePerm n σ i = j := by
  intro j hj
  have h := (lt_of_getElem j hj).ne
  have h' : σ⁻¹ (Complete.edges n)[j].1 ≠ σ⁻¹ (Complete.edges n)[j].2 := by simpa using h
  refine ⟨edgeVar (σ⁻¹ (Complete.edges n)[j].1) (σ⁻¹ (Complete.edges n)[j].2), edgeVar_lt h', ?_⟩
  have hs : ∀ x, σ (σ⁻¹ x) = x := fun x => σ.apply_symm_apply x
  rw [edgePerm_edgeVar σ h', hs, hs]
  exact edgeVar_getElem j hj

variable [MulAction (Perm (Fin n)) {G // P G}]

theorem equiv_smul (hact : ∀ (σ : Perm (Fin n)) (x : {G // P G}), (σ • x).1 = σ • x.1)
    (hF : ∀ a : Fin (numEdges n) → Bool, F.eval (ext a) = true ↔ P (graphOf a))
    (σ : Perm (Fin n)) (x : {G // P G}) :
    ∀ i < numEdges n, ext (equiv hF (σ • x)).1 (edgePerm n σ i) = ext (equiv hF x).1 i := by
  intro i hi
  have h := (lt_of_getElem i hi).ne
  have hσ : σ (Complete.edges n)[i].1 ≠ σ (Complete.edges n)[i].2 := by simpa using h
  have e := edgeVar_getElem i hi
  show ext (modelOf (σ • x).1) _ = ext (modelOf x.1) i
  conv_rhs => rw [← e]
  conv_lhs => rw [← e]
  rw [edgePerm_edgeVar σ h, Bool.eq_iff_iff, ext_modelOf _ hσ, ext_modelOf _ h, hact,
    smul_adj_apply]

/-- The graphs fixed by `σ`, counted by an embedded certificate for the fixed-point formula. -/
theorem fix_card_of_check (hact : ∀ (σ : Perm (Fin n)) (x : {G // P G}), (σ • x).1 = σ • x.1)
    (hF : ∀ a : Fin (numEdges n) → Bool, F.eval (ext a) = true ↔ P (graphOf a))
    (σ : Perm (Fin n)) {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (numEdges n) (symCnf F (numEdges n) (edgePerm n σ)) pogStr lratStr N = true) :
    Nat.card (fixedBy {G // P G} σ) = N := by
  rw [card_fixedBy_eq (equiv hF) σ (edgePerm n σ) (edgePerm_onto σ) (equiv_smul hact hF σ)]
  exact checkAll_sound h

/-- The same with part B as a separate (streamed) refutation. -/
theorem fix_card_of_checkAC (hact : ∀ (σ : Perm (Fin n)) (x : {G // P G}), (σ • x).1 = σ • x.1)
    (hF : ∀ a : Fin (numEdges n) → Bool, F.eval (ext a) = true ↔ P (graphOf a))
    (σ : Perm (Fin n)) {pogStr : String} {N : ℕ}
    (h : checkAllAC (numEdges n) (symCnf F (numEdges n) (edgePerm n σ)) pogStr N = true)
    (hB : (fwdCnfOf (symCnf F (numEdges n) (edgePerm n σ)) pogStr).Unsat) :
    Nat.card (fixedBy {G // P G} σ) = N := by
  rw [card_fixedBy_eq (equiv hF) σ (edgePerm n σ) (edgePerm_onto σ) (equiv_smul hact hF σ)]
  exact checkAllAC_sound h hB

/-- No graph is fixed by `σ`: an LRAT refutation of the fixed-point formula. -/
theorem fix_card_of_unsat (hact : ∀ (σ : Perm (Fin n)) (x : {G // P G}), (σ • x).1 = σ • x.1)
    (hF : ∀ a : Fin (numEdges n) → Bool, F.eval (ext a) = true ↔ P (graphOf a))
    (σ : Perm (Fin n)) (h : (symCnf F (numEdges n) (edgePerm n σ)).Unsat) :
    Nat.card (fixedBy {G // P G} σ) = 0 := by
  rw [card_fixedBy_eq (equiv hF) σ (edgePerm n σ) (edgePerm_onto σ) (equiv_smul hact hF σ)]
  exact card_eq_zero_of_unsat h

end Encoding

/-! ## Clique encoders -/

/-- The clause of the vertex list `S`: the literals `(x_uv, pos)` for `u < v` in `S`. With
    `pos = false` it forbids that `S` is a clique, with `pos = true` that `S` is independent. -/
def cliqueClause (pos : Bool) (S : List (Fin n)) : CNF.Clause ℕ :=
  S.flatMap fun u => (S.filter (u < ·)).map fun v => (edgeVar u v, pos)

/-- One clause per `s`-subset of the vertices (as increasing lists). -/
def cliqueClauses (n s : ℕ) (pos : Bool) : List (CNF.Clause ℕ) :=
  (List.sublistsLen s (List.finRange n)).map (cliqueClause pos)

/-- No `s`-clique. -/
def cliqueCnf (n s : ℕ) : CNF ℕ := ⟨(cliqueClauses n s false).toArray⟩

/-- No `s`-clique and no independent set of size `t`. -/
def ramseyCnf (n s t : ℕ) : CNF ℕ := ⟨(cliqueClauses n s false ++ cliqueClauses n t true).toArray⟩

theorem eval_cliqueClause (w : ℕ → Bool) (pos : Bool) (S : List (Fin n)) :
    (cliqueClause pos S).eval w = true ↔ ∃ u ∈ S, ∃ v ∈ S, u < v ∧ w (edgeVar u v) = pos := by
  simp only [CNF.Clause.eval, cliqueClause, List.any_flatMap, List.any_map, List.any_eq_true,
    List.mem_filter, Function.comp_apply, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨u, hu, v, ⟨hv, huv⟩, h⟩
    exact ⟨u, hu, v, hv, huv, h⟩
  · rintro ⟨u, hu, v, hv, huv, h⟩
    exact ⟨u, hu, v, ⟨hv, huv⟩, h⟩

/-- The clauses of `cliqueClauses n s pos` hold iff `H` has no `s`-clique, where `H` is the
    graph of the edges whose variable is `!pos`. -/
theorem forall_cliqueClauses_iff (w : ℕ → Bool) (pos : Bool) (s : ℕ) (H : SimpleGraph (Fin n))
    (hH : ∀ u v, H.Adj u v ↔ u ≠ v ∧ w (edgeVar u v) = !pos) :
    (∀ c ∈ cliqueClauses n s pos, c.eval w = true) ↔ H.CliqueFree s := by
  classical
  have key : (∀ c ∈ cliqueClauses n s pos, c.eval w = true) ↔
      ∀ S : List (Fin n), S.Sublist (List.finRange n) → S.length = s →
        ∃ u ∈ S, ∃ v ∈ S, u < v ∧ w (edgeVar u v) = pos := by
    simp only [cliqueClauses, List.forall_mem_map, List.mem_sublistsLen, and_imp,
      eval_cliqueClause]
  rw [key]
  constructor
  · intro h t ht
    -- the vertices of the clique, in increasing order
    let S := (List.finRange n).filter (· ∈ t)
    have hS : S.Nodup := (List.nodup_finRange n).filter _
    have hmem : ∀ x, x ∈ S ↔ x ∈ t := by simp [S]
    have hSt : S.toFinset = t := by ext x; simp [hmem]
    obtain ⟨u, hu, v, hv, huv, hw⟩ := h S (List.filter_sublist)
      (by rw [← List.toFinset_card_of_nodup hS, hSt, ht.2])
    have hadj := ht.1 ((hmem u).1 hu) ((hmem v).1 hv) huv.ne
    rw [hH] at hadj
    rw [hadj.2] at hw
    cases pos <;> simp at hw
  · intro hfree S hsub hlen
    have hS : S.Nodup := (List.nodup_finRange n).sublist hsub
    have hnc : ¬ H.IsNClique s S.toFinset := hfree _
    rw [isNClique_iff, List.toFinset_card_of_nodup hS, hlen] at hnc
    simp only [and_true, IsClique, Set.Pairwise, not_forall] at hnc
    obtain ⟨u, hu, v, hv, huv, hnadj⟩ := hnc
    simp only [List.coe_toFinset, Set.mem_setOf_eq] at hu hv
    have hw : w (edgeVar u v) = pos := by
      rw [hH] at hnadj
      cases hp : pos <;> cases hwv : w (edgeVar u v) <;> simp_all
    rcases lt_or_gt_of_ne huv with h' | h'
    · exact ⟨u, hu, v, hv, h', hw⟩
    · exact ⟨v, hv, u, hu, h', by rw [edgeVar_comm]; exact hw⟩

theorem cliqueCnf_eval (s : ℕ) (a : Fin (numEdges n) → Bool) :
    (cliqueCnf n s).eval (ext a) = true ↔ (graphOf a).CliqueFree s := by
  unfold CNF.eval
  rw [Array.all_eq_true_iff_forall_mem]
  simp only [cliqueCnf, List.mem_toArray]
  exact forall_cliqueClauses_iff _ false s _ fun u v => by simp [graphOf_adj]

theorem ramseyCnf_eval (s t : ℕ) (a : Fin (numEdges n) → Bool) :
    (ramseyCnf n s t).eval (ext a) = true ↔
      (graphOf a).CliqueFree s ∧ (graphOf a)ᶜ.CliqueFree t := by
  unfold CNF.eval
  rw [Array.all_eq_true_iff_forall_mem]
  simp only [ramseyCnf, List.mem_toArray, List.mem_append, or_imp, forall_and]
  exact and_congr (forall_cliqueClauses_iff _ false s _ fun u v => by simp [graphOf_adj])
    (forall_cliqueClauses_iff _ true t _ fun u v => by
      simp only [compl_adj, graphOf_adj, ne_eq, Bool.not_true]
      cases ext a (edgeVar u v) <;> simp)

/-! ### The compiled clique encoders

`cliqueCnf` and `ramseyCnf` run in the interpreter, where every `edgeVar` rebuilds and searches
`Complete.edges n` (about 0.53 s for the (3,5)-Ramsey encoder on 13 vertices, 2026-10-02). The
family lemmas below take the compiled `CountCatcher.cliqueCnfN` and `ramseyCnfN` instead, proved
equal here. -/

theorem edgePairs_eq (n : ℕ) :
    edgePairs n = (Complete.edges n).map fun e => (e.1.val, e.2.val) := by
  unfold edgePairs Complete.edges
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro i _
  simp only [List.filter_map, List.map_map, Function.comp_def]
  congr 1

theorem idxOf_map_of_injective {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    {f : α → β} (hf : Function.Injective f) (a : α) :
    ∀ l : List α, (l.map f).idxOf (f a) = l.idxOf a := by
  intro l
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, ih]
    by_cases h : x = a
    · subst h; simp
    · have : f x ≠ f a := fun h' => h (hf h')
      rw [show (f x == f a) = false by simpa using this, show (x == a) = false by simpa using h]

theorem edgeVar_eq_idxOf {u v : Fin n} (h : u < v) :
    edgeVar u v = (edgePairs n).idxOf (u.val, v.val) := by
  rw [edgePairs_eq, edgeVar, min_eq_left h.le, max_eq_right h.le]
  exact (idxOf_map_of_injective (f := fun e : Fin n × Fin n => (e.1.val, e.2.val))
    (fun e e' he => by
      simp only [Prod.mk.injEq] at he
      exact Prod.ext (Fin.ext he.1) (Fin.ext he.2)) (u, v) _).symm

theorem sublistsLen_map {α β : Type} (f : α → β) :
    ∀ (k : ℕ) (l : List α), List.sublistsLen k (l.map f) = (List.sublistsLen k l).map (List.map f)
  | 0, l => by simp [List.sublistsLen_zero]
  | k + 1, [] => by simp
  | k + 1, a :: l => by
    rw [List.map_cons, List.sublistsLen_succ_cons, List.sublistsLen_succ_cons,
      sublistsLen_map f (k + 1) l, sublistsLen_map f k l, List.map_append, List.map_map,
      List.map_map]
    rfl

theorem sublistsLenN_eq : ∀ (k : ℕ) (l : List ℕ), sublistsLenN k l = List.sublistsLen k l
  | 0, l => by cases l <;> simp [sublistsLenN, List.sublistsLen_zero]
  | k + 1, [] => by simp [sublistsLenN]
  | k + 1, a :: l => by
    rw [sublistsLenN, List.sublistsLen_succ_cons, sublistsLenN_eq (k + 1) l, sublistsLenN_eq k l]

theorem cliqueClauseN_eq (pos : Bool) (S : List (Fin n)) :
    cliqueClauseN (edgePairs n) pos (S.map Fin.val) = cliqueClause pos S := by
  unfold cliqueClauseN cliqueClause
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro u _
  rw [List.filter_map, List.map_map]
  apply List.map_congr_left
  intro v hv
  rw [List.mem_filter] at hv
  have huv : u < v := by simpa [Function.comp] using hv.2
  simp only [Function.comp_apply, edgeVar_eq_idxOf huv]

theorem cliqueClausesN_eq (n s : ℕ) (pos : Bool) : cliqueClausesN n s pos = cliqueClauses n s pos := by
  unfold cliqueClausesN cliqueClauses
  simp only
  rw [sublistsLenN_eq, ← List.map_coe_finRange_eq_range, sublistsLen_map, List.map_map]
  apply List.map_congr_left
  intro S _
  exact cliqueClauseN_eq pos S

theorem cliqueCnfN_eq (n s : ℕ) : cliqueCnfN n s = cliqueCnf n s := by
  rw [cliqueCnfN, cliqueCnf, cliqueClausesN_eq]

theorem ramseyCnfN_eq (n s t : ℕ) : ramseyCnfN n s t = ramseyCnf n s t := by
  rw [ramseyCnfN, ramseyCnf, cliqueClausesN_eq, cliqueClausesN_eq]

theorem cliqueCnfN_eval (s : ℕ) (a : Fin (numEdges n) → Bool) :
    (cliqueCnfN n s).eval (ext a) = true ↔ (graphOf a).CliqueFree s := by
  rw [cliqueCnfN_eq]; exact cliqueCnf_eval s a

theorem ramseyCnfN_eval (s t : ℕ) (a : Fin (numEdges n) → Bool) :
    (ramseyCnfN n s t).eval (ext a) = true ↔
      (graphOf a).CliqueFree s ∧ (graphOf a)ᶜ.CliqueFree t := by
  rw [ramseyCnfN_eq]; exact ramseyCnf_eval s t a

/-! ## Concrete graphs: checking a property on the encoder by evaluation -/

/-- The assignment of a graph with decidable adjacency (computable `modelOf`). -/
def modelOfDec (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin (numEdges n)) : Bool :=
  decide (G.Adj (Complete.edges n)[x.1].1 (Complete.edges n)[x.1].2)

theorem modelOfDec_eq (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    modelOfDec G = modelOf G := by
  funext x
  simp only [modelOfDec, modelOf]
  congr 1

/-- `G` has no `s`-clique, checked by evaluating the clauses of `cliqueCnf` (structural list
    recursion, so `decide +kernel` works for concrete graphs). -/
theorem cliqueFree_of_check (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : ℕ)
    (h : (cliqueClauses n s false).all (fun c => c.eval (ext (modelOfDec G))) = true) :
    G.CliqueFree s := by
  rw [List.all_eq_true] at h
  have := (forall_cliqueClauses_iff (ext (modelOfDec G)) false s (graphOf (modelOfDec G))
    (fun u v => by simp [graphOf_adj])).1 h
  rwa [modelOfDec_eq, graphOf_modelOf] at this

/-- `G` has no independent `t`-set, checked by evaluation. -/
theorem compl_cliqueFree_of_check (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ)
    (h : (cliqueClauses n t true).all (fun c => c.eval (ext (modelOfDec G))) = true) :
    Gᶜ.CliqueFree t := by
  rw [List.all_eq_true] at h
  have := (forall_cliqueClauses_iff (ext (modelOfDec G)) true t (graphOf (modelOfDec G))ᶜ
    (fun u v => by
      simp only [compl_adj, graphOf_adj, ne_eq, Bool.not_true]
      cases ext (modelOfDec G) (edgeVar u v) <;> simp)).1 h
  rwa [modelOfDec_eq, graphOf_modelOf] at this

/-! ## Splitting the labelled count by the neighbourhood of vertex `0`

For larger `n` the identity term of Burnside's sum (the labelled count) is split. By
relabelling with permutations that fix vertex `0`, the number of graphs whose vertex `0` has the
neighbourhood `S` depends only on `|S|` (`card_nbrs_eq`), so
`Nat.card {G // P G} = Σ_k C(n-1, k) · #{G | P G ∧ N(0) = {1, …, k}}` (`card_eq_sum_choose`),
one certified count per `k`: the encoder plus unit clauses that fix the edges at `0` (`nbrCnf`,
`nbr_card_of_check`). -/

section Split

open Classical in
/-- The neighbours of `v` in `G`. -/
noncomputable def nbrs (G : SimpleGraph (Fin n)) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (G.Adj v)

theorem mem_nbrs {G : SimpleGraph (Fin n)} {v u : Fin n} : u ∈ nbrs G v ↔ G.Adj v u := by
  classical
  simp [nbrs]

theorem mem_nbrs_smul {σ : Perm (Fin n)} {v : Fin n} (hv : σ v = v) (G : SimpleGraph (Fin n))
    (w : Fin n) : σ w ∈ nbrs (σ • G) v ↔ w ∈ nbrs G v := by
  rw [mem_nbrs, mem_nbrs, ← smul_adj_apply σ G v w, hv]

/-- The canonical neighbourhood `{1, …, k}` of vertex `0`. -/
def nbrBlock (n k : ℕ) : Finset (Fin n) := Finset.univ.filter fun j => j.val ≠ 0 ∧ j.val ≤ k

theorem card_nbrBlock {k : ℕ} (h : k < n) : (nbrBlock n k).card = k := by
  have e : (nbrBlock n k).map Fin.valEmbedding = Finset.Icc 1 k := by
    ext i
    simp only [nbrBlock, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Icc]
    constructor
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      omega
    · intro hi
      exact ⟨⟨i, by omega⟩, ⟨by simp; omega, by simp; omega⟩, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e, Nat.card_Icc]
  omega

/-- Two sets of the same size that avoid `v` are mapped onto each other by a permutation that
    fixes `v`. -/
theorem exists_perm_fix_map (v : Fin n) {S T : Finset (Fin n)} (hS : v ∉ S) (hT : v ∉ T)
    (h : S.card = T.card) : ∃ σ : Perm (Fin n), σ v = v ∧ ∀ w, σ w ∈ T ↔ w ∈ S := by
  classical
  let p : Fin n → Prop := (· ≠ v)
  let S' := S.subtype p
  let T' := T.subtype p
  have hcS : S'.card = S.card := by
    rw [Finset.card_subtype]
    exact congrArg Finset.card (Finset.filter_true_of_mem fun w hw (hwv : w = v) => hS (hwv ▸ hw))
  have hcT : T'.card = T.card := by
    rw [Finset.card_subtype]
    exact congrArg Finset.card (Finset.filter_true_of_mem fun w hw (hwv : w = v) => hT (hwv ▸ hw))
  let e0 : {x : Subtype p // x ∈ S'} ≃ {x : Subtype p // x ∈ T'} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hcS, hcT, h])
  let τ : Perm (Subtype p) := e0.extendSubtype
  refine ⟨Perm.ofSubtype τ, Perm.ofSubtype_apply_of_not_mem τ (by simp [p]), fun w => ?_⟩
  by_cases hw : w = v
  · subst hw
    rw [Perm.ofSubtype_apply_of_not_mem τ (by simp [p])]
    exact iff_of_false hT hS
  · have hy : w = ((⟨w, hw⟩ : Subtype p) : Fin n) := rfl
    rw [hy, Perm.ofSubtype_apply_coe]
    have hmT : ∀ y : Subtype p, (y : Fin n) ∈ T ↔ y ∈ T' := fun y => by simp [T']
    have hmS : ∀ y : Subtype p, (y : Fin n) ∈ S ↔ y ∈ S' := fun y => by simp [S']
    rw [hmT, hmS]
    constructor
    · intro h1
      by_contra h2
      exact Equiv.extendSubtype_not_mem e0 _ h2 h1
    · exact Equiv.extendSubtype_mem e0 _

variable {P : SimpleGraph (Fin n) → Prop} [MulAction (Perm (Fin n)) {G // P G}]

/-- The number of graphs with `N(v) = S` depends only on `|S|`. -/
theorem card_nbrs_eq (hact : ∀ (σ : Perm (Fin n)) (x : {G // P G}), (σ • x).1 = σ • x.1)
    (v : Fin n) {S T : Finset (Fin n)} (hS : v ∉ S) (hT : v ∉ T) (h : S.card = T.card) :
    Nat.card {x : {G // P G} // nbrs x.1 v = S} = Nat.card {x : {G // P G} // nbrs x.1 v = T} := by
  obtain ⟨σ, hσv, hσ⟩ := exists_perm_fix_map v hS hT h
  have key : ∀ x : {G // P G}, nbrs (σ • x).1 v = T ↔ nbrs x.1 v = S := by
    intro x
    rw [hact]
    constructor
    · intro hx
      ext w
      rw [← mem_nbrs_smul hσv, hx, hσ]
    · intro hx
      ext u
      obtain ⟨w, rfl⟩ : ∃ w, σ w = u := ⟨σ⁻¹ u, σ.apply_symm_apply u⟩
      rw [mem_nbrs_smul hσv, hx, hσ]
  exact Nat.card_congr
    { toFun := fun x => ⟨σ • x.1, (key x.1).2 x.2⟩
      invFun := fun y => ⟨σ⁻¹ • y.1, (key _).1 (by rw [smul_inv_smul]; exact y.2)⟩
      left_inv := fun x => Subtype.ext (inv_smul_smul σ x.1)
      right_inv := fun y => Subtype.ext (smul_inv_smul σ y.1) }

/-- The labelled count as a sum over the neighbourhood sizes of vertex `0`. -/
theorem card_eq_sum_choose [NeZero n]
    (hact : ∀ (σ : Perm (Fin n)) (x : {G // P G}), (σ • x).1 = σ • x.1) :
    Nat.card {G // P G} = ∑ k ∈ Finset.range n,
      (n - 1).choose k * Nat.card {x : {G // P G} // nbrs x.1 0 = nbrBlock n k} := by
  classical
  have : Fintype {G // P G} := Fintype.ofFinite _
  let g : ℕ → ℕ := fun k => Nat.card {x : {G // P G} // nbrs x.1 0 = nbrBlock n k}
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hsub : ∀ x : {G // P G}, nbrs x.1 0 ∈ (Finset.univ.erase (0 : Fin n)).powerset := by
    intro x
    rw [Finset.mem_powerset]
    intro u hu
    exact Finset.mem_erase.2 ⟨fun h0 => (mem_nbrs.1 hu).ne h0.symm, Finset.mem_univ _⟩
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := fun x : {G // P G} => nbrs x.1 0)
      (t := (Finset.univ.erase (0 : Fin n)).powerset) (fun x _ => hsub x)]
  have hfib : ∀ S ∈ (Finset.univ.erase (0 : Fin n)).powerset,
      (Finset.univ.filter fun x : {G // P G} => nbrs x.1 0 = S).card = g S.card := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    have h0S : (0 : Fin n) ∉ S := fun h => by simpa using hS h
    have hcard : S.card < n := by
      have := Finset.card_le_card hS
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
      omega
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_nbrs_eq hact 0 h0S (by simp [nbrBlock]) (card_nbrBlock hcard).symm
  rw [Finset.sum_congr rfl hfib, Finset.sum_powerset_apply_card,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
    Nat.sub_add_cancel hn]
  simp only [smul_eq_mul, g]

/-- The side condition of `card_eq_of_split`: the list gives one count for each `k < n`, and
    `Σ_k C(n-1, k) · count_k = N`. -/
def checkSplit (n N : ℕ) (L : List (ℕ × ℕ)) : Bool :=
  L.map Prod.fst == List.range n && (L.map fun p => (n - 1).choose p.1 * p.2).sum == N

/-- The labelled count from one count per neighbourhood size `k` of vertex `0`. -/
theorem card_eq_of_split [NeZero n]
    (hact : ∀ (σ : Perm (Fin n)) (x : {G // P G}), (σ • x).1 = σ • x.1) (N : ℕ)
    (L : List (ℕ × ℕ))
    (hfix : ∀ p ∈ L, Nat.card {x : {G // P G} // nbrs x.1 0 = nbrBlock n p.1} = p.2)
    (hc : checkSplit n N L = true) : Nat.card {G // P G} = N := by
  simp only [checkSplit, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hL, hN⟩ := hc
  rw [card_eq_sum_choose hact, ← List.toFinset_range, List.sum_toFinset _ (List.nodup_range),
    ← hL, List.map_map, ← hN]
  congr 1
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply, hfix p hp]

/-- The encoder `F` with the edges at vertex `0` fixed: `0` is adjacent to `nbrBlock n k` only. -/
def nbrCnf (F : CNF ℕ) (n k : ℕ) [NeZero n] : CNF ℕ :=
  F ++ ⟨(((List.finRange n).filter (· ≠ 0)).map fun j =>
    [(edgeVar (0 : Fin n) j, decide (j ∈ nbrBlock n k))]).toArray⟩

theorem nbrCnf_eval [NeZero n] (F : CNF ℕ) (k : ℕ) (a : Fin (numEdges n) → Bool) :
    (nbrCnf F n k).eval (ext a) = true ↔
      F.eval (ext a) = true ∧ nbrs (graphOf a) 0 = nbrBlock n k := by
  simp only [nbrCnf, CNF.eval_append, Bool.and_eq_true]
  apply and_congr_right'
  unfold CNF.eval
  rw [Array.all_eq_true_iff_forall_mem]
  simp only [List.mem_toArray, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    forall_exists_index, and_imp]
  have hc : ∀ j : Fin n, (CNF.Clause.eval (ext a) [(edgeVar (0 : Fin n) j,
      decide (j ∈ nbrBlock n k))] = true ↔ (ext a (edgeVar 0 j) = true ↔ j ∈ nbrBlock n k)) := by
    intro j
    simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false, beq_iff_eq]
    cases h : ext a (edgeVar 0 j) <;> simp
  constructor
  · intro h
    ext u
    rw [mem_nbrs, graphOf_adj]
    by_cases hu : u = 0
    · subst hu
      simp [nbrBlock]
    · have := (hc u).1 (h _ u (by simpa using hu) rfl)
      rw [← this]
      simp [Ne.symm hu]
  · rintro h c j hj rfl
    rw [hc, ← h, mem_nbrs, graphOf_adj]
    simp [Ne.symm (by simpa using hj : j ≠ 0)]

variable {F : CNF ℕ}

omit [MulAction (Perm (Fin n)) {G // P G}] in
/-- The graphs with `N(0) = {1, …, k}`, counted by an embedded certificate for `nbrCnf F n k`. -/
theorem nbr_card_of_check [NeZero n]
    (hF : ∀ a : Fin (numEdges n) → Bool, F.eval (ext a) = true ↔ P (graphOf a)) (k : ℕ)
    {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (numEdges n) (nbrCnf F n k) pogStr lratStr N = true) :
    Nat.card {x : {G // P G} // nbrs x.1 0 = nbrBlock n k} = N :=
  Family.card_of_check ((equiv (P := fun G => P G ∧ nbrs G 0 = nbrBlock n k)
    fun a => (nbrCnf_eval F k a).trans (and_congr_left' (hF a))).symm.trans
      (Equiv.subtypeSubtypeEquivSubtypeInter P (fun G => nbrs G 0 = nbrBlock n k)).symm) h

omit [MulAction (Perm (Fin n)) {G // P G}] in
theorem nbr_card_of_checkAC [NeZero n]
    (hF : ∀ a : Fin (numEdges n) → Bool, F.eval (ext a) = true ↔ P (graphOf a)) (k : ℕ)
    {pogStr : String} {N : ℕ} (h : checkAllAC (numEdges n) (nbrCnf F n k) pogStr N = true)
    (hB : (fwdCnfOf (nbrCnf F n k) pogStr).Unsat) :
    Nat.card {x : {G // P G} // nbrs x.1 0 = nbrBlock n k} = N :=
  Family.card_of_checkAC ((equiv (P := fun G => P G ∧ nbrs G 0 = nbrBlock n k)
    fun a => (nbrCnf_eval F k a).trans (and_congr_left' (hF a))).symm.trans
      (Equiv.subtypeSubtypeEquivSubtypeInter P (fun G => nbrs G 0 = nbrBlock n k)).symm) h hB

omit [MulAction (Perm (Fin n)) {G // P G}] in
theorem nbr_card_of_unsat [NeZero n]
    (hF : ∀ a : Fin (numEdges n) → Bool, F.eval (ext a) = true ↔ P (graphOf a)) (k : ℕ)
    (h : (nbrCnf F n k).Unsat) : Nat.card {x : {G // P G} // nbrs x.1 0 = nbrBlock n k} = 0 :=
  Family.card_of_unsat ((equiv (P := fun G => P G ∧ nbrs G 0 = nbrBlock n k)
    fun a => (nbrCnf_eval F k a).trans (and_congr_left' (hF a))).symm.trans
      (Equiv.subtypeSubtypeEquivSubtypeInter P (fun G => nbrs G 0 = nbrBlock n k)).symm) h

end Split

/-! ## Cubes: counts under fixed edges, relabelling, and cell splits

A pattern `α` is a list of required adjacencies `(u, v, b)`: `Sat G α` says `G.Adj u v ↔ b`
for every entry. The graphs with `P` that satisfy `α` are the models of `cubeCnf F α` (the
encoder plus one unit clause per entry; `cube_card_of_check` and variants).

* Relabelling (`card_sat_relabel`, `card_sat_iso`): a permutation `σ` maps the graphs that
  satisfy `α` onto those that satisfy `relabel σ α`, so two patterns that are equal up to a
  relabelling (checked by `patEquiv`, `decide`) have the same count.
* Cell split (`card_sat_eq_sum`, `card_eq_of_cell`): if every permutation that fixes all
  vertices outside a list `C` preserves `α` (`cellOk`, checked by `decide`) and `v ∉ C`, the
  number of graphs that satisfy `α` and have `N(v) ∩ C = A` depends only on `|A|`, so
  `#α = Σ_j C(|C|, j) · #(α ++ star v C j)`, where `star v C j` makes `v` adjacent to the
  first `j` vertices of `C` and to no other vertex of `C`.

Starting from the empty pattern, a tree of cell splits refines the vertices step by step (the
neighbourhood split of vertex `0` is the first step); every leaf is a certified count, an LRAT
refutation, or a relabelling of another leaf. The multiplicities are binomial coefficients and
the leaves cover every graph by construction, so no class sizes or automorphism groups enter. -/

section Cube

/-- Required adjacencies `(u, v, b)`. -/
abbrev Pattern (n : ℕ) := List (Fin n × Fin n × Bool)

/-- `G` satisfies the pattern `α`. -/
def Sat (G : SimpleGraph (Fin n)) (α : Pattern n) : Prop :=
  ∀ e ∈ α, (G.Adj e.1 e.2.1 ↔ e.2.2 = true)

theorem sat_nil (G : SimpleGraph (Fin n)) : Sat G [] := by simp [Sat]

theorem sat_append {G : SimpleGraph (Fin n)} {α β : Pattern n} :
    Sat G (α ++ β) ↔ Sat G α ∧ Sat G β := by
  simp only [Sat, List.mem_append, or_imp, forall_and]

/-- The pattern moved by `σ`. -/
def relabel (σ : Perm (Fin n)) (α : Pattern n) : Pattern n :=
  α.map fun e => (σ e.1, σ e.2.1, e.2.2)

/-- The product of the swaps in the list (how the driver writes a relabelling). -/
def swaps (L : List (Fin n × Fin n)) : Perm (Fin n) := (L.map fun p => Equiv.swap p.1 p.2).prod

theorem sat_smul_relabel (σ : Perm (Fin n)) (G : SimpleGraph (Fin n)) (α : Pattern n) :
    Sat (σ • G) (relabel σ α) ↔ Sat G α := by
  simp only [Sat, relabel, List.forall_mem_map, smul_adj_apply]

theorem sat_smul (σ : Perm (Fin n)) (G : SimpleGraph (Fin n)) (α : Pattern n) :
    Sat (σ • G) α ↔ Sat G (relabel σ⁻¹ α) := by
  simp only [Sat, relabel, List.forall_mem_map, smul_adj]

/-- The entry `e` occurs in `β`, up to the orientation of the pair. -/
def entryMem (e : Fin n × Fin n × Bool) (β : Pattern n) : Bool :=
  β.any fun f => f.2.2 == e.2.2 &&
    ((f.1 == e.1 && f.2.1 == e.2.1) || (f.1 == e.2.1 && f.2.1 == e.1))

theorem sat_entry {G : SimpleGraph (Fin n)} {β : Pattern n} {e : Fin n × Fin n × Bool}
    (h : Sat G β) (he : entryMem e β = true) : G.Adj e.1 e.2.1 ↔ e.2.2 = true := by
  obtain ⟨f, hf, hfe⟩ := List.any_eq_true.1 he
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hfe
  have := h f hf
  rcases hfe with ⟨hb, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · rw [← h1, ← h2, ← hb]
    exact this
  · rw [G.adj_comm, ← h1, ← h2, ← hb]
    exact this

/-- Every entry of `α` occurs in `β`. -/
def patSub (α β : Pattern n) : Bool := α.all fun e => entryMem e β

theorem sat_of_patSub {G : SimpleGraph (Fin n)} {α β : Pattern n} (h : patSub α β = true)
    (hβ : Sat G β) : Sat G α :=
  fun e he => sat_entry hβ (List.all_eq_true.1 h e he)

/-- The two patterns have the same entries, up to orientation. -/
def patEquiv (α β : Pattern n) : Bool := patSub α β && patSub β α

theorem sat_iff_of_patEquiv {G : SimpleGraph (Fin n)} {α β : Pattern n}
    (h : patEquiv α β = true) : Sat G α ↔ Sat G β := by
  simp only [patEquiv, Bool.and_eq_true] at h
  exact ⟨sat_of_patSub h.2, sat_of_patSub h.1⟩

/-! ### Cells -/

/-- `C` is a cell of `α`: no entry has both ends in `C`, and an entry with one end in `C`
    occurs (with the same value) for every vertex of `C` in that place. -/
def cellOk (α : Pattern n) (C : List (Fin n)) : Bool :=
  α.all fun e =>
    if e.1 ∈ C then !decide (e.2.1 ∈ C) && C.all fun c => entryMem (c, e.2.1, e.2.2) α
    else if e.2.1 ∈ C then C.all fun c => entryMem (e.1, c, e.2.2) α
    else true

theorem mem_of_fix_out {C : List (Fin n)} {ρ : Perm (Fin n)} (hρ : ∀ x, x ∉ C → ρ x = x)
    {x : Fin n} (hx : x ∈ C) : ρ x ∈ C := by
  by_contra h
  have h' : ρ (ρ x) = ρ x := hρ _ h
  rw [ρ.injective h'] at h
  exact h hx

theorem sat_relabel_of_cell {α : Pattern n} {C : List (Fin n)} (hc : cellOk α C = true)
    {ρ : Perm (Fin n)} (hρ : ∀ x, x ∉ C → ρ x = x) {G : SimpleGraph (Fin n)} (h : Sat G α) :
    Sat G (relabel ρ α) := by
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  have hc0 := List.all_eq_true.1 hc e0 he0
  dsimp only
  by_cases h1 : e0.1 ∈ C
  · rw [if_pos h1] at hc0
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      List.all_eq_true] at hc0
    rw [hρ _ hc0.1]
    exact sat_entry h (hc0.2 _ (mem_of_fix_out hρ h1))
  · rw [if_neg h1] at hc0
    by_cases h2 : e0.2.1 ∈ C
    · rw [if_pos h2, List.all_eq_true] at hc0
      rw [hρ _ h1]
      exact sat_entry h (hc0 _ (mem_of_fix_out hρ h2))
    · rw [hρ _ h1, hρ _ h2]
      exact h e0 he0

/-- A permutation that fixes every vertex outside a cell of `α` preserves `Sat · α`. -/
theorem sat_smul_of_cell {α : Pattern n} {C : List (Fin n)} (hc : cellOk α C = true)
    {ρ : Perm (Fin n)} (hρ : ∀ x, x ∉ C → ρ x = x) (G : SimpleGraph (Fin n)) :
    Sat (ρ • G) α ↔ Sat G α := by
  constructor
  · intro h
    exact (sat_smul_relabel ρ G α).1 (sat_relabel_of_cell hc hρ h)
  · intro h
    have hρ' : ∀ x, x ∉ C → ρ⁻¹ x = x := fun x hx => by
      conv_lhs => rw [← hρ x hx]
      exact ρ.symm_apply_apply x
    exact (sat_smul ρ G α).2 (sat_relabel_of_cell hc hρ' h)

/-- `v` adjacent to the first `j` vertices of the list and to no other vertex of it. -/
def star (v : Fin n) : List (Fin n) → ℕ → Pattern n
  | [], _ => []
  | c :: C, j => (v, c, decide (0 < j)) :: star v C (j - 1)

theorem sat_star_iff {G : SimpleGraph (Fin n)} {v : Fin n} :
    ∀ {C : List (Fin n)} (_ : C.Nodup) (j : ℕ),
      Sat G (star v C j) ↔ ∀ c ∈ C, (G.Adj v c ↔ c ∈ C.take j)
  | [], _, j => by simp [star, Sat]
  | c :: C, hC, j => by
    rw [List.nodup_cons] at hC
    have ih := sat_star_iff (G := G) (v := v) hC.2 (j - 1)
    simp only [Sat, star, List.mem_cons, forall_eq_or_imp] at ih ⊢
    rw [ih]
    rcases j with _ | j
    · simp
    · simp only [Nat.add_one_sub_one, decide_eq_true_eq, Nat.zero_lt_succ, iff_true, true_or,
        List.take_succ_cons, List.mem_cons]
      apply and_congr_right'
      apply forall₂_congr
      intro c' hc'
      have : c' ≠ c := fun h => hC.1 (h ▸ hc')
      simp [this]

open Classical in
theorem sat_star_iff_nbrs {G : SimpleGraph (Fin n)} {v : Fin n} {C : List (Fin n)}
    (hC : C.Nodup) (j : ℕ) :
    Sat G (star v C j) ↔ nbrs G v ∩ C.toFinset = (C.take j).toFinset := by
  rw [sat_star_iff hC, Finset.ext_iff]
  simp only [Finset.mem_inter, mem_nbrs, List.mem_toFinset]
  constructor
  · intro h c
    constructor
    · rintro ⟨h1, h2⟩
      exact (h c h2).1 h1
    · intro h1
      have h2 := List.mem_of_mem_take h1
      exact ⟨(h c h2).2 h1, h2⟩
  · intro h c hc
    rw [← h c]
    simp [hc]

theorem card_take_toFinset {C : List (Fin n)} (hC : C.Nodup) {j : ℕ} (hj : j ≤ C.length) :
    (C.take j).toFinset.card = j := by
  rw [List.toFinset_card_of_nodup (hC.sublist (List.take_sublist j C)), List.length_take,
    min_eq_left hj]

/-- Two subsets of the same size of a set `C` are mapped onto each other by a permutation that
    fixes every vertex outside `C`. -/
theorem exists_perm_out_map {C A B : Finset (Fin n)} (hA : A ⊆ C) (hB : B ⊆ C)
    (h : A.card = B.card) : ∃ σ : Perm (Fin n), (∀ x, x ∉ C → σ x = x) ∧ ∀ w, σ w ∈ B ↔ w ∈ A := by
  classical
  let p : Fin n → Prop := (· ∈ C)
  let A' := A.subtype p
  let B' := B.subtype p
  have hcA : A'.card = A.card := by
    rw [Finset.card_subtype]
    exact congrArg Finset.card (Finset.filter_true_of_mem fun w hw => hA hw)
  have hcB : B'.card = B.card := by
    rw [Finset.card_subtype]
    exact congrArg Finset.card (Finset.filter_true_of_mem fun w hw => hB hw)
  let e0 : {x : Subtype p // x ∈ A'} ≃ {x : Subtype p // x ∈ B'} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hcA, hcB, h])
  let τ : Perm (Subtype p) := e0.extendSubtype
  refine ⟨Perm.ofSubtype τ, fun x hx => Perm.ofSubtype_apply_of_not_mem τ hx, fun w => ?_⟩
  by_cases hw : w ∈ C
  · have hy : w = ((⟨w, hw⟩ : Subtype p) : Fin n) := rfl
    rw [hy, Perm.ofSubtype_apply_coe]
    have hmB : ∀ y : Subtype p, (y : Fin n) ∈ B ↔ y ∈ B' := fun y => by simp [B']
    have hmA : ∀ y : Subtype p, (y : Fin n) ∈ A ↔ y ∈ A' := fun y => by simp [A']
    rw [hmB, hmA]
    constructor
    · intro h1
      by_contra h2
      exact Equiv.extendSubtype_not_mem e0 _ h2 h1
    · exact Equiv.extendSubtype_mem e0 _
  · rw [Perm.ofSubtype_apply_of_not_mem τ hw]
    exact iff_of_false (fun h => hw (hB h)) (fun h => hw (hA h))

variable {P : SimpleGraph (Fin n) → Prop} [MulAction (Perm (Fin n)) {G // P G}]

omit [MulAction (Perm (Fin n)) {G // P G}] in
theorem card_sat_nil : Nat.card {x : {G // P G} // Sat x.1 []} = Nat.card {G // P G} :=
  Nat.card_congr (Equiv.subtypeUnivEquiv fun x => sat_nil x.1)

omit [MulAction (Perm (Fin n)) {G // P G}] in
theorem card_sat_congr {α β : Pattern n} (h : patEquiv α β = true) :
    Nat.card {x : {G // P G} // Sat x.1 α} = Nat.card {x : {G // P G} // Sat x.1 β} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => sat_iff_of_patEquiv h)

/-- Relabelling: the graphs that satisfy `α` and those that satisfy `relabel σ α` are
    equinumerous. -/
theorem card_sat_relabel (hact : ∀ (σ : Perm (Fin n)) (x : {G // P G}), (σ • x).1 = σ • x.1)
    (σ : Perm (Fin n)) (α : Pattern n) :
    Nat.card {x : {G // P G} // Sat x.1 α} = Nat.card {x : {G // P G} // Sat x.1 (relabel σ α)} :=
  Nat.card_congr
    { toFun := fun x => ⟨σ • x.1, by rw [hact, sat_smul_relabel]; exact x.2⟩
      invFun := fun y => ⟨σ⁻¹ • y.1, by
        rw [← sat_smul_relabel σ, ← hact, smul_inv_smul]; exact y.2⟩
      left_inv := fun x => Subtype.ext (inv_smul_smul σ x.1)
      right_inv := fun y => Subtype.ext (smul_inv_smul σ y.1) }

/-- Two patterns that agree up to the relabelling `σ` have the same count. -/
theorem card_sat_iso (hact : ∀ (σ : Perm (Fin n)) (x : {G // P G}), (σ • x).1 = σ • x.1)
    (σ : Perm (Fin n)) {α β : Pattern n} (h : patEquiv (relabel σ α) β = true) :
    Nat.card {x : {G // P G} // Sat x.1 α} = Nat.card {x : {G // P G} // Sat x.1 β} :=
  (card_sat_relabel hact σ α).trans (card_sat_congr h)

/-- For a fixed neighbourhood `S` of `v`, the number of graphs with `P` whose induced graph on
    `S` agrees with `H` is the same for `H` and for every relabelling `σ • H` by a permutation
    that fixes all vertices outside `S`. -/
theorem card_nbrs_induce_eq (hact : ∀ (σ : Perm (Fin n)) (x : {G // P G}), (σ • x).1 = σ • x.1)
    (v : Fin n) (S : Finset (Fin n)) (hv : v ∉ S) (σ : Perm (Fin n)) (hσ : ∀ x, x ∉ S → σ x = x)
    (H : SimpleGraph (Fin n)) :
    Nat.card {x : {G // P G} // nbrs x.1 v = S ∧ ∀ a ∈ S, ∀ b ∈ S, (x.1.Adj a b ↔ H.Adj a b)} =
      Nat.card {x : {G // P G} //
        nbrs x.1 v = S ∧ ∀ a ∈ S, ∀ b ∈ S, (x.1.Adj a b ↔ (σ • H).Adj a b)} := by
  have hmem : ∀ w, σ w ∈ S ↔ w ∈ S := fun w => by
    constructor
    · intro h
      by_contra hw
      rw [hσ w hw] at h
      exact hw h
    · intro h
      by_contra h'
      have := hσ _ h'
      rw [σ.injective this] at h'
      exact h' h
  have hsv : σ v = v := hσ v hv
  have key : ∀ G : SimpleGraph (Fin n),
      (nbrs (σ • G) v = S ∧ ∀ a ∈ S, ∀ b ∈ S, ((σ • G).Adj a b ↔ (σ • H).Adj a b)) ↔
      (nbrs G v = S ∧ ∀ a ∈ S, ∀ b ∈ S, (G.Adj a b ↔ H.Adj a b)) := by
    intro G
    have hn : nbrs (σ • G) v = S ↔ nbrs G v = S := by
      constructor
      · intro h
        ext w
        rw [← mem_nbrs_smul hsv, h, hmem]
      · intro h
        ext u
        obtain ⟨w, rfl⟩ : ∃ w, σ w = u := ⟨σ⁻¹ u, σ.apply_symm_apply u⟩
        rw [mem_nbrs_smul hsv, h, hmem]
    rw [hn]
    apply and_congr_right'
    constructor
    · intro h a ha b hb
      have := h (σ a) ((hmem a).2 ha) (σ b) ((hmem b).2 hb)
      rwa [smul_adj_apply, smul_adj_apply] at this
    · intro h a ha b hb
      obtain ⟨a', rfl⟩ : ∃ w, σ w = a := ⟨σ⁻¹ a, σ.apply_symm_apply a⟩
      obtain ⟨b', rfl⟩ : ∃ w, σ w = b := ⟨σ⁻¹ b, σ.apply_symm_apply b⟩
      rw [smul_adj_apply, smul_adj_apply]
      exact h a' ((hmem a').1 ha) b' ((hmem b').1 hb)
  exact Nat.card_congr
    { toFun := fun x => ⟨σ • x.1, by rw [hact]; exact (key x.1.1).2 x.2⟩
      invFun := fun y => ⟨σ⁻¹ • y.1, (key _).1 (by rw [← hact, smul_inv_smul]; exact y.2)⟩
      left_inv := fun x => Subtype.ext (inv_smul_smul σ x.1)
      right_inv := fun y => Subtype.ext (smul_inv_smul σ y.1) }

open Classical in
/-- The fibres of a cell split: graphs that satisfy `α` and have `N(v) ∩ C = A`, for `A ⊆ C`,
    are as many as those that satisfy `α ++ star v C |A|`. -/
theorem card_fibre_eq (hact : ∀ (σ : Perm (Fin n)) (x : {G // P G}), (σ • x).1 = σ • x.1)
    {α : Pattern n} {v : Fin n} {C : List (Fin n)} (hC : C.Nodup) (hv : v ∉ C)
    (hc : cellOk α C = true) {A : Finset (Fin n)} (hA : A ⊆ C.toFinset) :
    Nat.card {x : {x : {G // P G} // Sat x.1 α} // nbrs x.1.1 v ∩ C.toFinset = A} =
      Nat.card {x : {G // P G} // Sat x.1 (α ++ star v C A.card)} := by
  have hAC : A.card ≤ C.length := by
    have := Finset.card_le_card hA
    rwa [List.toFinset_card_of_nodup hC] at this
  set B := (C.take A.card).toFinset with hBdef
  have hB : B ⊆ C.toFinset := fun x hx => by
    simp only [hBdef, List.mem_toFinset] at hx ⊢
    exact List.mem_of_mem_take hx
  obtain ⟨σ, hσC, hσ⟩ := exists_perm_out_map hA hB (card_take_toFinset hC hAC).symm
  have hσC' : ∀ x, x ∉ C → σ x = x := fun x hx => hσC x (by simpa using hx)
  have hsv : σ v = v := hσC' v hv
  have hmemC : ∀ w, σ w ∈ C.toFinset ↔ w ∈ C.toFinset := fun w => by
    simp only [List.mem_toFinset]
    constructor
    · intro h
      by_contra hw
      rw [hσC' w hw] at h
      exact hw h
    · exact mem_of_fix_out hσC'
  have key : ∀ G : SimpleGraph (Fin n),
      nbrs (σ • G) v ∩ C.toFinset = B ↔ nbrs G v ∩ C.toFinset = A := by
    intro G
    constructor
    · intro h
      ext w
      rw [← hσ, ← h, Finset.mem_inter, Finset.mem_inter, mem_nbrs_smul hsv, hmemC]
    · intro h
      ext u
      obtain ⟨w, rfl⟩ : ∃ w, σ w = u := ⟨σ⁻¹ u, σ.apply_symm_apply u⟩
      rw [hσ, ← h, Finset.mem_inter, Finset.mem_inter, mem_nbrs_smul hsv, hmemC]
  have hsat : ∀ G : SimpleGraph (Fin n), Sat (σ • G) α ↔ Sat G α :=
    sat_smul_of_cell hc hσC'
  have e1 : {x : {x : {G // P G} // Sat x.1 α} // nbrs x.1.1 v ∩ C.toFinset = A} ≃
      {x : {x : {G // P G} // Sat x.1 α} // nbrs x.1.1 v ∩ C.toFinset = B} :=
    { toFun := fun x => ⟨⟨σ • x.1.1, by rw [hact, hsat]; exact x.1.2⟩,
        by simp only [hact]; exact (key _).2 x.2⟩
      invFun := fun y => ⟨⟨σ⁻¹ • y.1.1, by
          rw [← hsat, ← hact, smul_inv_smul]; exact y.1.2⟩,
        (key _).1 (by rw [← hact, smul_inv_smul]; exact y.2)⟩
      left_inv := fun x => Subtype.ext (Subtype.ext (inv_smul_smul σ x.1.1))
      right_inv := fun y => Subtype.ext (Subtype.ext (smul_inv_smul σ y.1.1)) }
  have e2 : {x : {x : {G // P G} // Sat x.1 α} // nbrs x.1.1 v ∩ C.toFinset = B} ≃
      {x : {G // P G} // Sat x.1 (α ++ star v C A.card)} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun x : {G // P G} => Sat x.1 α)
      (fun x => nbrs x.1 v ∩ C.toFinset = B)).trans
      (Equiv.subtypeEquivRight fun _ => by rw [sat_append, sat_star_iff_nbrs hC])
  exact Nat.card_congr (e1.trans e2)

/-- The cell split: `#α = Σ_j C(|C|, j) · #(α ++ star v C j)`. -/
theorem card_sat_eq_sum (hact : ∀ (σ : Perm (Fin n)) (x : {G // P G}), (σ • x).1 = σ • x.1)
    {α : Pattern n} {v : Fin n} {C : List (Fin n)} (hC : C.Nodup) (hv : v ∉ C)
    (hc : cellOk α C = true) :
    Nat.card {x : {G // P G} // Sat x.1 α} = ∑ j ∈ Finset.range (C.length + 1),
      C.length.choose j * Nat.card {x : {G // P G} // Sat x.1 (α ++ star v C j)} := by
  classical
  have : Fintype {G // P G} := Fintype.ofFinite _
  let X := {x : {G // P G} // Sat x.1 α}
  let g : ℕ → ℕ := fun j => Nat.card {x : {G // P G} // Sat x.1 (α ++ star v C j)}
  have hsub : ∀ x : X, nbrs x.1.1 v ∩ C.toFinset ∈ C.toFinset.powerset := fun x =>
    Finset.mem_powerset.2 Finset.inter_subset_right
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := fun x : X => nbrs x.1.1 v ∩ C.toFinset)
      (t := C.toFinset.powerset) (fun x _ => hsub x)]
  have hfib : ∀ A ∈ C.toFinset.powerset,
      (Finset.univ.filter fun x : X => nbrs x.1.1 v ∩ C.toFinset = A).card = g A.card := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_fibre_eq hact hC hv hc hA
  rw [Finset.sum_congr rfl hfib, Finset.sum_powerset_apply_card,
    List.toFinset_card_of_nodup hC]
  simp only [smul_eq_mul, g]

/-- The side condition of `card_eq_of_cell`: a valid cell, one count for each `j ≤ |C|`, and
    `Σ_j C(|C|, j) · count_j = N`. -/
def checkCell (α : Pattern n) (v : Fin n) (C : List (Fin n)) (N : ℕ) (L : List (ℕ × ℕ)) : Bool :=
  decide C.Nodup && !decide (v ∈ C) && cellOk α C &&
    L.map Prod.fst == List.range (C.length + 1) &&
    (L.map fun p => C.length.choose p.1 * p.2).sum == N

/-- The count of a pattern from the counts of its children in a cell split. -/
theorem card_eq_of_cell (hact : ∀ (σ : Perm (Fin n)) (x : {G // P G}), (σ • x).1 = σ • x.1)
    (α : Pattern n) (v : Fin n) (C : List (Fin n)) (N : ℕ) (L : List (ℕ × ℕ))
    (hfix : ∀ p ∈ L, Nat.card {x : {G // P G} // Sat x.1 (α ++ star v C p.1)} = p.2)
    (hc : checkCell α v C N L = true) : Nat.card {x : {G // P G} // Sat x.1 α} = N := by
  simp only [checkCell, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at hc
  obtain ⟨⟨⟨⟨hC, hv⟩, hcell⟩, hL⟩, hN⟩ := hc
  rw [card_sat_eq_sum hact hC hv hcell, ← List.toFinset_range, List.sum_toFinset _ List.nodup_range,
    ← hL, List.map_map, ← hN]
  congr 1
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply, hfix p hp]

/-! ### Leaves: the encoder plus unit clauses -/

theorem ext_edgeVar_self (a : Fin (numEdges n) → Bool) (u : Fin n) : ext a (edgeVar u u) = false := by
  have h : (u, u) ∉ Complete.edges n := fun h => lt_irrefl _ (Complete.mem_edges.1 h)
  have : edgeVar u u = numEdges n := by
    simp only [edgeVar, min_self, max_self]
    exact List.idxOf_eq_length h
  simp [ext, this]

theorem graphOf_adj_iff_ext (a : Fin (numEdges n) → Bool) (u v : Fin n) :
    (graphOf a).Adj u v ↔ ext a (edgeVar u v) = true := by
  rw [graphOf_adj]
  by_cases h : u = v
  · subst h
    simp [ext_edgeVar_self]
  · simp [h]

/-- The encoder `F` with the entries of `α` as unit clauses. -/
def cubeCnf (F : CNF ℕ) (α : Pattern n) : CNF ℕ :=
  F ++ ⟨(α.map fun e => [(edgeVar e.1 e.2.1, e.2.2)]).toArray⟩

theorem cubeCnf_eval (F : CNF ℕ) (α : Pattern n) (a : Fin (numEdges n) → Bool) :
    (cubeCnf F α).eval (ext a) = true ↔ F.eval (ext a) = true ∧ Sat (graphOf a) α := by
  simp only [cubeCnf, CNF.eval_append, Bool.and_eq_true]
  apply and_congr_right'
  unfold CNF.eval
  rw [Array.all_eq_true_iff_forall_mem]
  simp only [List.mem_toArray, List.forall_mem_map, Sat, graphOf_adj_iff_ext]
  apply forall₂_congr
  intro e _
  simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false, beq_iff_eq]
  cases ext a (edgeVar e.1 e.2.1) <;> cases e.2.2 <;> simp

variable {F : CNF ℕ}

omit [MulAction (Perm (Fin n)) {G // P G}] in
/-- The models of `cubeCnf F α` are the graphs with `P` that satisfy `α`. -/
noncomputable def cube_equiv (hF : ∀ a : Fin (numEdges n) → Bool, F.eval (ext a) = true ↔ P (graphOf a))
    (α : Pattern n) :
    {a : Fin (numEdges n) → Bool // (cubeCnf F α).eval (ext a) = true} ≃
      {x : {G // P G} // Sat x.1 α} :=
  (equiv (P := fun G => P G ∧ Sat G α)
    fun a => (cubeCnf_eval F α a).trans (and_congr_left' (hF a))).symm.trans
      (Equiv.subtypeSubtypeEquivSubtypeInter P (fun G => Sat G α)).symm

omit [MulAction (Perm (Fin n)) {G // P G}] in
/-- The graphs that satisfy `α`, counted by an embedded certificate for `cubeCnf F α`. -/
theorem cube_card_of_check
    (hF : ∀ a : Fin (numEdges n) → Bool, F.eval (ext a) = true ↔ P (graphOf a)) (α : Pattern n)
    {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (numEdges n) (cubeCnf F α) pogStr lratStr N = true) :
    Nat.card {x : {G // P G} // Sat x.1 α} = N :=
  Family.card_of_check (cube_equiv hF α) h

omit [MulAction (Perm (Fin n)) {G // P G}] in
theorem cube_card_of_checkAC
    (hF : ∀ a : Fin (numEdges n) → Bool, F.eval (ext a) = true ↔ P (graphOf a)) (α : Pattern n)
    {pogStr : String} {N : ℕ} (h : checkAllAC (numEdges n) (cubeCnf F α) pogStr N = true)
    (hB : (fwdCnfOf (cubeCnf F α) pogStr).Unsat) :
    Nat.card {x : {G // P G} // Sat x.1 α} = N :=
  Family.card_of_checkAC (cube_equiv hF α) h hB

omit [MulAction (Perm (Fin n)) {G // P G}] in
theorem cube_card_of_unsat
    (hF : ∀ a : Fin (numEdges n) → Bool, F.eval (ext a) = true ↔ P (graphOf a)) (α : Pattern n)
    (h : (cubeCnf F α).Unsat) : Nat.card {x : {G // P G} // Sat x.1 α} = 0 :=
  Family.card_of_unsat (cube_equiv hF α) h

end Cube

end CountCatcher.GraphIso

/-! ## The families, as `count_models` lemmas -/

namespace CountCatcher.CliqueFreeFam

open CountCatcher.GraphIso CountCatcher.CycleType

variable {n s : ℕ}

theorem hact (σ : Perm (Fin n)) (x : {G : SimpleGraph (Fin n) // G.CliqueFree s}) :
    (σ • x).1 = σ • x.1 := rfl

/-- The labelled count: graphs on `Fin n` without an `s`-clique. -/
theorem card_of_check {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (numEdges n) (cliqueCnfN n s) pogStr lratStr N = true) :
    Nat.card {G : SimpleGraph (Fin n) // G.CliqueFree s} = N :=
  Family.card_of_check (equiv (cliqueCnfN_eval s)).symm h

theorem card_of_checkAC {pogStr : String} {N : ℕ}
    (h : checkAllAC (numEdges n) (cliqueCnfN n s) pogStr N = true)
    (hB : (fwdCnfOf (cliqueCnfN n s) pogStr).Unsat) :
    Nat.card {G : SimpleGraph (Fin n) // G.CliqueFree s} = N :=
  Family.card_of_checkAC (equiv (cliqueCnfN_eval s)).symm h hB

theorem card_of_unsat (h : (cliqueCnfN n s).Unsat) :
    Nat.card {G : SimpleGraph (Fin n) // G.CliqueFree s} = 0 :=
  Family.card_of_unsat (equiv (cliqueCnfN_eval s)).symm h

/-- The graphs fixed by the representative of the cycle type `l`. -/
theorem fix_card_of_check {l : List ℕ} {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (numEdges n) (symCnf (cliqueCnfN n s) (numEdges n) (edgePerm n (rep n l)))
      pogStr lratStr N = true) :
    Nat.card (fixedBy {G : SimpleGraph (Fin n) // G.CliqueFree s} (rep n l)) = N :=
  GraphIso.fix_card_of_check hact (cliqueCnfN_eval s) _ h

theorem fix_card_of_checkAC {l : List ℕ} {pogStr : String} {N : ℕ}
    (h : checkAllAC (numEdges n) (symCnf (cliqueCnfN n s) (numEdges n) (edgePerm n (rep n l)))
      pogStr N = true)
    (hB : (fwdCnfOf (symCnf (cliqueCnfN n s) (numEdges n) (edgePerm n (rep n l))) pogStr).Unsat) :
    Nat.card (fixedBy {G : SimpleGraph (Fin n) // G.CliqueFree s} (rep n l)) = N :=
  GraphIso.fix_card_of_checkAC hact (cliqueCnfN_eval s) _ h hB

theorem fix_card_of_unsat {l : List ℕ}
    (h : (symCnf (cliqueCnfN n s) (numEdges n) (edgePerm n (rep n l))).Unsat) :
    Nat.card (fixedBy {G : SimpleGraph (Fin n) // G.CliqueFree s} (rep n l)) = 0 :=
  GraphIso.fix_card_of_unsat hact (cliqueCnfN_eval s) _ h

/-- The identity term of Burnside's sum is the labelled count. -/
theorem fix_nil {c : ℕ} (h : Nat.card {G : SimpleGraph (Fin n) // G.CliqueFree s} = c) :
    Nat.card (fixedBy {G : SimpleGraph (Fin n) // G.CliqueFree s} (rep n [])) = c := by
  rw [show rep n [] = 1 from rfl, fixedBy_one_eq_univ, Nat.card_univ, h]

/-- Graphs without an `s`-clique up to isomorphism, as orbits and as isomorphism classes. -/
theorem card_orbits_eq (N : ℕ) (L : List (List ℕ × ℕ))
    (hfix : ∀ p ∈ L, Nat.card (fixedBy {G : SimpleGraph (Fin n) // G.CliqueFree s} (rep n p.1)) = p.2)
    (hc : checkClasses n N L = true) :
    Nat.card (orbitRel.Quotient (Perm (Fin n)) {G : SimpleGraph (Fin n) // G.CliqueFree s}) = N :=
  CycleType.card_orbits_eq N L hfix hc

theorem card_isoClasses_eq {N : ℕ}
    (h : Nat.card (orbitRel.Quotient (Perm (Fin n)) {G : SimpleGraph (Fin n) // G.CliqueFree s}) = N) :
    Nat.card (Quot fun G H : {G : SimpleGraph (Fin n) // G.CliqueFree s} => Nonempty (G.1 ≃g H.1)) = N := by
  rw [card_isoClasses hact, h]

/-- Graphs whose vertex `0` has the neighbourhood `{1, …, k}` (the split of the labelled count). -/
theorem nbr_card_of_check {k : ℕ} [NeZero n] {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (numEdges n) (nbrCnf (cliqueCnfN n s) n k) pogStr lratStr N = true) :
    Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s} // nbrs x.1 0 = nbrBlock n k} = N :=
  GraphIso.nbr_card_of_check (cliqueCnfN_eval s) k h

theorem nbr_card_of_checkAC {k : ℕ} [NeZero n] {pogStr : String} {N : ℕ}
    (h : checkAllAC (numEdges n) (nbrCnf (cliqueCnfN n s) n k) pogStr N = true)
    (hB : (fwdCnfOf (nbrCnf (cliqueCnfN n s) n k) pogStr).Unsat) :
    Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s} // nbrs x.1 0 = nbrBlock n k} = N :=
  GraphIso.nbr_card_of_checkAC (cliqueCnfN_eval s) k h hB

theorem nbr_card_of_unsat {k : ℕ} [NeZero n] (h : (nbrCnf (cliqueCnfN n s) n k).Unsat) :
    Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s} // nbrs x.1 0 = nbrBlock n k} = 0 :=
  GraphIso.nbr_card_of_unsat (cliqueCnfN_eval s) k h

/-- The labelled count from the counts per neighbourhood size of vertex `0`. -/
theorem card_eq_of_split [NeZero n] (N : ℕ) (L : List (ℕ × ℕ))
    (hfix : ∀ p ∈ L, Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s} //
      nbrs x.1 0 = nbrBlock n p.1} = p.2)
    (hc : checkSplit n N L = true) : Nat.card {G : SimpleGraph (Fin n) // G.CliqueFree s} = N :=
  GraphIso.card_eq_of_split hact N L hfix hc


/-- The graphs that satisfy the pattern `α` (a cube of the cell-split tree). -/
theorem cube_card_of_check {α : Pattern n} {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (numEdges n) (cubeCnf (cliqueCnfN n s) α) pogStr lratStr N = true) :
    Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s} // Sat x.1 α} = N :=
  GraphIso.cube_card_of_check (cliqueCnfN_eval s) α h

theorem cube_card_of_checkAC {α : Pattern n} {pogStr : String} {N : ℕ}
    (h : checkAllAC (numEdges n) (cubeCnf (cliqueCnfN n s) α) pogStr N = true)
    (hB : (fwdCnfOf (cubeCnf (cliqueCnfN n s) α) pogStr).Unsat) :
    Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s} // Sat x.1 α} = N :=
  GraphIso.cube_card_of_checkAC (cliqueCnfN_eval s) α h hB

theorem cube_card_of_unsat {α : Pattern n} (h : (cubeCnf (cliqueCnfN n s) α).Unsat) :
    Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s} // Sat x.1 α} = 0 :=
  GraphIso.cube_card_of_unsat (cliqueCnfN_eval s) α h

/-- A node of the cell-split tree from its children. -/
theorem card_eq_of_cell (α : Pattern n) (v : Fin n) (C : List (Fin n)) (N : ℕ) (L : List (ℕ × ℕ))
    (hfix : ∀ p ∈ L, Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s} // Sat x.1 (α ++ star v C p.1)} = p.2)
    (hc : checkCell α v C N L = true) : Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s} // Sat x.1 α} = N :=
  GraphIso.card_eq_of_cell hact α v C N L hfix hc

/-- A leaf that is a relabelling of another leaf. -/
theorem card_sat_iso (σ : Perm (Fin n)) {α β : Pattern n} (h : patEquiv (relabel σ α) β = true)
    {N : ℕ} (hβ : Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s} // Sat x.1 β} = N) :
    Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s} // Sat x.1 α} = N :=
  (GraphIso.card_sat_iso hact σ h).trans hβ

/-- The labelled count from the root of the tree (the empty pattern). -/
theorem card_of_root {N : ℕ} (h : Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s} // Sat x.1 []} = N) :
    Nat.card {G : SimpleGraph (Fin n) // G.CliqueFree s} = N :=
  card_sat_nil.symm.trans h

end CountCatcher.CliqueFreeFam

namespace CountCatcher.RamseyFam

open CountCatcher.GraphIso CountCatcher.CycleType

variable {n s t : ℕ}

theorem hact (σ : Perm (Fin n)) (x : {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t}) :
    (σ • x).1 = σ • x.1 := rfl

/-- The labelled count: graphs on `Fin n` without an `s`-clique and without an independent
    `t`-set. -/
theorem card_of_check {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (numEdges n) (ramseyCnfN n s t) pogStr lratStr N = true) :
    Nat.card {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} = N :=
  Family.card_of_check (equiv (ramseyCnfN_eval s t)).symm h

theorem card_of_checkAC {pogStr : String} {N : ℕ}
    (h : checkAllAC (numEdges n) (ramseyCnfN n s t) pogStr N = true)
    (hB : (fwdCnfOf (ramseyCnfN n s t) pogStr).Unsat) :
    Nat.card {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} = N :=
  Family.card_of_checkAC (equiv (ramseyCnfN_eval s t)).symm h hB

theorem card_of_unsat (h : (ramseyCnfN n s t).Unsat) :
    Nat.card {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} = 0 :=
  Family.card_of_unsat (equiv (ramseyCnfN_eval s t)).symm h

theorem fix_card_of_check {l : List ℕ} {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (numEdges n) (symCnf (ramseyCnfN n s t) (numEdges n) (edgePerm n (rep n l)))
      pogStr lratStr N = true) :
    Nat.card (fixedBy {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} (rep n l)) = N :=
  GraphIso.fix_card_of_check hact (ramseyCnfN_eval s t) _ h

theorem fix_card_of_checkAC {l : List ℕ} {pogStr : String} {N : ℕ}
    (h : checkAllAC (numEdges n) (symCnf (ramseyCnfN n s t) (numEdges n) (edgePerm n (rep n l)))
      pogStr N = true)
    (hB : (fwdCnfOf (symCnf (ramseyCnfN n s t) (numEdges n) (edgePerm n (rep n l))) pogStr).Unsat) :
    Nat.card (fixedBy {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} (rep n l)) = N :=
  GraphIso.fix_card_of_checkAC hact (ramseyCnfN_eval s t) _ h hB

theorem fix_card_of_unsat {l : List ℕ}
    (h : (symCnf (ramseyCnfN n s t) (numEdges n) (edgePerm n (rep n l))).Unsat) :
    Nat.card (fixedBy {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} (rep n l)) = 0 :=
  GraphIso.fix_card_of_unsat hact (ramseyCnfN_eval s t) _ h

theorem fix_nil {c : ℕ}
    (h : Nat.card {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} = c) :
    Nat.card (fixedBy {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} (rep n [])) = c := by
  rw [show rep n [] = 1 from rfl, fixedBy_one_eq_univ, Nat.card_univ, h]

theorem card_orbits_eq (N : ℕ) (L : List (List ℕ × ℕ))
    (hfix : ∀ p ∈ L, Nat.card
      (fixedBy {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} (rep n p.1)) = p.2)
    (hc : checkClasses n N L = true) :
    Nat.card (orbitRel.Quotient (Perm (Fin n))
      {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t}) = N :=
  CycleType.card_orbits_eq N L hfix hc

theorem card_isoClasses_eq {N : ℕ}
    (h : Nat.card (orbitRel.Quotient (Perm (Fin n))
      {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t}) = N) :
    Nat.card (Quot fun G H : {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} =>
      Nonempty (G.1 ≃g H.1)) = N := by
  rw [card_isoClasses hact, h]

theorem nbr_card_of_check {k : ℕ} [NeZero n] {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (numEdges n) (nbrCnf (ramseyCnfN n s t) n k) pogStr lratStr N = true) :
    Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} //
      nbrs x.1 0 = nbrBlock n k} = N :=
  GraphIso.nbr_card_of_check (ramseyCnfN_eval s t) k h

theorem nbr_card_of_checkAC {k : ℕ} [NeZero n] {pogStr : String} {N : ℕ}
    (h : checkAllAC (numEdges n) (nbrCnf (ramseyCnfN n s t) n k) pogStr N = true)
    (hB : (fwdCnfOf (nbrCnf (ramseyCnfN n s t) n k) pogStr).Unsat) :
    Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} //
      nbrs x.1 0 = nbrBlock n k} = N :=
  GraphIso.nbr_card_of_checkAC (ramseyCnfN_eval s t) k h hB

theorem nbr_card_of_unsat {k : ℕ} [NeZero n] (h : (nbrCnf (ramseyCnfN n s t) n k).Unsat) :
    Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} //
      nbrs x.1 0 = nbrBlock n k} = 0 :=
  GraphIso.nbr_card_of_unsat (ramseyCnfN_eval s t) k h

theorem card_eq_of_split [NeZero n] (N : ℕ) (L : List (ℕ × ℕ))
    (hfix : ∀ p ∈ L, Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} //
      nbrs x.1 0 = nbrBlock n p.1} = p.2)
    (hc : checkSplit n N L = true) :
    Nat.card {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} = N :=
  GraphIso.card_eq_of_split hact N L hfix hc


/-- The graphs that satisfy the pattern `α` (a cube of the cell-split tree). -/
theorem cube_card_of_check {α : Pattern n} {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (numEdges n) (cubeCnf (ramseyCnfN n s t) α) pogStr lratStr N = true) :
    Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} // Sat x.1 α} = N :=
  GraphIso.cube_card_of_check (ramseyCnfN_eval s t) α h

theorem cube_card_of_checkAC {α : Pattern n} {pogStr : String} {N : ℕ}
    (h : checkAllAC (numEdges n) (cubeCnf (ramseyCnfN n s t) α) pogStr N = true)
    (hB : (fwdCnfOf (cubeCnf (ramseyCnfN n s t) α) pogStr).Unsat) :
    Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} // Sat x.1 α} = N :=
  GraphIso.cube_card_of_checkAC (ramseyCnfN_eval s t) α h hB

theorem cube_card_of_unsat {α : Pattern n} (h : (cubeCnf (ramseyCnfN n s t) α).Unsat) :
    Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} // Sat x.1 α} = 0 :=
  GraphIso.cube_card_of_unsat (ramseyCnfN_eval s t) α h

/-- A node of the cell-split tree from its children. -/
theorem card_eq_of_cell (α : Pattern n) (v : Fin n) (C : List (Fin n)) (N : ℕ) (L : List (ℕ × ℕ))
    (hfix : ∀ p ∈ L, Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} // Sat x.1 (α ++ star v C p.1)} = p.2)
    (hc : checkCell α v C N L = true) : Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} // Sat x.1 α} = N :=
  GraphIso.card_eq_of_cell hact α v C N L hfix hc

/-- A leaf that is a relabelling of another leaf. -/
theorem card_sat_iso (σ : Perm (Fin n)) {α β : Pattern n} (h : patEquiv (relabel σ α) β = true)
    {N : ℕ} (hβ : Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} // Sat x.1 β} = N) :
    Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} // Sat x.1 α} = N :=
  (GraphIso.card_sat_iso hact σ h).trans hβ

/-- The labelled count from the root of the tree (the empty pattern). -/
theorem card_of_root {N : ℕ} (h : Nat.card {x : {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} // Sat x.1 []} = N) :
    Nat.card {G : SimpleGraph (Fin n) // G.CliqueFree s ∧ Gᶜ.CliqueFree t} = N :=
  card_sat_nil.symm.trans h

end CountCatcher.RamseyFam
