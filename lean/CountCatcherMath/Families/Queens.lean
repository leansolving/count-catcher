import CountCatcherMath.Families.Matching

/-!
# n-queens

Encoder: cell `(r, c)` is variable `r * n + c`. Per row an at-least-one clause and pairwise
at-most-one clauses, then pairwise at-most-one clauses per column, per diagonal (`r - c`
constant, Python's `d = k - (n - 1)` for `k < 2n - 1`) and per anti-diagonal (`r + c = s`),
in the order of `scripts/gen_queens.py` (the DIMACS export is byte-identical). Family lemma:
the models correspond to the placements `f : Fin n → Fin n` (the queen of row `r` stands in
column `f r`) in which no two queens share a column or a diagonal.
-/

open Std.Sat

namespace CountCatcher.Queens

/-- Pairwise at-most-one clauses over `l`, in the order of Python's `combinations(l, 2)`. -/
def amo (l : List ℕ) : List (CNF.Clause ℕ) :=
  (Matching.pairs l).map fun p => [(p.1, false), (p.2, false)]

def rowCells (n r : ℕ) : List ℕ := (List.range n).map fun c => r * n + c
def colCells (n c : ℕ) : List ℕ := (List.range n).map fun r => r * n + c
/-- Diagonal `k`: the cells `(r, r + (n - 1) - k)`. -/
def diagCells (n k : ℕ) : List ℕ :=
  ((List.range n).filter fun r => r ≤ k ∧ k < r + n).map fun r => r * n + (r + (n - 1) - k)
/-- Anti-diagonal `s`: the cells `(r, s - r)`. -/
def antiCells (n s : ℕ) : List ℕ :=
  ((List.range n).filter fun r => r ≤ s ∧ s < r + n).map fun r => r * n + (s - r)

def clauses (n : ℕ) : List (CNF.Clause ℕ) :=
  (List.range n).flatMap (fun r => ((rowCells n r).map fun i => (i, true)) :: amo (rowCells n r)) ++
  (List.range n).flatMap (fun c => amo (colCells n c)) ++
  (List.range (2 * n - 1)).flatMap (fun k => amo (diagCells n k)) ++
  (List.range (2 * n - 1)).flatMap (fun s => amo (antiCells n s))

/-- The n-queens CNF. -/
def cnf (n : ℕ) : CNF ℕ := ⟨(clauses n).toArray⟩

/-- No two queens share a column, a diagonal or an anti-diagonal (rows are distinct by the
    shape of `f`). -/
def Safe {n : ℕ} (f : Fin n → Fin n) : Prop :=
  ∀ i j, i ≠ j → f i ≠ f j ∧ (i : ℕ) + f j ≠ j + f i ∧ (i : ℕ) + f i ≠ j + f j

variable {n : ℕ}

/-! ## Clause semantics -/

theorem amo_eval {l : List ℕ} (hl : l.Nodup) (v : ℕ → Bool) :
    (∀ c ∈ amo l, c.eval v = true) ↔ ∀ x ∈ l, ∀ y ∈ l, v x = true → v y = true → x = y := by
  constructor
  · intro h x hx y hy hvx hvy
    by_contra hxy
    rcases Matching.pairs_complete hx hy hxy with hp | hp
    · have := h _ (List.mem_map.2 ⟨_, hp, rfl⟩)
      simp [CNF.Clause.eval, hvx, hvy] at this
    · have := h _ (List.mem_map.2 ⟨_, hp, rfl⟩)
      simp [CNF.Clause.eval, hvx, hvy] at this
  · intro h c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    rcases Matching.mem_pairs hp with ⟨h1, h2, h3⟩ | hnd
    · simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
        beq_iff_eq]
      by_contra hb
      simp only [not_or] at hb
      exact h3 (h _ h1 _ h2 (by simpa using hb.1) (by simpa using hb.2))
    · exact absurd hl hnd

theorem alo_eval (l : List ℕ) (v : ℕ → Bool) :
    CNF.Clause.eval v (l.map fun i => (i, true)) = true ↔ ∃ x ∈ l, v x = true := by
  simp [CNF.Clause.eval, List.any_map, Function.comp]

theorem cell_inj {r c r' c' : ℕ} (hc : c < n) (hc' : c' < n) (h : r * n + c = r' * n + c') :
    r = r' ∧ c = c' := by
  have hn : 0 < n := by omega
  have e1 : (r * n + c) / n = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc, Nat.zero_add]
  have e2 : (r' * n + c') / n = r' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc', Nat.zero_add]
  have hr : r = r' := by rw [← e1, ← e2, h]
  subst hr
  exact ⟨rfl, by omega⟩

theorem cell_lt {r c : ℕ} (hr : r < n) (hc : c < n) : r * n + c < n * n := by
  calc r * n + c < r * n + n := by omega
    _ = (r + 1) * n := by rw [Nat.succ_mul]
    _ ≤ n * n := Nat.mul_le_mul_right _ hr

theorem mem_rowCells {r x : ℕ} : x ∈ rowCells n r ↔ ∃ c < n, r * n + c = x := by
  simp [rowCells]

theorem mem_colCells {c x : ℕ} : x ∈ colCells n c ↔ ∃ r < n, r * n + c = x := by
  simp [colCells]

theorem mem_diagCells {k x : ℕ} :
    x ∈ diagCells n k ↔ ∃ r < n, (r ≤ k ∧ k < r + n) ∧ r * n + (r + (n - 1) - k) = x := by
  simp [diagCells, and_assoc]

theorem mem_antiCells {s x : ℕ} :
    x ∈ antiCells n s ↔ ∃ r < n, (r ≤ s ∧ s < r + n) ∧ r * n + (s - r) = x := by
  simp [antiCells, and_assoc]

theorem rowCells_nodup (r : ℕ) : (rowCells n r).Nodup :=
  List.nodup_range.map_on fun _ hc _ hc' h =>
    (cell_inj (List.mem_range.1 hc) (List.mem_range.1 hc') h).2

theorem colCells_nodup {c : ℕ} (hc : c < n) : (colCells n c).Nodup :=
  List.nodup_range.map_on fun _ _ _ _ h => (cell_inj hc hc h).1

theorem diagCells_nodup (k : ℕ) : (diagCells n k).Nodup :=
  (List.nodup_range.filter _).map_on fun r hr r' hr' h => by
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hr hr'
    exact (cell_inj (by omega) (by omega) h).1

theorem antiCells_nodup (s : ℕ) : (antiCells n s).Nodup :=
  (List.nodup_range.filter _).map_on fun r hr r' hr' h => by
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hr hr'
    exact (cell_inj (by omega) (by omega) h).1

/-- Semantics of the encoder: every row has a queen, and two queens on a common row, column,
    diagonal or anti-diagonal coincide. -/
theorem eval_iff (v : ℕ → Bool) :
    (cnf n).eval v = true ↔
      (∀ r < n, ∃ c < n, v (r * n + c) = true) ∧
      ∀ r c r' c', r < n → c < n → r' < n → c' < n → v (r * n + c) = true →
        v (r' * n + c') = true → (r = r' ∨ c = c' ∨ r + c' = r' + c ∨ r + c = r' + c') →
        r = r' ∧ c = c' := by
  have hcnf : (cnf n).eval v = true ↔ ∀ cl ∈ clauses n, cl.eval v = true := by
    unfold CNF.eval
    rw [Array.all_eq_true_iff_forall_mem]
    simp only [cnf, List.mem_toArray]
  rw [hcnf]
  constructor
  · intro H
    have hrow : ∀ r < n, ∀ x ∈ rowCells n r, ∀ y ∈ rowCells n r, v x = true → v y = true →
        x = y := fun r hr => (amo_eval (rowCells_nodup r) v).1 fun cl hcl => H cl (by
      simp only [clauses, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
      exact Or.inl (Or.inl (Or.inl ⟨r, hr, Or.inr hcl⟩)))
    have hcol : ∀ c < n, ∀ x ∈ colCells n c, ∀ y ∈ colCells n c, v x = true → v y = true →
        x = y := fun c hc => (amo_eval (colCells_nodup hc) v).1 fun cl hcl => H cl (by
      simp only [clauses, List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inl (Or.inr ⟨c, hc, hcl⟩)))
    have hdiag : ∀ k < 2 * n - 1, ∀ x ∈ diagCells n k, ∀ y ∈ diagCells n k, v x = true →
        v y = true → x = y := fun k hk => (amo_eval (diagCells_nodup k) v).1 fun cl hcl =>
      H cl (by
        simp only [clauses, List.mem_append, List.mem_flatMap, List.mem_range]
        exact Or.inl (Or.inr ⟨k, hk, hcl⟩))
    have hanti : ∀ s < 2 * n - 1, ∀ x ∈ antiCells n s, ∀ y ∈ antiCells n s, v x = true →
        v y = true → x = y := fun s hs => (amo_eval (antiCells_nodup s) v).1 fun cl hcl =>
      H cl (by
        simp only [clauses, List.mem_append, List.mem_flatMap, List.mem_range]
        exact Or.inr ⟨s, hs, hcl⟩)
    refine ⟨fun r hr => ?_, fun r c r' c' hr hc hr' hc' hv hv' hatt => ?_⟩
    · have := H _ (by
        simp only [clauses, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
        exact Or.inl (Or.inl (Or.inl ⟨r, hr, Or.inl rfl⟩)))
      obtain ⟨x, hx, hvx⟩ := (alo_eval _ v).1 this
      obtain ⟨c, hc, rfl⟩ := mem_rowCells.1 hx
      exact ⟨c, hc, hvx⟩
    · apply cell_inj hc hc'
      rcases hatt with rfl | rfl | hd | ha
      · exact hrow r hr _ (mem_rowCells.2 ⟨c, hc, rfl⟩) _ (mem_rowCells.2 ⟨c', hc', rfl⟩) hv hv'
      · exact hcol c hc _ (mem_colCells.2 ⟨r, hr, rfl⟩) _ (mem_colCells.2 ⟨r', hr', rfl⟩) hv hv'
      · refine hdiag (r + (n - 1) - c) (by omega) _
          (mem_diagCells.2 ⟨r, hr, by omega, by congr 1; omega⟩) _
          (mem_diagCells.2 ⟨r', hr', by omega, by congr 1; omega⟩) hv hv'
      · refine hanti (r + c) (by omega) _
          (mem_antiCells.2 ⟨r, hr, by omega, by congr 1; omega⟩) _
          (mem_antiCells.2 ⟨r', hr', by omega, by congr 1; omega⟩) hv hv'
  · rintro ⟨halo, hatt⟩ cl hcl
    -- two cells of one line: the attack condition identifies them
    have same : ∀ {r c r' c'}, r < n → c < n → r' < n → c' < n →
        (r = r' ∨ c = c' ∨ r + c' = r' + c ∨ r + c = r' + c') →
        v (r * n + c) = true → v (r' * n + c') = true → r * n + c = r' * n + c' :=
      fun hr hc hr' hc' ht hv hv' => by
        obtain ⟨rfl, rfl⟩ := hatt _ _ _ _ hr hc hr' hc' hv hv' ht
        rfl
    simp only [clauses, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons] at hcl
    rcases hcl with ((⟨r, hr, rfl | hcl⟩ | ⟨c, hc, hcl⟩) | ⟨k, hk, hcl⟩) | ⟨s, hs, hcl⟩
    · obtain ⟨c, hc, hv⟩ := halo r hr
      exact (alo_eval _ v).2 ⟨_, mem_rowCells.2 ⟨c, hc, rfl⟩, hv⟩
    · refine (amo_eval (rowCells_nodup r) v).2 (fun x hx y hy hvx hvy => ?_) cl hcl
      obtain ⟨c, hc, rfl⟩ := mem_rowCells.1 hx
      obtain ⟨c', hc', rfl⟩ := mem_rowCells.1 hy
      exact same hr hc hr hc' (Or.inl rfl) hvx hvy
    · refine (amo_eval (colCells_nodup hc) v).2 (fun x hx y hy hvx hvy => ?_) cl hcl
      obtain ⟨r, hr, rfl⟩ := mem_colCells.1 hx
      obtain ⟨r', hr', rfl⟩ := mem_colCells.1 hy
      exact same hr hc hr' hc (Or.inr (Or.inl rfl)) hvx hvy
    · refine (amo_eval (diagCells_nodup k) v).2 (fun x hx y hy hvx hvy => ?_) cl hcl
      obtain ⟨r, hr, hk1, rfl⟩ := mem_diagCells.1 hx
      obtain ⟨r', hr', hk2, rfl⟩ := mem_diagCells.1 hy
      exact same hr (by omega) hr' (by omega) (Or.inr (Or.inr (Or.inl (by omega)))) hvx hvy
    · refine (amo_eval (antiCells_nodup s) v).2 (fun x hx y hy hvx hvy => ?_) cl hcl
      obtain ⟨r, hr, hs1, rfl⟩ := mem_antiCells.1 hx
      obtain ⟨r', hr', hs2, rfl⟩ := mem_antiCells.1 hy
      exact same hr (by omega) hr' (by omega) (Or.inr (Or.inr (Or.inr (by omega)))) hvx hvy

/-! ## Models and placements -/

section
variable {a : Fin (n * n) → Bool} (ha : (cnf n).eval (ext a) = true)

/-- The column of the queen in row `r` of a model. -/
noncomputable def col (r : Fin n) : Fin n :=
  ⟨Classical.choose (((eval_iff _).1 ha).1 r r.2),
    (Classical.choose_spec (((eval_iff _).1 ha).1 r r.2)).1⟩

theorem col_spec (r : Fin n) : ext a (r * n + col ha r) = true :=
  (Classical.choose_spec (((eval_iff _).1 ha).1 r r.2)).2

theorem col_unique {r : Fin n} {c : ℕ} (hc : c < n) (h : ext a (r * n + c) = true) :
    c = col ha r :=
  (((eval_iff _).1 ha).2 r c r (col ha r) r.2 hc r.2 (col ha r).2 h (col_spec ha r)
    (Or.inl rfl)).2

theorem col_safe : Safe (col ha) := by
  intro i j hij
  have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have att := fun h => ((eval_iff _).1 ha).2 i (col ha i) j (col ha j) i.2 (col ha i).2 j.2
    (col ha j).2 (col_spec ha i) (col_spec ha j) h
  refine ⟨fun h => hne (att (Or.inr (Or.inl (congrArg Fin.val h)))).1,
    fun h => hne (att (Or.inr (Or.inr (Or.inl h)))).1,
    fun h => hne (att (Or.inr (Or.inr (Or.inr h)))).1⟩

end

/-- The model of a placement: cell `x = r * n + c` is true iff `f r = c`. -/
def toModel (f : Fin n → Fin n) (x : Fin (n * n)) : Bool :=
  decide ((f ⟨x / n, Nat.div_lt_of_lt_mul x.2⟩ : ℕ) = x % n)

theorem ext_toModel (f : Fin n → Fin n) {r c : ℕ} (hr : r < n) (hc : c < n) :
    ext (toModel f) (r * n + c) = decide ((f ⟨r, hr⟩ : ℕ) = c) := by
  have hn : 0 < n := by omega
  have e1 : (r * n + c) / n = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc, Nat.zero_add]
  have e2 : (r * n + c) % n = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  have hf : f ⟨(r * n + c) / n, Nat.div_lt_of_lt_mul (cell_lt hr hc)⟩ = f ⟨r, hr⟩ :=
    congrArg f (Fin.ext e1)
  simp only [ext, cell_lt hr hc, dite_true, toModel, e2, hf]

theorem toModel_model {f : Fin n → Fin n} (hf : Safe f) : (cnf n).eval (ext (toModel f)) = true := by
  rw [eval_iff]
  refine ⟨fun r hr => ⟨f ⟨r, hr⟩, (f ⟨r, hr⟩).2, by rw [ext_toModel f hr (f ⟨r, hr⟩).2]; simp⟩,
    fun r c r' c' hr hc hr' hc' hv hv' ht => ?_⟩
  rw [ext_toModel f hr hc, decide_eq_true_eq] at hv
  rw [ext_toModel f hr' hc', decide_eq_true_eq] at hv'
  by_cases hrr : r = r'
  · subst hrr; exact ⟨rfl, hv.symm.trans hv'⟩
  · exfalso
    obtain ⟨h1, h2, h3⟩ := hf ⟨r, hr⟩ ⟨r', hr'⟩ (fun h => hrr (congrArg Fin.val h))
    simp only at h2 h3
    rcases ht with h | h | h | h
    · exact hrr h
    · exact h1 (Fin.ext (hv.trans (h.trans hv'.symm)))
    · exact h2 (by rw [hv, hv']; exact h)
    · exact h3 (by rw [hv, hv']; exact h)

/-- Family lemma: models of the encoder are the non-attacking placements. -/
noncomputable def equiv :
    {a : Fin (n * n) → Bool // (cnf n).eval (ext a) = true} ≃ {f : Fin n → Fin n // Safe f} where
  toFun a := ⟨col a.2, col_safe a.2⟩
  invFun f := ⟨toModel f.1, toModel_model f.2⟩
  left_inv a := by
    obtain ⟨a, ha⟩ := a
    apply Subtype.ext
    funext x
    have hx : x.val = x / n * n + x % n := (Nat.div_add_mod' x n).symm
    have hr : x / n < n := Nat.div_lt_of_lt_mul x.2
    have hc : x % n < n := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hr)
    have key : ext (toModel (col ha)) (x / n * n + x % n) = ext a (x / n * n + x % n) := by
      rw [ext_toModel _ hr hc]
      cases hax : ext a (x / n * n + x % n)
      · rw [decide_eq_false_iff_not]
        intro h
        have := col_spec ha ⟨x / n, hr⟩
        rw [h, hax] at this
        exact Bool.false_ne_true this
      · rw [decide_eq_true_eq]
        exact (col_unique ha (r := ⟨x / n, hr⟩) hc hax).symm
    rw [← hx] at key
    simpa [ext, x.2] using key
  right_inv f := by
    obtain ⟨f, hf⟩ := f
    apply Subtype.ext
    funext r
    have h := ext_toModel f r.2 (f r).2
    simp only [decide_true] at h
    exact (Fin.ext (col_unique (toModel_model hf) (f r).2 h)).symm

/-- A certificate for the n-queens CNF counts the non-attacking placements. -/
theorem card_of_check {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (n * n) (cnf n) pogStr lratStr N = true) :
    Nat.card {f : Fin n → Fin n // Safe f} = N := by
  rw [← Nat.card_congr equiv, Nat.card_eq_fintype_card, checkAll_sound h]

/-- The same with part B as a separate (streamed) refutation, for large certificates. -/
theorem card_of_checkAC {pogStr : String} {N : ℕ}
    (h : checkAllAC (n * n) (cnf n) pogStr N = true) (hB : (fwdCnfOf (cnf n) pogStr).Unsat) :
    Nat.card {f : Fin n → Fin n // Safe f} = N := by
  rw [← Nat.card_congr equiv, Nat.card_eq_fintype_card, checkAllAC_sound h hB]

end CountCatcher.Queens
