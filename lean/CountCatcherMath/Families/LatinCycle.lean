import CountCatcherMath.Families.LatinAll

/-!
# Reduced Latin squares by the cycle type of the second row

Conjugation invariance (`card_fibre_eq_of_conj`). Relabel the columns and the symbols of a Latin
square at once by a permutation `σ`, `L' i j = σ (L i (σ⁻¹ j))`: the identity first row stays the
identity and a second row `r` becomes `σ r σ⁻¹`. So the squares with the identity first row and
second row `r` (column `0` free) are as many as those with second row `q` whenever
`q ∘ σ = σ ∘ r` (`twoRowsConj`). Normalising column `0` by a row permutation that fixes rows `0`
and `1` (as `normEquiv` does for all rows) splits that set into the permutations `β` with
`β 0 = 0`, `β 1 = 1` times the reduced squares with second row `r`, when `r 0 = 1`
(`twoRowsEquiv`). Hence the fibre counts of two admissible second rows agree when the rows are
conjugate as permutations: the fibre count depends only on the cycle type.

Assembly over classes (`card_eq_of_classes`): every admissible second row (the list `rows n`),
each with a permutation `σ` carrying it onto a representative whose fibre count is certified;
the side condition `classCheck` is a Boolean function on value lists, checked by `decide`.

Sub-split of a fibre (`fibre_card_eq_of_cells`): the fibre of `r` is the disjoint union over the
admissible values of the cells `(2, 1), …, (2, k)` of the third row (`thirdRows`, proved complete
like `rows`); each part is the fibre formula plus unit clauses (`cellCnf`).
-/

open Equiv Std.Sat

namespace CountCatcher.Latin

variable {n : ℕ}

section Conj
variable [NeZero n]

/-! ## Conjugation invariance -/

/-- Columns and symbols relabelled by `σ`: `L' i j = σ (L i (σ⁻¹ j))`. -/
def conjSq (σ : Perm (Fin n)) (L : Fin n → Fin n → Fin n) : Fin n → Fin n → Fin n :=
  fun i j => σ (L i (σ.symm j))

omit [NeZero n] in
theorem isLatin_conjSq (σ : Perm (Fin n)) {L : Fin n → Fin n → Fin n} (hL : IsLatin L) :
    IsLatin (conjSq σ L) :=
  ⟨fun i => σ.bijective.comp ((hL.1 i).comp σ.symm.bijective),
    fun j => σ.bijective.comp (hL.2 (σ.symm j))⟩

/-- Squares with the identity first row and second row `r` (column `0` free). -/
abbrev TwoRows (r : Fin n → Fin n) :=
  {L : Fin n → Fin n → Fin n // IsLatin L ∧ (∀ j, L 0 j = j) ∧ L 1 = r}

/-- Conjugation by `σ` maps the squares with second row `r` onto those with second row `q`,
    when `q ∘ σ = σ ∘ r`. -/
def twoRowsConj (σ : Perm (Fin n)) {r q : Fin n → Fin n} (h : ∀ j, q (σ j) = σ (r j)) :
    TwoRows r ≃ TwoRows q where
  toFun L := ⟨conjSq σ L.1, isLatin_conjSq σ L.2.1, fun j => by simp [conjSq, L.2.2.1],
    funext fun j => by
      simp only [conjSq, L.2.2.2]
      rw [← h, Equiv.apply_symm_apply]⟩
  invFun L := ⟨conjSq σ.symm L.1, isLatin_conjSq σ.symm L.2.1, fun j => by simp [conjSq, L.2.2.1],
    funext fun j => by
      simp only [conjSq, L.2.2.2, Equiv.symm_symm, h, Equiv.symm_apply_apply]⟩
  left_inv L := Subtype.ext (funext₂ fun i j => by simp [conjSq])
  right_inv L := Subtype.ext (funext₂ fun i j => by simp [conjSq])

/-- Column `0` of a square as a permutation. -/
noncomputable def col0 {r : Fin n → Fin n} (L : TwoRows r) : Perm (Fin n) :=
  Equiv.ofBijective (fun i => L.1 i 0) (L.2.1.2 0)

/-- Normalising column `0`: the squares with the identity first row and second row `r` are the
    permutations of the rows that fix `0` and `1`, times the reduced squares with second row
    `r` (`L i j = R (β i) j`), when `r 0 = 1`. -/
noncomputable def twoRowsEquiv {r : Fin n → Fin n} (hr : r 0 = 1) :
    TwoRows r ≃ {β : Perm (Fin n) // β 0 = 0 ∧ β 1 = 1} ×
      {R : Fin n → Fin n → Fin n // IsReducedLatin R ∧ R 1 = r} where
  toFun L :=
    have h0 : col0 L 0 = 0 := L.2.2.1 0
    have h1 : col0 L 1 = 1 := by
      show L.1 1 0 = 1
      rw [L.2.2.2, hr]
    (⟨col0 L, h0, h1⟩,
      ⟨fun i j => L.1 ((col0 L).symm i) j,
        ⟨isLatin_relabel L.2.1 _ (Equiv.refl _),
          fun j => by
            have : (col0 L).symm 0 = 0 := by rw [Equiv.symm_apply_eq]; exact h0.symm
            simp only [this]; exact L.2.2.1 j,
          fun i => (col0 L).apply_symm_apply i⟩,
        funext fun j => by
          have : (col0 L).symm 1 = 1 := by rw [Equiv.symm_apply_eq]; exact h1.symm
          simp only [this]; exact congrFun L.2.2.2 j⟩)
  invFun x := ⟨fun i j => x.2.1 (x.1.1 i) j, isLatin_relabel x.2.2.1.1 x.1.1 (Equiv.refl _),
    fun j => by simp only [x.1.2.1]; exact x.2.2.1.2.1 j,
    funext fun j => by simp only [x.1.2.2]; exact congrFun x.2.2.2 j⟩
  left_inv L := Subtype.ext (funext₂ fun i j => by
    simp only [Equiv.symm_apply_apply])
  right_inv x := by
    obtain ⟨⟨β, hβ0, hβ1⟩, ⟨R, hR, hR1⟩⟩ := x
    have hc : col0 (r := r) ⟨fun i j => R (β i) j, isLatin_relabel hR.1 β (Equiv.refl _),
        fun j => by simp only [hβ0]; exact hR.2.1 j,
        funext fun j => by simp only [hβ1]; exact congrFun hR1 j⟩ = β := by
      ext i
      simp only [col0, Equiv.ofBijective_apply]
      rw [hR.2.2]
    refine Prod.ext (Subtype.ext hc) (Subtype.ext ?_)
    funext i j
    simp only [hc, Equiv.apply_symm_apply]

/-- Fibres of conjugate second rows have the same size. -/
theorem card_fibre_eq_of_conj (σ : Perm (Fin n)) {r q : Fin n → Fin n} (hr : r 0 = 1)
    (hq : q 0 = 1) (h : ∀ j, q (σ j) = σ (r j)) :
    Nat.card {L : Fin n → Fin n → Fin n // IsReducedLatin L ∧ L 1 = r} =
      Nat.card {L : Fin n → Fin n → Fin n // IsReducedLatin L ∧ L 1 = q} := by
  have : Nonempty {β : Perm (Fin n) // β 0 = 0 ∧ β 1 = 1} := ⟨⟨1, rfl, rfl⟩⟩
  have hpos : 0 < Nat.card {β : Perm (Fin n) // β 0 = 0 ∧ β 1 = 1} := Nat.card_pos
  have e := Nat.card_congr ((twoRowsEquiv hr).symm.trans ((twoRowsConj σ h).trans (twoRowsEquiv hq)))
  rw [Nat.card_prod, Nat.card_prod] at e
  exact Nat.eq_of_mul_eq_mul_left hpos e

end Conj

/-! ## Assembly over classes of second rows -/

/-- The function of a list of values (entries taken mod `n`). -/
def ofList (n : ℕ) [NeZero n] (l : List ℕ) : Fin n → Fin n :=
  fun j => ⟨l.getD j 0 % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- `s` (a permutation of `0, …, n-1` as its list of values) carries the row `r` onto the row
    `q`, and `q` starts with `1`: `q (s j) = s (r j)` for every `j < n`. -/
def conjOk (n : ℕ) (s r q : List ℕ) : Bool :=
  s.length == n && s.all (· < n) && decide s.Nodup && q.getD 0 0 == 1 &&
    (List.range n).all fun j => q.getD (s.getD j 0) 0 == s.getD (r.getD j 0) 0

/-- Side condition of `card_eq_of_classes`: `A` lists the admissible second rows in the order of
    `rows n`, each with a permutation (values) carrying it onto the representative `reps[k]`. -/
def classCheck (n : ℕ) (reps : List (List ℕ)) (A : List (List ℕ × List ℕ × ℕ)) : Bool :=
  A.map Prod.fst == rows n && A.all fun a =>
    match reps[a.2.2]? with
    | some q => conjOk n a.2.1 a.1 q
    | none => false

theorem mem_seqs_lt {ok : ℕ → ℕ → Bool} : ∀ {k : ℕ} {l : List ℕ}, l ∈ seqs n ok k →
    l.length = k ∧ ∀ x ∈ l, x < n
  | 0, l, h => by simp [seqs] at h; simp [h]
  | k + 1, l, h => by
    simp only [seqs, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at h
    obtain ⟨l', hl', v, ⟨hv, -⟩, rfl⟩ := h
    obtain ⟨h1, h2⟩ := mem_seqs_lt hl'
    refine ⟨by simp [h1], fun x hx => ?_⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact h2 x hx
    · rw [List.mem_singleton.1 hx]; exact hv

theorem getD_of_lt {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

section Classes
variable [NeZero n]

theorem val_ofList {l : List ℕ} (hl : l.length = n) (hlt : ∀ x ∈ l, x < n) (j : Fin n) :
    (ofList n l j : ℕ) = l.getD j 0 := by
  have hj : (j : ℕ) < l.length := hl ▸ j.2
  simp only [ofList, getD_of_lt hj]
  exact Nat.mod_eq_of_lt (hlt _ (List.getElem_mem hj))

theorem rowList_ofList {l : List ℕ} (hl : l.length = n) (hlt : ∀ x ∈ l, x < n) :
    rowList (ofList n l) = l := by
  apply List.ext_getElem (by simp [rowList, hl])
  intro j h1 h2
  simp only [rowList, List.getElem_ofFn]
  rw [val_ofList hl hlt, getD_of_lt h2]

omit [NeZero n] in
theorem getD_rowList (f : Fin n → Fin n) (j : Fin n) : (rowList f).getD j 0 = f j := by
  rw [getD_of_lt (by simp [rowList])]
  simp [rowList]

/-- What `conjOk` checks: a permutation `σ` with `q ∘ σ = σ ∘ r`, and `q 0 = 1`. -/
theorem conjOk_sound (hn : 2 ≤ n) {s : List ℕ} {rf qf : Fin n → Fin n}
    (h : conjOk n s (rowList rf) (rowList qf) = true) :
    ∃ σ : Perm (Fin n), (∀ j, qf (σ j) = σ (rf j)) ∧ qf 0 = 1 := by
  simp only [conjOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hlen, hlt⟩, hnd⟩, hq0⟩, hall⟩ := h
  have hlt' : ∀ x ∈ s, x < n := fun x hx => by simpa using hlt x hx
  have hinj : Function.Injective (ofList n s) := by
    intro i j hij
    have := congrArg Fin.val hij
    rw [val_ofList hlen hlt', val_ofList hlen hlt',
      getD_of_lt (by rw [hlen]; exact i.2), getD_of_lt (by rw [hlen]; exact j.2)] at this
    exact Fin.ext ((hnd.getElem_inj_iff).1 this)
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj), fun j => ?_, ?_⟩
  · have hj := hall j j.2
    simp only [Equiv.ofBijective_apply]
    apply Fin.ext
    rw [getD_rowList rf j, ← val_ofList hlen hlt' (rf j), ← val_ofList hlen hlt' j,
      getD_rowList qf] at hj
    exact hj
  · apply Fin.ext
    rw [val_one hn]
    have := getD_rowList qf 0
    rw [Fin.val_zero] at this
    rw [← this]; exact hq0

/-- Assembly: the reduced Latin squares of order `n` from one certified fibre count per class of
    second rows. `R` lists the representatives with their counts; `A` lists every admissible
    second row (as in `rows n`) with a permutation carrying it onto its representative `R[k]`
    (`classCheck`, by `decide`). -/
theorem card_eq_of_classes (hn : 2 ≤ n) (N : ℕ) (R : List ((Fin n → Fin n) × ℕ))
    (hR : ∀ p ∈ R, Nat.card {L : Fin n → Fin n → Fin n // IsReducedLatin L ∧ L 1 = p.1} = p.2)
    (A : List (List ℕ × List ℕ × ℕ))
    (hc : classCheck n (R.map fun p => rowList p.1) A = true)
    (hN : (A.map fun a => (R.map Prod.snd).getD a.2.2 0).sum = N) :
    Nat.card {L : Fin n → Fin n → Fin n // IsReducedLatin L} = N := by
  simp only [classCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨hrows, hall⟩ := hc
  have hmem : ∀ a ∈ A, a.1 ∈ rows n := fun a ha => hrows ▸ List.mem_map_of_mem ha
  have hrf : ∀ a ∈ A, rowList (ofList n a.1) = a.1 := fun a ha =>
    have h := mem_seqs_lt (hmem a ha)
    rowList_ofList h.1 h.2
  refine card_eq_of_rows hn N (A.map fun a => (ofList n a.1, (R.map Prod.snd).getD a.2.2 0))
    ?_ ?_ ?_
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
    have hr0 : ofList n a.1 0 = 1 := by
      have h := (mem_admRows_iff hn _).2 ((hrf a ha).symm ▸ hmem a ha)
      simp only [admRows, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h.2.1
    have hk := hall a ha
    split at hk
    · rename_i q hq
      rw [List.getElem?_map] at hq
      obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.1 hq
      rw [← hrf a ha] at hk
      obtain ⟨σ, hσ, hq0⟩ := conjOk_sound hn hk
      simp only
      rw [card_fibre_eq_of_conj σ hr0 hq0 hσ, hR p' (List.mem_of_getElem? hp'),
        List.getD_eq_getElem?_getD, List.getElem?_map, hp']
      rfl
    · simp at hk
  · rw [List.map_map, ← hrows]
    exact List.map_congr_left fun a ha => hrf a ha
  · rw [List.map_map]
    exact hN

end Classes

/-! ## Sub-split of a fibre by the cells `(2, 1), …, (2, k)` of the third row -/

/-- Admissible value `v` of the cell `(2, c + 1)`, given the second row `r` (values): not `c + 1`
    (row `0` in that column), not `r (c + 1)` (row `1`), not `2` (column `0` of row `2`). -/
def cellOk (r : List ℕ) (c v : ℕ) : Bool := v != c + 1 && v != r.getD (c + 1) 0 && v != 2

/-- The admissible values of the cells `(2, 1), …, (2, k)` (distinct; lexicographic order). -/
def thirdRows (n : ℕ) (r : List ℕ) (k : ℕ) : List (List ℕ) := seqs n (cellOk r) k

/-- Unit literals fixing the cells `(2, 1), …, (2, |t|)` to the values `t`. -/
def cellLits (n : ℕ) (t : List ℕ) : List (ℕ × Bool) :=
  (List.range t.length).map fun c => (var n 2 (c + 1) (t.getD c 0), true)

/-- The part of the fibre of `r` whose cells `(2, 1), …, (2, |t|)` hold `t`. -/
def cellCnf (n : ℕ) [NeZero n] (r : Fin n → Fin n) (t : List ℕ) : CNF ℕ :=
  cube (fibreCnf n r) (cellLits n t)

section Cells
variable [NeZero n]

/-- The cells `(2, 1), …, (2, k)` of a square, as values. -/
def thirdPre (hn : 3 ≤ n) (k : ℕ) (hk : k < n) (L : Fin n → Fin n → Fin n) : List ℕ :=
  List.ofFn fun c : Fin k => (L ⟨2, by omega⟩ ⟨c + 1, by omega⟩ : ℕ)

theorem cell_eval (r : Fin n → Fin n) (t : List ℕ) (v : ℕ → Bool) :
    (cellCnf n r t).eval v = true ↔
      (fibreCnf n r).eval v = true ∧ ∀ c < t.length, v (var n 2 (c + 1) (t.getD c 0)) = true := by
  simp [cellCnf, eval_cube, cellLits, List.all_map]

/-- Family lemma of a part: its models are the reduced squares with second row `r` and the cells
    `(2, 1), …, (2, k)` equal to `t`. -/
noncomputable def cellEquiv (hn : 3 ≤ n) {k : ℕ} (hk : k < n) (r : Fin n → Fin n) {t : List ℕ}
    (ht : t.length = k) (hlt : ∀ x ∈ t, x < n) :
    {a : Fin (n * n * n) → Bool // (cellCnf n r t).eval (ext a) = true} ≃
      {L : Fin n → Fin n → Fin n // (IsReducedLatin L ∧ L 1 = r) ∧ thirdPre hn k hk L = t} where
  toFun a :=
    have ha := (cell_eval r t _).1 a.2
    have hf := (fibre_eval r _).1 ha.1
    ⟨sq hf.1, ⟨sq_reduced hf.1, funext fun j => (sq_eq_iff hf.1).2 (hf.2 j)⟩, by
      apply List.ext_getElem (by simp [thirdPre, ht])
      intro c h1 h2
      simp only [thirdPre, List.getElem_ofFn]
      have hc : c < k := by simpa [thirdPre] using h1
      have hv := ha.2 c (ht ▸ hc)
      rw [getD_of_lt h2] at hv
      have := (sq_eq_iff hf.1 (i := ⟨2, by omega⟩) (j := ⟨c + 1, by omega⟩)
        (s := ⟨t[c], hlt _ (List.getElem_mem h2)⟩)).2 hv
      rw [this]⟩
  invFun L := ⟨toModel L.1, (cell_eval r t _).2 ⟨(fibre_eval r _).2 ⟨toModel_model L.2.1.1,
    fun j => by rw [ext_toModel, L.2.1.2]; simp⟩, fun c hc => by
      have hc' : c < k := ht ▸ hc
      have h := congrArg (·[c]?) L.2.2
      simp only [thirdPre, List.getElem?_ofFn, hc', dite_true,
        List.getElem?_eq_getElem hc, Option.some.injEq] at h
      have := ext_toModel L.1 ⟨2, by omega⟩ ⟨c + 1, by omega⟩ ⟨t[c], hlt _ (List.getElem_mem hc)⟩
      simp only at this
      rw [getD_of_lt hc, this, decide_eq_true_eq]
      exact Fin.ext h⟩⟩
  left_inv a := Subtype.ext (toModel_sq ((fibre_eval r _).1 ((cell_eval r t _).1 a.2).1).1)
  right_inv L := Subtype.ext (sq_toModel L.2.1.1)

/-- Every reduced square with second row `r` has admissible values in the cells
    `(2, 1), …, (2, k)`. -/
theorem thirdPre_mem (hn : 3 ≤ n) {k : ℕ} (hk : k < n) {r : Fin n → Fin n}
    {L : Fin n → Fin n → Fin n} (hL : IsReducedLatin L ∧ L 1 = r) :
    thirdPre hn k hk L ∈ thirdRows n (rowList r) k := by
  obtain ⟨⟨⟨hrow, hcol⟩, h0, h0'⟩, hr⟩ := hL
  have h01 : (⟨0, by omega⟩ : Fin n) = 0 := rfl
  rw [thirdRows, thirdPre, ofFn_mem_seqs]
  refine ⟨fun c c' h => ?_, fun c => ⟨Fin.is_lt _, ?_⟩⟩
  · have := (hrow ⟨2, by omega⟩).1 (Fin.ext h)
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · simp only [cellOk, Bool.and_eq_true, bne_iff_ne, ne_eq]
    have hc1 : (c : ℕ) + 1 < n := by omega
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
    · -- column `c + 1` holds `c + 1` in row `0`
      have e : L ⟨2, by omega⟩ ⟨c + 1, hc1⟩ = L 0 ⟨c + 1, hc1⟩ := by
        rw [h0]; exact Fin.ext h
      have := congrArg Fin.val ((hcol ⟨c + 1, hc1⟩).1 e)
      simp at this
    · -- column `c + 1` holds `r (c + 1)` in row `1`
      rw [getD_rowList r ⟨c + 1, hc1⟩] at h
      have e : L ⟨2, by omega⟩ ⟨c + 1, hc1⟩ = L 1 ⟨c + 1, hc1⟩ := by
        rw [hr]; exact Fin.ext h
      have := congrArg Fin.val ((hcol ⟨c + 1, hc1⟩).1 e)
      rw [val_one (by omega)] at this
      simp at this
    · -- row `2` holds `2` in column `0`
      have e : L ⟨2, by omega⟩ ⟨c + 1, hc1⟩ = L ⟨2, by omega⟩ 0 := by
        rw [h0']; exact Fin.ext h
      have := congrArg Fin.val ((hrow ⟨2, by omega⟩).1 e)
      simp at this

/-- The fibre of `r` from one certified count per admissible filling of the cells
    `(2, 1), …, (2, k)` (listed as in `thirdRows`, a `decide` side condition). -/
theorem fibre_card_eq_of_cells (hn : 3 ≤ n) (r : Fin n → Fin n) (k : ℕ) (hk : k < n) (N : ℕ)
    (T : List (List ℕ × ℕ))
    (hT : ∀ p ∈ T,
      Fintype.card {a : Fin (n * n * n) → Bool // (cellCnf n r p.1).eval (ext a) = true} = p.2)
    (hlist : T.map Prod.fst = thirdRows n (rowList r) k) (hN : (T.map Prod.snd).sum = N) :
    Nat.card {L : Fin n → Fin n → Fin n // IsReducedLatin L ∧ L 1 = r} = N := by
  classical
  have hnd : (T.map Prod.fst).Nodup := hlist ▸ seqs_nodup _ k
  rw [card_eq_sum_fibres (fun L : Fin n → Fin n → Fin n => IsReducedLatin L ∧ L 1 = r)
    (thirdPre hn k hk) (T.map Prod.fst).toFinset fun L hL => by
      rw [List.mem_toFinset, hlist]; exact thirdPre_mem hn hk hL,
    List.sum_toFinset _ hnd, ← hN, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  have hmem : p.1 ∈ thirdRows n (rowList r) k := hlist ▸ List.mem_map_of_mem hp
  obtain ⟨hlen, hlt⟩ := mem_seqs_lt hmem
  simp only [Function.comp_apply]
  rw [← Nat.card_congr (cellEquiv hn hk r hlen hlt), Nat.card_eq_fintype_card, hT p hp]

/-- `count_models` lemmas for a part (the theorem states the model count of `cellCnf`). -/
theorem cell_card_of_check {r : Fin n → Fin n} {t : List ℕ} {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (n * n * n) (cellCnf n r t) pogStr lratStr N = true) :
    Fintype.card {a : Fin (n * n * n) → Bool // (cellCnf n r t).eval (ext a) = true} = N :=
  checkAll_sound h

theorem cell_card_of_checkAC {r : Fin n → Fin n} {t : List ℕ} {pogStr : String} {N : ℕ}
    (h : checkAllAC (n * n * n) (cellCnf n r t) pogStr N = true)
    (hB : (fwdCnfOf (cellCnf n r t) pogStr).Unsat) :
    Fintype.card {a : Fin (n * n * n) → Bool // (cellCnf n r t).eval (ext a) = true} = N :=
  checkAllAC_sound h hB

theorem cell_card_of_unsat {r : Fin n → Fin n} {t : List ℕ} (h : (cellCnf n r t).Unsat) :
    Fintype.card {a : Fin (n * n * n) → Bool // (cellCnf n r t).eval (ext a) = true} = 0 :=
  card_eq_zero_of_unsat h

end Cells

end CountCatcher.Latin
