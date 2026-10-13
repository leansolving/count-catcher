import CountCatcherMath.Family
import CountCatcherMath.Split
import CountCatcherMath.Families.Queens

/-!
# Family: reduced Latin squares, split by the second row

Definitions (Mathlib only, independent of the encoding): `IsLatin L` for
`L : Fin n → Fin n → Fin n` says that every row `L i` and every column `fun i => L i j` is a
bijection; `IsReducedLatin L` adds that the first row and the first column are the identity.

Encoder `cnf n` (clause order of `scripts/showcase/gen_latin.py n --reduced`): variable
`var n i j s = (i * n + j) * n + s` says that cell `(i, j)` holds symbol `s`. Exactly one symbol
per cell, then for every symbol `s` exactly one cell per row and exactly one per column (one
at-least-one clause and the pairwise at-most-one clauses each), then unit clauses for the first
row (`var n 0 j j`) and the first column (`var n i 0 i`, `i ≠ 0`). No auxiliary variables.
Family lemma `equiv`: the models are the reduced Latin squares.

Fibres: `fibreCnf n r = cube (cnf n) (rowLits n r)` adds one unit clause per cell of row `1`;
`fibreEquiv r` identifies its models with `{L // IsReducedLatin L ∧ L 1 = r}`.

Decomposition: `card_eq_sum_admRows` sums the fibres over the admissible second rows
`admRows n` (bijections `r` with `r 0 = 1` and `r j ≠ j`, `row1_mem`). The list `rows n`
enumerates them (`mem_admRows_iff`, `seqs_nodup`; an enumeration with pruning, 309 lists for
`n = 7`), so `card_eq_of_rows` turns one certified count per listed row into the total; the
side condition that the listed rows are `rows n` is checked by `decide` in the kernel.
-/

open Std.Sat

namespace CountCatcher.Latin

/-! ## Latin squares -/

/-- Every row `L i` and every column `fun i => L i j` is a bijection. -/
def IsLatin {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ i, Function.Bijective (L i)) ∧ ∀ j, Function.Bijective fun i => L i j

/-- A Latin square whose first row and first column are the identity. -/
def IsReducedLatin {n : ℕ} [NeZero n] (L : Fin n → Fin n → Fin n) : Prop :=
  IsLatin L ∧ (∀ j, L 0 j = j) ∧ ∀ i, L i 0 = i

/-! ## Encoder -/

/-- The variable "cell `(i, j)` holds symbol `s`". -/
def var (n i j s : ℕ) : ℕ := (i * n + j) * n + s

/-- Exactly one of `l`: one at-least-one clause, then the pairwise at-most-one clauses. -/
def eo (l : List ℕ) : List (CNF.Clause ℕ) := (l.map fun x => (x, true)) :: Queens.amo l

def clauses (n : ℕ) : List (CNF.Clause ℕ) :=
  (List.finRange n).flatMap (fun i : Fin n => (List.finRange n).flatMap fun j : Fin n =>
    eo ((List.finRange n).map fun s : Fin n => var n i j s)) ++
  (List.finRange n).flatMap (fun s : Fin n =>
    (List.finRange n).flatMap (fun i : Fin n =>
      eo ((List.finRange n).map fun j : Fin n => var n i j s)) ++
    (List.finRange n).flatMap (fun j : Fin n =>
      eo ((List.finRange n).map fun i : Fin n => var n i j s))) ++
  (List.finRange n).map (fun j : Fin n => [(var n 0 j j, true)]) ++
  ((List.finRange n).filter fun i : Fin n => (i : ℕ) != 0).map
    fun i : Fin n => [(var n i 0 i, true)]

/-- The CNF whose models are the reduced Latin squares of order `n`. -/
def cnf (n : ℕ) : CNF ℕ := ⟨(clauses n).toArray⟩

/-- Unit literals fixing row `1` to `r`. -/
def rowLits (n : ℕ) [NeZero n] (r : Fin n → Fin n) : List (ℕ × Bool) :=
  (List.finRange n).map fun j : Fin n => (var n (1 : Fin n) j (r j), true)

/-- The fibre of the second row `r`: the encoder plus one unit clause per cell of row `1`. -/
def fibreCnf (n : ℕ) [NeZero n] (r : Fin n → Fin n) : CNF ℕ := cube (cnf n) (rowLits n r)

variable {n : ℕ}

/-! ## Clause semantics -/

theorem eo_eval {l : List ℕ} (hl : l.Nodup) (v : ℕ → Bool) :
    (∀ c ∈ eo l, c.eval v = true) ↔
      (∃ x ∈ l, v x = true) ∧ ∀ x ∈ l, ∀ y ∈ l, v x = true → v y = true → x = y := by
  simp only [eo, List.forall_mem_cons]
  rw [Queens.alo_eval, Queens.amo_eval hl]

theorem eo_fin_eval {f : Fin n → ℕ} (hf : Function.Injective f) (v : ℕ → Bool) :
    (∀ c ∈ eo ((List.finRange n).map f), c.eval v = true) ↔
      (∃ s, v (f s) = true) ∧ ∀ s s', v (f s) = true → v (f s') = true → s = s' := by
  rw [eo_eval ((List.nodup_finRange n).map hf)]
  simp only [List.mem_map, List.mem_finRange, true_and, exists_exists_eq_and,
    forall_exists_index, forall_apply_eq_imp_iff]
  exact and_congr Iff.rfl (forall₂_congr fun s s' => imp_congr_right fun _ =>
    imp_congr_right fun _ => hf.eq_iff)

theorem var_inj {i j s i' j' s' : ℕ} (hj : j < n) (hs : s < n) (hj' : j' < n) (hs' : s' < n)
    (h : var n i j s = var n i' j' s') : i = i' ∧ j = j' ∧ s = s' := by
  obtain ⟨h1, rfl⟩ := Queens.cell_inj hs hs' h
  obtain ⟨rfl, rfl⟩ := Queens.cell_inj hj hj' h1
  exact ⟨rfl, rfl, rfl⟩

theorem var_lt {i j s : ℕ} (hi : i < n) (hj : j < n) (hs : s < n) : var n i j s < n * n * n := by
  have h1 : i * n + j < n * n := Queens.cell_lt hi hj
  calc (i * n + j) * n + s < (i * n + j) * n + n := by omega
    _ = (i * n + j + 1) * n := by ring
    _ ≤ n * n * n := Nat.mul_le_mul_right _ h1

theorem eo_cell (v : ℕ → Bool) (i j : Fin n) :
    (∀ c ∈ eo ((List.finRange n).map fun s : Fin n => var n i j s), c.eval v = true) ↔
      (∃ s : Fin n, v (var n i j s) = true) ∧
        ∀ s s' : Fin n, v (var n i j s) = true → v (var n i j s') = true → s = s' :=
  eo_fin_eval (fun s s' h => Fin.ext (var_inj j.2 s.2 j.2 s'.2 h).2.2) v

theorem eo_row (v : ℕ → Bool) (s i : Fin n) :
    (∀ c ∈ eo ((List.finRange n).map fun j : Fin n => var n i j s), c.eval v = true) ↔
      (∃ j : Fin n, v (var n i j s) = true) ∧
        ∀ j j' : Fin n, v (var n i j s) = true → v (var n i j' s) = true → j = j' :=
  eo_fin_eval (fun j j' h => Fin.ext (var_inj j.2 s.2 j'.2 s.2 h).2.1) v

theorem eo_col (v : ℕ → Bool) (s j : Fin n) :
    (∀ c ∈ eo ((List.finRange n).map fun i : Fin n => var n i j s), c.eval v = true) ↔
      (∃ i : Fin n, v (var n i j s) = true) ∧
        ∀ i i' : Fin n, v (var n i j s) = true → v (var n i' j s) = true → i = i' :=
  eo_fin_eval (fun _ _ h => Fin.ext (var_inj j.2 s.2 j.2 s.2 h).1) v

/-- Semantics of the encoder: exactly one symbol per cell, every symbol exactly once per row and
    per column, and the units of the first row and column. -/
theorem eval_iff (v : ℕ → Bool) :
    (cnf n).eval v = true ↔
      (∀ i j : Fin n, (∃ s : Fin n, v (var n i j s) = true) ∧
        ∀ s s' : Fin n, v (var n i j s) = true → v (var n i j s') = true → s = s') ∧
      (∀ s i : Fin n, (∃ j : Fin n, v (var n i j s) = true) ∧
        ∀ j j' : Fin n, v (var n i j s) = true → v (var n i j' s) = true → j = j') ∧
      (∀ s j : Fin n, (∃ i : Fin n, v (var n i j s) = true) ∧
        ∀ i i' : Fin n, v (var n i j s) = true → v (var n i' j s) = true → i = i') ∧
      (∀ j : Fin n, v (var n 0 j j) = true) ∧
      ∀ i : Fin n, (i : ℕ) ≠ 0 → v (var n i 0 i) = true := by
  have hcnf : (cnf n).eval v = true ↔ ∀ cl ∈ clauses n, cl.eval v = true := by
    unfold CNF.eval
    rw [Array.all_eq_true_iff_forall_mem]
    simp only [cnf, List.mem_toArray]
  rw [hcnf]
  simp only [clauses, List.forall_mem_append, List.forall_mem_flatMap, List.mem_finRange,
    forall_const, List.forall_mem_map, List.forall_mem_filter, bne_iff_ne, ne_eq, eo_cell,
    eo_row, eo_col, forall_and, and_assoc]
  simp [CNF.Clause.eval]

/-! ## Models and squares -/

section Model
variable [NeZero n]

theorem var_div {i j s : ℕ} (hs : s < n) : var n i j s / n = i * n + j := by
  unfold var
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (NeZero.pos n), Nat.div_eq_of_lt hs, Nat.zero_add]

omit [NeZero n] in
theorem var_mod {i j s : ℕ} (hs : s < n) : var n i j s % n = s := by
  unfold var
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]

theorem cell_div {i j : ℕ} (hj : j < n) : (i * n + j) / n = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (NeZero.pos n), Nat.div_eq_of_lt hj, Nat.zero_add]

omit [NeZero n] in
theorem cell_mod {i j : ℕ} (hj : j < n) : (i * n + j) % n = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

omit [NeZero n] in
theorem div_div_lt (x : Fin (n * n * n)) : (x : ℕ) / n / n < n :=
  Nat.div_lt_of_lt_mul (Nat.div_lt_of_lt_mul (by rw [← Nat.mul_assoc]; exact x.2))

/-- Every variable of the universe is `var n i j s` for cells and symbols of the square. -/
theorem exists_var (x : Fin (n * n * n)) : ∃ i j s : Fin n, var n i j s = x :=
  ⟨⟨x / n / n, div_div_lt x⟩, ⟨x / n % n, Nat.mod_lt _ (NeZero.pos n)⟩,
    ⟨x % n, Nat.mod_lt _ (NeZero.pos n)⟩, by simp only [var, Nat.div_add_mod']⟩

theorem eq_of_ext_var {a b : Fin (n * n * n) → Bool}
    (h : ∀ i j s : Fin n, ext a (var n i j s) = ext b (var n i j s)) : a = b := by
  funext x
  obtain ⟨i, j, s, hx⟩ := exists_var x
  have := h i j s
  rw [hx] at this
  simpa [ext, x.2] using this

section
variable {a : Fin (n * n * n) → Bool} (ha : (cnf n).eval (ext a) = true)
include ha

/-- The symbol in cell `(i, j)` of a model. -/
noncomputable def sq (i j : Fin n) : Fin n :=
  Classical.choose (((eval_iff _).1 ha).1 i j).1

omit [NeZero n] in
theorem sq_spec (i j : Fin n) : ext a (var n i j (sq ha i j)) = true :=
  Classical.choose_spec (((eval_iff _).1 ha).1 i j).1

omit [NeZero n] in
theorem sq_eq_iff {i j s : Fin n} : sq ha i j = s ↔ ext a (var n i j s) = true :=
  ⟨fun h => h ▸ sq_spec ha i j, fun h => (((eval_iff _).1 ha).1 i j).2 _ _ (sq_spec ha i j) h⟩

theorem sq_reduced : IsReducedLatin (sq ha) := by
  obtain ⟨-, hrow, hcol, hu1, hu2⟩ := (eval_iff _).1 ha
  refine ⟨⟨fun i => Finite.injective_iff_bijective.1 fun j j' h => ?_,
    fun j => Finite.injective_iff_bijective.1 fun i i' h => ?_⟩, fun j => ?_, fun i => ?_⟩
  · have h2 := sq_spec ha i j'
    rw [← h] at h2
    exact (hrow (sq ha i j) i).2 j j' (sq_spec ha i j) h2
  · have h2 := sq_spec ha i' j
    simp only at h
    rw [← h] at h2
    exact (hcol (sq ha i j) j).2 i i' (sq_spec ha i j) h2
  · exact (sq_eq_iff ha).2 (by simpa using hu1 j)
  · by_cases hi : (i : ℕ) = 0
    · have h0 : i = 0 := Fin.ext (by simpa using hi)
      subst h0
      exact (sq_eq_iff ha).2 (by simpa using hu1 0)
    · exact (sq_eq_iff ha).2 (by simpa using hu2 i hi)

end

/-- The model of a square: `var n i j s` is true iff `L i j = s`. -/
def toModel (L : Fin n → Fin n → Fin n) (x : Fin (n * n * n)) : Bool :=
  decide (L ⟨x / n / n, div_div_lt x⟩ ⟨x / n % n, Nat.mod_lt _ (NeZero.pos n)⟩ =
    ⟨x % n, Nat.mod_lt _ (NeZero.pos n)⟩)

theorem ext_toModel (L : Fin n → Fin n → Fin n) (i j s : Fin n) :
    ext (toModel L) (var n i j s) = decide (L i j = s) := by
  have h := var_lt i.2 j.2 s.2
  have e1 : var n i j s / n / n = i := by rw [var_div s.2, cell_div j.2]
  have e2 : var n i j s / n % n = j := by rw [var_div s.2, cell_mod j.2]
  have e3 : var n i j s % n = s := var_mod s.2
  simp only [ext, h, dite_true, toModel, e1, e2, e3, Fin.eta]

theorem toModel_model {L : Fin n → Fin n → Fin n} (hL : IsReducedLatin L) :
    (cnf n).eval (ext (toModel L)) = true := by
  obtain ⟨⟨hrow, hcol⟩, h0, h0'⟩ := hL
  rw [eval_iff]
  refine ⟨fun i j => ⟨⟨L i j, ?_⟩, fun s s' hs hs' => ?_⟩, fun s i => ⟨?_, fun j j' hj hj' => ?_⟩,
    fun s j => ⟨?_, fun i i' hi hi' => ?_⟩, fun j => ?_, fun i _ => ?_⟩
  · simp [ext_toModel]
  · simp only [ext_toModel, decide_eq_true_eq] at hs hs'
    rw [← hs, ← hs']
  · obtain ⟨j, hj⟩ := (hrow i).2 s
    exact ⟨j, by simp [ext_toModel, hj]⟩
  · simp only [ext_toModel, decide_eq_true_eq] at hj hj'
    exact (hrow i).1 (hj.trans hj'.symm)
  · obtain ⟨i, hi⟩ := (hcol j).2 s
    exact ⟨i, by simp [ext_toModel, hi]⟩
  · simp only [ext_toModel, decide_eq_true_eq] at hi hi'
    exact (hcol j).1 (hi.trans hi'.symm)
  · have := ext_toModel L 0 j j
    simp only [Fin.val_zero, h0 j, decide_true] at this
    exact this
  · have := ext_toModel L i 0 i
    simp only [Fin.val_zero, h0' i, decide_true] at this
    exact this

theorem toModel_sq {a : Fin (n * n * n) → Bool} (ha : (cnf n).eval (ext a) = true) :
    toModel (sq ha) = a :=
  eq_of_ext_var fun i j s => by
    rw [ext_toModel, Bool.eq_iff_iff, decide_eq_true_iff, sq_eq_iff ha]

theorem sq_toModel {L : Fin n → Fin n → Fin n} (hL : IsReducedLatin L) :
    sq (toModel_model hL) = L :=
  funext₂ fun i j => (sq_eq_iff _).2 (by simp [ext_toModel])

/-- Family lemma: the models of the encoder are the reduced Latin squares. -/
noncomputable def equiv :
    {a : Fin (n * n * n) → Bool // (cnf n).eval (ext a) = true} ≃
      {L : Fin n → Fin n → Fin n // IsReducedLatin L} where
  toFun a := ⟨sq a.2, sq_reduced a.2⟩
  invFun L := ⟨toModel L.1, toModel_model L.2⟩
  left_inv a := Subtype.ext (toModel_sq a.2)
  right_inv L := Subtype.ext (sq_toModel L.2)

theorem fibre_eval (r : Fin n → Fin n) (v : ℕ → Bool) :
    (fibreCnf n r).eval v = true ↔
      (cnf n).eval v = true ∧ ∀ j : Fin n, v (var n (1 : Fin n) j (r j)) = true := by
  simp [fibreCnf, eval_cube, rowLits, List.all_map]

/-- Family lemma for a fibre: the models are the reduced Latin squares with second row `r`. -/
noncomputable def fibreEquiv (r : Fin n → Fin n) :
    {a : Fin (n * n * n) → Bool // (fibreCnf n r).eval (ext a) = true} ≃
      {L : Fin n → Fin n → Fin n // IsReducedLatin L ∧ L 1 = r} where
  toFun a :=
    have ha := (fibre_eval r _).1 a.2
    ⟨sq ha.1, sq_reduced ha.1, funext fun j => (sq_eq_iff ha.1).2 (ha.2 j)⟩
  invFun L := ⟨toModel L.1, (fibre_eval r _).2 ⟨toModel_model L.2.1, fun j => by
    rw [ext_toModel, L.2.2]; simp⟩⟩
  left_inv a := Subtype.ext (toModel_sq ((fibre_eval r _).1 a.2).1)
  right_inv L := Subtype.ext (sq_toModel L.2.1)

end Model

/-! ## `count_models` lemmas -/

section Lemmas
variable [NeZero n]

/-- A certificate for the encoder counts the reduced Latin squares. -/
theorem card_of_check {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (n * n * n) (cnf n) pogStr lratStr N = true) :
    Nat.card {L : Fin n → Fin n → Fin n // IsReducedLatin L} = N :=
  Family.card_of_check equiv h

theorem card_of_checkAC {pogStr : String} {N : ℕ}
    (h : checkAllAC (n * n * n) (cnf n) pogStr N = true)
    (hB : (fwdCnfOf (cnf n) pogStr).Unsat) :
    Nat.card {L : Fin n → Fin n → Fin n // IsReducedLatin L} = N :=
  Family.card_of_checkAC equiv h hB

/-- A certificate for the fibre of `r` counts the reduced Latin squares with second row `r`. -/
theorem fibre_card_of_check {r : Fin n → Fin n} {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (n * n * n) (fibreCnf n r) pogStr lratStr N = true) :
    Nat.card {L : Fin n → Fin n → Fin n // IsReducedLatin L ∧ L 1 = r} = N :=
  Family.card_of_check (fibreEquiv r) h

theorem fibre_card_of_checkAC {r : Fin n → Fin n} {pogStr : String} {N : ℕ}
    (h : checkAllAC (n * n * n) (fibreCnf n r) pogStr N = true)
    (hB : (fwdCnfOf (fibreCnf n r) pogStr).Unsat) :
    Nat.card {L : Fin n → Fin n → Fin n // IsReducedLatin L ∧ L 1 = r} = N :=
  Family.card_of_checkAC (fibreEquiv r) h hB

theorem fibre_card_of_unsat {r : Fin n → Fin n} (h : (fibreCnf n r).Unsat) :
    Nat.card {L : Fin n → Fin n → Fin n // IsReducedLatin L ∧ L 1 = r} = 0 :=
  Family.card_of_unsat (fibreEquiv r) h

end Lemmas

/-! ## Decomposition by the second row -/

/-- Counting by the fibres of `f`, over a finite set `S` that contains `f x` for every `x` with
    `P x`. -/
theorem card_eq_sum_fibres {α β : Type*} [Fintype α] (P : α → Prop) (f : α → β) (S : Finset β)
    (hS : ∀ x, P x → f x ∈ S) :
    Nat.card {x // P x} = ∑ b ∈ S, Nat.card {x // P x ∧ f x = b} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := S)
    fun x hx => hS x (Finset.mem_filter.1 hx).2]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.filter_filter]

open Classical in
/-- The admissible second rows: bijections `r` with `r 0 = 1` and no fixed point. -/
noncomputable def admRows (n : ℕ) [NeZero n] : Finset (Fin n → Fin n) :=
  Finset.univ.filter fun r => Function.Bijective r ∧ r 0 = 1 ∧ ∀ j, r j ≠ j

section Rows
variable [NeZero n]

theorem val_one (hn : 2 ≤ n) : ((1 : Fin n) : ℕ) = 1 := by
  rw [Fin.val_one', Nat.mod_eq_of_lt hn]

theorem one_ne_zero (hn : 2 ≤ n) : (1 : Fin n) ≠ 0 := fun h => by
  have := congrArg Fin.val h
  rw [val_one hn, Fin.val_zero] at this
  exact absurd this Nat.one_ne_zero

/-- The second row of a reduced square is admissible: a bijection, `1` in column `0` (the first
    column is the identity), and `r j ≠ j`, since column `j` holds `j` in row `0` already. -/
theorem row1_mem (hn : 2 ≤ n) {L : Fin n → Fin n → Fin n} (hL : IsReducedLatin L) :
    L 1 ∈ admRows n := by
  obtain ⟨⟨hrow, hcol⟩, h0, h0'⟩ := hL
  simp only [admRows, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hrow 1, h0' 1, fun j h => one_ne_zero hn ((hcol j).1 (h.trans (h0 j).symm))⟩

/-- The decomposition: the reduced squares are the disjoint union of the fibres of the
    admissible second rows. -/
theorem card_eq_sum_admRows (hn : 2 ≤ n) :
    Nat.card {L : Fin n → Fin n → Fin n // IsReducedLatin L} =
      ∑ r ∈ admRows n, Nat.card {L : Fin n → Fin n → Fin n // IsReducedLatin L ∧ L 1 = r} :=
  card_eq_sum_fibres (fun L : Fin n → Fin n → Fin n => IsReducedLatin L) (fun L => L 1) _
    fun _ hL => row1_mem hn hL

end Rows

/-- Lists of length `k` with pairwise distinct entries below `n`, entry `j` satisfying `ok j`:
    the lists of length `k - 1` extended by every admissible last entry (lexicographic order). -/
def seqs (n : ℕ) (ok : ℕ → ℕ → Bool) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (seqs n ok k).flatMap fun l =>
      ((List.range n).filter fun v => ok k v && !l.contains v).map fun v => l ++ [v]

theorem append_mem_seqs {ok : ℕ → ℕ → Bool} {k : ℕ} {l : List ℕ} {v : ℕ} :
    l ++ [v] ∈ seqs n ok (k + 1) ↔ l ∈ seqs n ok k ∧ v < n ∧ ok k v = true ∧ v ∉ l := by
  simp only [seqs, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨l', hl', v', ⟨hv', hok, hnot⟩, he⟩
    obtain ⟨rfl, h2⟩ := List.append_inj' he rfl
    obtain rfl : v' = v := by simpa using h2
    exact ⟨hl', hv', hok, by simpa using hnot⟩
  · rintro ⟨hl, hv, hok, hnot⟩
    exact ⟨l, hl, v, ⟨hv, hok, by simpa using hnot⟩, rfl⟩

theorem injective_succ_iff {k : ℕ} {f : Fin (k + 1) → ℕ} :
    Function.Injective f ↔ Function.Injective (fun i : Fin k => f i.castSucc) ∧
      ∀ i : Fin k, f i.castSucc ≠ f (Fin.last k) := by
  constructor
  · intro h
    exact ⟨h.comp (Fin.castSucc_injective k), fun i e => (Fin.castSucc_lt_last i).ne (h e)⟩
  · rintro ⟨h1, h2⟩ a b hab
    induction a using Fin.lastCases <;> induction b using Fin.lastCases
    · rfl
    · exact absurd hab.symm (h2 _)
    · exact absurd hab (h2 _)
    · exact congrArg _ (h1 hab)

theorem ofFn_mem_seqs {ok : ℕ → ℕ → Bool} : ∀ {k : ℕ} (f : Fin k → ℕ),
    List.ofFn f ∈ seqs n ok k ↔ Function.Injective f ∧ ∀ j, f j < n ∧ ok j (f j) = true
  | 0, f => by simp [seqs, Function.injective_of_subsingleton]
  | k + 1, f => by
    rw [List.ofFn_succ', List.concat_eq_append, append_mem_seqs, ofFn_mem_seqs,
      injective_succ_iff, Fin.forall_fin_succ']
    simp only [List.mem_ofFn, Fin.val_castSucc, Fin.val_last, not_exists]
    tauto

theorem seqs_nodup (ok : ℕ → ℕ → Bool) : ∀ k, (seqs n ok k).Nodup
  | 0 => List.nodup_singleton _
  | k + 1 => by
    rw [seqs, List.nodup_flatMap]
    refine ⟨fun l _ => ((List.nodup_range).filter _).map fun a b h => by simpa using h, ?_⟩
    refine (seqs_nodup ok k).imp fun {a b} hab x hxa hxb => ?_
    simp only [List.mem_map] at hxa hxb
    obtain ⟨v, _, rfl⟩ := hxa
    obtain ⟨w, _, he⟩ := hxb
    exact hab (List.append_inj' he rfl).1.symm

/-- Entry `j` of an admissible second row: not `j`, and `1` at `j = 0`. -/
def rowOk (j v : ℕ) : Bool := v != j && (j != 0 || v == 1)

/-- The admissible second rows as lists of values, in lexicographic order. -/
def rows (n : ℕ) : List (List ℕ) := seqs n rowOk n

/-- A row as the list of its values. -/
def rowList (r : Fin n → Fin n) : List ℕ := List.ofFn fun j => (r j : ℕ)

theorem rowList_injective : Function.Injective (rowList (n := n)) := fun r r' h => by
  funext j
  exact Fin.ext (congrFun (List.ofFn_injective h) j)

theorem mem_admRows_iff [NeZero n] (hn : 2 ≤ n) (r : Fin n → Fin n) :
    r ∈ admRows n ↔ rowList r ∈ rows n := by
  simp only [admRows, Finset.mem_filter, Finset.mem_univ, true_and, rows, rowList,
    ofFn_mem_seqs, ← Finite.injective_iff_bijective, Fin.is_lt, true_and, rowOk,
    Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq]
  have hinj : (Function.Injective fun j => (r j : ℕ)) ↔ Function.Injective r :=
    ⟨fun h _ _ e => h (congrArg Fin.val e), fun h => Fin.val_injective.comp h⟩
  rw [hinj]
  constructor
  · rintro ⟨hi, h0, hj⟩
    refine ⟨hi, fun j => ⟨fun e => hj j (Fin.ext e), ?_⟩⟩
    by_cases hj0 : (j : ℕ) = 0
    · right
      obtain rfl : j = 0 := Fin.ext (by simpa using hj0)
      rw [h0, val_one hn]
    · exact Or.inl hj0
  · rintro ⟨hi, h⟩
    refine ⟨hi, Fin.ext ?_, fun j e => (h j).1 (congrArg Fin.val e)⟩
    rw [val_one hn]
    simpa using (h 0).2

/-- Assembly: one count per admissible second row, the rows listed as in `rows n` (a `decide`
    side condition), give the number of reduced Latin squares. -/
theorem card_eq_of_rows [NeZero n] (hn : 2 ≤ n) (N : ℕ) (E : List ((Fin n → Fin n) × ℕ))
    (hE : ∀ p ∈ E, Nat.card {L : Fin n → Fin n → Fin n // IsReducedLatin L ∧ L 1 = p.1} = p.2)
    (hrows : E.map (fun p => rowList p.1) = rows n) (hN : (E.map Prod.snd).sum = N) :
    Nat.card {L : Fin n → Fin n → Fin n // IsReducedLatin L} = N := by
  classical
  have hmap : (E.map Prod.fst).map rowList = rows n := by rw [List.map_map]; exact hrows
  have hnd : (E.map Prod.fst).Nodup := List.Nodup.of_map rowList (hmap ▸ seqs_nodup rowOk n)
  have hR : admRows n = (E.map Prod.fst).toFinset := by
    ext r
    rw [mem_admRows_iff hn, ← hmap, List.mem_toFinset, List.mem_map]
    exact ⟨fun ⟨r', hr', h⟩ => rowList_injective h ▸ hr', fun h => ⟨r, h, rfl⟩⟩
  rw [card_eq_sum_admRows hn, hR, List.sum_toFinset _ hnd, ← hN, List.map_map]
  congr 1
  exact List.map_congr_left fun p hp => hE p hp

end CountCatcher.Latin
