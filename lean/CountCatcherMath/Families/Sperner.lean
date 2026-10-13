import CountCatcherMath.Family
import CountCatcherMath.Families.Dedekind
import Mathlib.Order.Antichain

/-!
# Family: uncomplemented Sperner families (OEIS A396728)

Objects: families `F : Finset (Finset (Fin n))` that are antichains under inclusion and contain
no set together with its complement (uncomplemented Sperner families). For `n ≥ 1` their number
is A396728(n). At `n = 0` the OEIS counts `{∅}` although `∅ᶜ = ∅` there (a(0) = 2, the object
predicate below gives 1), so the family lemma assumes `NeZero n`; the encoder is the
generator's for every `n`.

Encoder: one variable per subset `A` of `Fin n`, numbered by its bit mask (`code`: element `i`
has weight `2 ^ i`, through `binEquiv` of `CountCatcherMath/Families/Graphs.lean`), and negative
2-clauses, in the order of `scripts/showcase/oeis/gen_A396728.py`:
* `¬x_s ∨ ¬x_c` for every mask `c < 2 ^ n` and every strict submask `s` of `c` (`c` ascending,
  then `s` descending): `3 ^ n - 2 ^ n` clauses;
* `¬x_a ∨ ¬x_b` with `b = (2 ^ n - 1) ^^^ a` the complement, for `0 < a < b` (the pair of `0`
  and the full set is comparable): `2 ^ (n - 1) - 1` clauses for `n ≥ 1`.
No auxiliary variables (128 variables and 2,122 clauses at `n = 7`).
-/

open Std.Sat

namespace CountCatcher.Sperner

/-- The complement of a mask below `2 ^ n`. -/
abbrev cmp (n u : ℕ) : ℕ := (2 ^ n - 1) ^^^ u

/-- One clause per strictly comparable pair of masks: `c` ascending, then `s` descending. -/
def comparable (n : ℕ) : List (CNF.Clause ℕ) :=
  (List.range (2 ^ n)).flatMap fun c =>
    ((List.range c).reverse.filter fun s => s &&& c == s).map fun s => [(s, false), (c, false)]

/-- One clause per complementary pair of a nonempty mask with a larger mask. -/
def complementary (n : ℕ) : List (CNF.Clause ℕ) :=
  ((List.range (2 ^ n)).filter fun a => a != 0 && decide (a < cmp n a)).map fun a =>
    [(a, false), (cmp n a, false)]

/-- The CNF whose models are the uncomplemented Sperner families on `Fin n`. -/
def cnf (n : ℕ) : CNF ℕ := ⟨(comparable n ++ complementary n).toArray⟩

variable {n : ℕ}

theorem mem_comparable {cl : CNF.Clause ℕ} :
    cl ∈ comparable n ↔ ∃ c < 2 ^ n, ∃ s < c, s &&& c = s ∧ cl = [(s, false), (c, false)] := by
  simp only [comparable, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    List.mem_reverse, beq_iff_eq]
  constructor
  · rintro ⟨c, hc, s, ⟨hs, hsc⟩, rfl⟩; exact ⟨c, hc, s, hs, hsc, rfl⟩
  · rintro ⟨c, hc, s, hs, hsc, rfl⟩; exact ⟨c, hc, s, ⟨hs, hsc⟩, rfl⟩

theorem mem_complementary {cl : CNF.Clause ℕ} :
    cl ∈ complementary n ↔
      ∃ a < 2 ^ n, a ≠ 0 ∧ a < cmp n a ∧ cl = [(a, false), (cmp n a, false)] := by
  simp only [complementary, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true,
    bne_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨ha, h0, hlt⟩, rfl⟩; exact ⟨a, ha, h0, hlt, rfl⟩
  · rintro ⟨a, ha, h0, hlt, rfl⟩; exact ⟨a, ⟨ha, h0, hlt⟩, rfl⟩

/-- A clause of two negative literals: not both variables are true. -/
theorem eval_neg2 (v : ℕ → Bool) (x y : ℕ) :
    CNF.Clause.eval v [(x, false), (y, false)] = true ↔ (v x = true → v y = false) := by
  simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
  cases v x <;> cases v y <;> simp

/-- Semantics of the encoder. -/
theorem eval_iff (v : ℕ → Bool) :
    (cnf n).eval v = true ↔
      (∀ c < 2 ^ n, ∀ s < c, s &&& c = s → v s = true → v c = false) ∧
      (∀ a < 2 ^ n, a ≠ 0 → a < cmp n a → v a = true → v (cmp n a) = false) := by
  unfold CNF.eval
  rw [Array.all_eq_true_iff_forall_mem]
  simp only [cnf, List.mem_toArray, List.mem_append]
  constructor
  · intro h
    refine ⟨fun c hc s hs hsc => ?_, fun a ha h0 hlt => ?_⟩
    · exact (eval_neg2 v _ _).1 (h _ (Or.inl (mem_comparable.2 ⟨c, hc, s, hs, hsc, rfl⟩)))
    · exact (eval_neg2 v _ _).1 (h _ (Or.inr (mem_complementary.2 ⟨a, ha, h0, hlt, rfl⟩)))
  · rintro ⟨h1, h2⟩ cl (hcl | hcl)
    · obtain ⟨c, hc, s, hs, hsc, rfl⟩ := mem_comparable.1 hcl
      exact (eval_neg2 v _ _).2 (h1 c hc s hs hsc)
    · obtain ⟨a, ha, h0, hlt, rfl⟩ := mem_complementary.1 hcl
      exact (eval_neg2 v _ _).2 (h2 a ha h0 hlt)

/-! ## Subsets as masks -/

/-- Subsets of a finite type as their indicator functions. -/
def finsetEquiv (α : Type*) [Fintype α] [DecidableEq α] : Finset α ≃ (α → Bool) where
  toFun A i := decide (i ∈ A)
  invFun f := Finset.univ.filter fun i => f i = true
  left_inv A := by ext i; simp
  right_inv f := by funext i; simp

/-- A subset of `Fin n` as its bit mask. -/
def code (n : ℕ) : Finset (Fin n) ≃ Fin (2 ^ n) := (finsetEquiv (Fin n)).trans (binEquiv n)

theorem mem_code_symm (u : Fin (2 ^ n)) (i : Fin n) :
    i ∈ (code n).symm u ↔ (u : ℕ).testBit i = true := by
  simp [code, finsetEquiv, Dedekind.binEquiv_symm_apply]

theorem testBit_of_le (u : Fin (2 ^ n)) {j : ℕ} (hj : n ≤ j) : (u : ℕ).testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le u.2 (Nat.pow_le_pow_right (by norm_num) hj))

/-- Inclusion of subsets is the submask relation. -/
theorem subset_iff (u w : Fin (2 ^ n)) :
    (code n).symm u ⊆ (code n).symm w ↔ (u : ℕ) &&& w = u := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    by_cases hj : j < n
    · have hi := @h ⟨j, hj⟩
      simp only [mem_code_symm] at hi
      cases hu : (u : ℕ).testBit j
      · simp
      · simp [hi hu]
    · rw [testBit_of_le u (not_lt.1 hj)]; simp
  · intro h i hi
    rw [mem_code_symm] at hi ⊢
    have := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_and, hi, Bool.true_and] at this
    exact this

/-- The complement mask, as an element of `Fin (2 ^ n)`. -/
def flipAll (u : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨cmp n u, Nat.xor_lt_two_pow (Nat.sub_lt (Nat.two_pow_pos n) one_pos) u.2⟩

/-- Complement of subsets is the complement mask. -/
theorem compl_symm (u : Fin (2 ^ n)) : ((code n).symm u)ᶜ = (code n).symm (flipAll u) := by
  ext i
  rw [Finset.mem_compl, mem_code_symm, mem_code_symm]
  simp [flipAll, cmp, Nat.testBit_xor]

theorem cmp_cmp (u : ℕ) : cmp n (cmp n u) = u := by
  simp only [cmp, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- With `n ≥ 1`, no mask is its own complement (bit 0 differs). -/
theorem ne_cmp [NeZero n] (u : ℕ) : u ≠ cmp n u := by
  intro h
  have := congrArg (fun x => x.testBit 0) h
  simp only [cmp, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.pos_of_neZero n,
    decide_true, Bool.true_xor] at this
  cases hb : u.testBit 0 <;> simp [hb] at this

/-! ## The family lemma -/

/-- Assignments of the masks as families of subsets. -/
def famEquiv (n : ℕ) : (Fin (2 ^ n) → Bool) ≃ Finset (Finset (Fin n)) :=
  (Equiv.arrowCongr (code n).symm (Equiv.refl Bool)).trans (finsetEquiv (Finset (Fin n))).symm

theorem mem_famEquiv (a : Fin (2 ^ n) → Bool) (A : Finset (Fin n)) :
    A ∈ famEquiv n a ↔ a (code n A) = true := by
  simp [famEquiv, finsetEquiv]

/-- Models of the encoder are the uncomplemented Sperner families. -/
theorem model_iff [NeZero n] (a : Fin (2 ^ n) → Bool) :
    (cnf n).eval (ext a) = true ↔
      IsAntichain (· ⊆ ·) (famEquiv n a : Set (Finset (Fin n))) ∧
        ∀ A ∈ famEquiv n a, Aᶜ ∉ famEquiv n a := by
  have hext : ∀ u : Fin (2 ^ n), ext a u = a u := fun u => by simp [ext]
  rw [eval_iff]
  constructor
  · rintro ⟨h1, h2⟩
    -- the clauses forbid a mask together with its complement
    have key : ∀ x < 2 ^ n, ∀ y < 2 ^ n, y = cmp n x → x < y →
        ext a x = true → ext a y = false := by
      intro x hx y hy hxy hlt hv
      by_cases h0 : x = 0
      · subst h0; exact h1 y hy 0 hlt (Nat.zero_and y) hv
      · subst hxy; exact h2 x hx h0 hlt hv
    refine ⟨fun A hA B hB hAB hsub => ?_, fun A hA hAc => ?_⟩
    · rw [Finset.mem_coe, mem_famEquiv] at hA hB
      have hA' : A = (code n).symm (code n A) := by simp
      have hB' : B = (code n).symm (code n B) := by simp
      rw [hA', hB', subset_iff] at hsub
      have hne : ((code n A : ℕ)) ≠ code n B := fun h => hAB (by rw [hA', hB', Fin.ext h])
      have hlt : (code n A : ℕ) < code n B :=
        lt_of_le_of_ne (hsub ▸ Nat.and_le_right) hne
      have := h1 _ (code n B).2 _ hlt hsub (by rw [hext]; exact hA)
      rw [hext, hB] at this
      exact Bool.noConfusion this
    · rw [mem_famEquiv] at hA hAc
      have hA' : A = (code n).symm (code n A) := by simp
      have hc : code n Aᶜ = flipAll (code n A) := by
        rw [hA', compl_symm, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rw [hc] at hAc
      set u := code n A
      have hu : ext a u = true := by rw [hext]; exact hA
      have hcu : ext a (cmp n u) = true := by
        have := hext (flipAll u); rw [hAc] at this; exact this
      rcases lt_or_gt_of_ne (ne_cmp (n := n) u) with hlt | hlt
      · have := key u u.2 (cmp n u) (flipAll u).2 rfl hlt hu
        rw [hcu] at this; exact Bool.noConfusion this
      · have := key (cmp n u) (flipAll u).2 u u.2 (cmp_cmp _).symm hlt hcu
        rw [hu] at this; exact Bool.noConfusion this
  · rintro ⟨hanti, hcomp⟩
    have hmem : ∀ u : Fin (2 ^ n), ext a u = true → (code n).symm u ∈ famEquiv n a := by
      intro u hu
      rw [mem_famEquiv, Equiv.apply_symm_apply, ← hext]
      exact hu
    refine ⟨fun c hc s hs hsc hvs => ?_, fun x hx _ _ hvx => ?_⟩
    · by_contra hvc
      rw [Bool.not_eq_false] at hvc
      have hU := hmem ⟨s, hs.trans hc⟩ hvs
      have hW := hmem ⟨c, hc⟩ hvc
      have hne : (code n).symm ⟨s, hs.trans hc⟩ ≠ (code n).symm ⟨c, hc⟩ := by
        intro h
        exact absurd (congrArg Fin.val ((code n).symm.injective h)) (ne_of_lt hs)
      exact hanti hU hW hne ((subset_iff _ _).2 hsc)
    · by_contra hvc
      rw [Bool.not_eq_false] at hvc
      have hX := hmem ⟨x, hx⟩ hvx
      have hY := hmem (flipAll ⟨x, hx⟩) hvc
      rw [← compl_symm] at hY
      exact hcomp _ hX hY

/-- Family lemma: models of the encoder are the uncomplemented Sperner families. -/
def equiv [NeZero n] :
    {a : Fin (2 ^ n) → Bool // (cnf n).eval (ext a) = true} ≃
      {F : Finset (Finset (Fin n)) //
        IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n))) ∧ ∀ A ∈ F, Aᶜ ∉ F} :=
  Equiv.subtypeEquiv (famEquiv n) fun a => model_iff a

/-- A certificate for the encoder counts the uncomplemented Sperner families. -/
theorem card_of_check [NeZero n] {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (2 ^ n) (cnf n) pogStr lratStr N = true) :
    Nat.card {F : Finset (Finset (Fin n)) //
      IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n))) ∧ ∀ A ∈ F, Aᶜ ∉ F} = N :=
  Family.card_of_check equiv h

/-- The same with part B as a separate (streamed) refutation, for large certificates. -/
theorem card_of_checkAC [NeZero n] {pogStr : String} {N : ℕ}
    (h : checkAllAC (2 ^ n) (cnf n) pogStr N = true) (hB : (fwdCnfOf (cnf n) pogStr).Unsat) :
    Nat.card {F : Finset (Finset (Fin n)) //
      IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n))) ∧ ∀ A ∈ F, Aᶜ ∉ F} = N :=
  Family.card_of_checkAC equiv h hB

end CountCatcher.Sperner
