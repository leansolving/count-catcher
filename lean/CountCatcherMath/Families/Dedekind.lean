import CountCatcherMath.Family
import CountCatcherMath.Families.Graphs
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Nat.Bitwise

/-!
# Family: monotone Boolean functions (Dedekind numbers)

Encoder: one variable per point of `Fin n → Bool`, the point `x` being variable
`binEquiv n x` (coordinate `i` has weight `2 ^ i`, `CountCatcherMath/Families/Graphs.lean`), and one
binary clause `¬x_u ∨ x_v` for every covering pair, where `v = u ||| 2 ^ b` is `u` with the
clear bit `b` set, in the order `u`, then `b` (as `scripts/showcase/gen_dedekind.py`). No
auxiliary variables. Family lemma: the models are the monotone functions
`(Fin n → Bool) → Bool` for Mathlib's pointwise order (`false ≤ true`), so a certificate proves
`Nat.card {f : (Fin n → Bool) → Bool // Monotone f} = M(n)`, the Dedekind number.

The key step is `monotone_iff_flip`: monotone equals monotone along single-bit flips, from
Mathlib's `monotone_iff_forall_covBy` (the order is locally finite) and `Pi.covBy_iff`.
-/

open Std.Sat

namespace CountCatcher.Dedekind

/-- One clause `¬x_u ∨ x_(u ||| 2 ^ b)` per point `u` and clear bit `b`. -/
def clauses (n : ℕ) : List (CNF.Clause ℕ) :=
  (List.range (2 ^ n)).flatMap fun u =>
    ((List.range n).filter fun b => !u.testBit b).map fun b => [(u, false), (u ||| 2 ^ b, true)]

/-- The CNF whose models are the monotone Boolean functions on `n` variables. -/
def cnf (n : ℕ) : CNF ℕ := ⟨(clauses n).toArray⟩

variable {n : ℕ}

theorem mem_clauses {c : CNF.Clause ℕ} :
    c ∈ clauses n ↔
      ∃ u < 2 ^ n, ∃ b < n, u.testBit b = false ∧ c = [(u, false), (u ||| 2 ^ b, true)] := by
  simp only [clauses, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · rintro ⟨u, hu, b, ⟨hb, hub⟩, rfl⟩; exact ⟨u, hu, b, hb, hub, rfl⟩
  · rintro ⟨u, hu, b, hb, hub, rfl⟩; exact ⟨u, hu, b, ⟨hb, hub⟩, rfl⟩

/-- Semantics of the encoder: every covering pair is respected. -/
theorem eval_iff (v : ℕ → Bool) :
    (cnf n).eval v = true ↔
      ∀ u < 2 ^ n, ∀ b < n, u.testBit b = false → v u = true → v (u ||| 2 ^ b) = true := by
  unfold CNF.eval
  rw [Array.all_eq_true_iff_forall_mem]
  simp only [cnf, List.mem_toArray]
  constructor
  · intro h u hu b hb hub hv
    have := h _ (mem_clauses.2 ⟨u, hu, b, hb, hub, rfl⟩)
    simpa [CNF.Clause.eval, hv] using this
  · intro h c hc
    obtain ⟨u, hu, b, hb, hub, rfl⟩ := mem_clauses.1 hc
    have := h u hu b hb hub
    simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false]
    cases hv : v u <;> simp_all

/-- Monotone equals monotone along single-bit flips. -/
theorem monotone_iff_flip (f : (Fin n → Bool) → Bool) :
    Monotone f ↔ ∀ x i, x i = false → f x ≤ f (Function.update x i true) := by
  classical
  letI : LocallyFiniteOrder (Fin n → Bool) := Fintype.toLocallyFiniteOrder
  rw [monotone_iff_forall_covBy]
  constructor
  · intro h x i hx
    apply h
    rw [Pi.covBy_iff]
    refine ⟨i, ?_, fun j hj => ?_⟩
    · rw [Bool.covBy_iff]; simp [hx]
    · simp [Function.update_of_ne hj]
  · intro h a b hab
    obtain ⟨i, hi, hj⟩ := Pi.covBy_iff.1 hab
    rw [Bool.covBy_iff] at hi
    have hai : a i = false ∧ b i = true := by
      revert hi; cases a i <;> cases b i <;> decide
    have hb : b = Function.update a i true := by
      funext j
      by_cases hji : j = i
      · subst hji; simp [hai.2]
      · simp [Function.update_of_ne hji, hj j hji]
    rw [hb]
    exact h a i hai.1

/-- The point of variable `u`: its bits. -/
theorem binEquiv_symm_apply (u : Fin (2 ^ n)) (i : Fin n) :
    (binEquiv n).symm u i = (u : ℕ).testBit i := by
  have h := finFunctionFinEquiv_symm_apply_val u i
  simp only [binEquiv, Equiv.symm_trans_apply, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply,
    Equiv.refl_symm, Equiv.symm_symm, Function.comp_apply, Equiv.refl_apply]
  rw [Nat.testBit_eq_decide_div_mod_eq, ← h]
  generalize finFunctionFinEquiv.symm u i = k
  fin_cases k <;> rfl

/-- Setting the clear bit `b` of `u`. -/
def flip (u : Fin (2 ^ n)) (b : Fin n) : Fin (2 ^ n) :=
  ⟨u ||| 2 ^ (b : ℕ), Nat.or_lt_two_pow u.2 (Nat.pow_lt_pow_right (by norm_num) b.2)⟩

theorem symm_flip (u : Fin (2 ^ n)) (b : Fin n) :
    (binEquiv n).symm (flip u b) = Function.update ((binEquiv n).symm u) b true := by
  funext i
  rw [binEquiv_symm_apply]
  by_cases hi : i = b
  · subst hi; simp [flip]
  · rw [Function.update_of_ne hi, binEquiv_symm_apply]
    have : (b : ℕ) ≠ i := fun h => hi (Fin.ext h.symm)
    simp [flip, this]

/-- Models of the encoder are the functions monotone along single-bit flips. -/
theorem model_iff (a : Fin (2 ^ n) → Bool) :
    (cnf n).eval (ext a) = true ↔ Monotone fun x => a (binEquiv n x) := by
  have hext : ∀ u : Fin (2 ^ n), ext a u = a u := fun u => by simp [ext]
  rw [eval_iff, monotone_iff_flip]
  constructor
  · intro h x i hx
    set u := binEquiv n x
    have hx' : x = (binEquiv n).symm u := by simp [u]
    have hub : (u : ℕ).testBit i = false := by rw [← binEquiv_symm_apply, ← hx', hx]
    have key := h u u.2 i i.2 hub
    have hf : ext a ((u : ℕ) ||| 2 ^ (i : ℕ)) = a (flip u i) := hext (flip u i)
    rw [hext, hf] at key
    have hw : binEquiv n (Function.update x i true) = flip u i := by
      rw [hx', ← symm_flip, Equiv.apply_symm_apply]
    rw [hw, Bool.le_iff_imp]
    exact key
  · intro h u hu b hb hub hv
    set U : Fin (2 ^ n) := ⟨u, hu⟩
    have hx : ((binEquiv n).symm U) ⟨b, hb⟩ = false := by rw [binEquiv_symm_apply]; exact hub
    have key := h _ _ hx
    rw [← symm_flip, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Bool.le_iff_imp] at key
    have hU : ext a u = a U := hext U
    have hf : ext a (u ||| 2 ^ b) = a (flip U ⟨b, hb⟩) := hext (flip U ⟨b, hb⟩)
    rw [hf]
    exact key (by rw [← hU]; exact hv)

/-- Family lemma: models of the encoder are the monotone Boolean functions. -/
def equiv :
    {a : Fin (2 ^ n) → Bool // (cnf n).eval (ext a) = true} ≃
      {f : (Fin n → Bool) → Bool // Monotone f} :=
  Equiv.subtypeEquiv (Equiv.arrowCongr (binEquiv n).symm (Equiv.refl Bool)) fun a => by
    rw [model_iff]; rfl

/-- A certificate for the encoder counts the monotone Boolean functions. -/
theorem card_of_check {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (2 ^ n) (cnf n) pogStr lratStr N = true) :
    Nat.card {f : (Fin n → Bool) → Bool // Monotone f} = N :=
  Family.card_of_check equiv h

/-- The same with part B as a separate (streamed) refutation, for large certificates. -/
theorem card_of_checkAC {pogStr : String} {N : ℕ}
    (h : checkAllAC (2 ^ n) (cnf n) pogStr N = true) (hB : (fwdCnfOf (cnf n) pogStr).Unsat) :
    Nat.card {f : (Fin n → Bool) → Bool // Monotone f} = N :=
  Family.card_of_checkAC equiv h hB

end CountCatcher.Dedekind
