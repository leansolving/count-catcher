import CountCatcherMath.Check
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Orbit counts from certified counts of fixed models

Generic, independent of any family. For a variable map `π` and a formula `F` over `Fin V`,
`symCnf F V π = F ++ eqClauses V π` adds the binary clauses `x ↔ π x` for the variables
`x < V` moved by `π`; its models are the models of `F` that are invariant under `π`
(`eval_symCnf`).

Let a group `G` act on a type `X` of objects, let `e : X ≃ Models F` be the family lemma, and
let `g` act on the encoding as the variable map `π g` (`ext (e (g • x)) (π g i) = ext (e x) i`,
with `π g` onto `Fin V`). Then the objects fixed by `g` correspond to the models of
`symCnf F V (π g)` (`card_fixedBy_eq`), and Burnside's lemma turns certified counts of these
formulas into the number of orbits (`card_orbits_mul_card_group`). The invariance of `F`
under `π g` is not checked separately: it follows from the action on `X` and `e`.
-/

open Std.Sat

namespace CountCatcher

/-- The clauses `¬x ∨ π x` and `x ∨ ¬π x` for every variable `x < V` with `π x ≠ x`, in
    increasing order of `x`. -/
def eqClauses (V : ℕ) (π : ℕ → ℕ) : List (CNF.Clause ℕ) :=
  ((List.range V).filter fun x => π x != x).flatMap fun x =>
    [[(x, false), (π x, true)], [(x, true), (π x, false)]]

/-- `F` restricted to the assignments invariant under `π`. -/
def symCnf (F : CNF ℕ) (V : ℕ) (π : ℕ → ℕ) : CNF ℕ := F ++ ⟨(eqClauses V π).toArray⟩

theorem eval_symCnf (F : CNF ℕ) (V : ℕ) (π : ℕ → ℕ) (v : ℕ → Bool) :
    (symCnf F V π).eval v = true ↔ F.eval v = true ∧ ∀ x < V, v (π x) = v x := by
  simp only [symCnf, CNF.eval_append, Bool.and_eq_true]
  apply and_congr_right'
  simp only [CNF.eval, List.all_toArray, List.all_eq_true, eqClauses, List.mem_flatMap,
    List.mem_filter, List.mem_range, bne_iff_ne, ne_eq]
  constructor
  · intro h x hx
    by_cases hπ : π x = x
    · rw [hπ]
    · have h1 := h [(x, false), (π x, true)] ⟨x, ⟨hx, hπ⟩, by simp⟩
      have h2 := h [(x, true), (π x, false)] ⟨x, ⟨hx, hπ⟩, by simp⟩
      cases hvx : v x <;> cases hvp : v (π x) <;> simp_all
  · rintro h c ⟨x, ⟨hx, -⟩, hc⟩
    have := h x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> cases hvx : v x <;> simp_all

section Burnside

variable {G X : Type*} [Group G] [MulAction G X] {V : ℕ} {F : CNF ℕ}

theorem ext_injective {a b : Fin V → Bool} (h : ∀ i < V, ext a i = ext b i) : a = b := by
  funext j
  simpa [ext, j.2] using h j j.2

/-- The objects fixed by `g` are the models of `symCnf F V π`, when `g` acts on the encoding
    as the variable map `π`. -/
theorem card_fixedBy_eq (e : X ≃ {a : Fin V → Bool // F.eval (ext a) = true}) (g : G)
    (π : ℕ → ℕ) (hπ : ∀ j < V, ∃ i < V, π i = j)
    (he : ∀ x, ∀ i < V, ext (e (g • x)).1 (π i) = ext (e x).1 i) :
    Nat.card (MulAction.fixedBy X g) =
      Fintype.card {a : Fin V → Bool // (symCnf F V π).eval (ext a) = true} := by
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨(e x).1, (eval_symCnf F V π _).2 ⟨(e x).2, fun i hi => by
        have hx : g • x.1 = x.1 := x.2
        rw [← he x.1 i hi, hx]⟩⟩
      invFun := fun a => ⟨e.symm ⟨a.1, ((eval_symCnf F V π _).1 a.2).1⟩, by
        show g • _ = _
        apply e.injective
        apply Subtype.ext
        apply ext_injective
        intro j hj
        obtain ⟨i, hi, rfl⟩ := hπ j hj
        rw [he _ i hi, Equiv.apply_symm_apply]
        exact (((eval_symCnf F V π _).1 a.2).2 i hi).symm⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp
      right_inv := fun a => by
        apply Subtype.ext
        simp }

/-- Burnside's lemma on certified counts: the number of orbits times the group order is the
    sum over `g` of the model counts of `symCnf F V (π g)`. -/
theorem card_orbits_mul_card_group [Fintype G] [Finite X]
    (e : X ≃ {a : Fin V → Bool // F.eval (ext a) = true}) (π : G → ℕ → ℕ)
    (hπ : ∀ g, ∀ j < V, ∃ i < V, π g i = j)
    (he : ∀ g x, ∀ i < V, ext (e (g • x)).1 (π g i) = ext (e x).1 i) :
    Nat.card (MulAction.orbitRel.Quotient G X) * Nat.card G =
      ∑ g, Fintype.card {a : Fin V → Bool // (symCnf F V (π g)).eval (ext a) = true} := by
  classical
  have : Fintype X := Fintype.ofFinite X
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  simp only [← Nat.card_eq_fintype_card] at hB
  rw [← hB]
  exact Finset.sum_congr rfl fun g _ => card_fixedBy_eq e g (π g) (hπ g) (he g)

end Burnside

/-- A formula without models has model count zero (for the fixed-point formulas refuted by
    an LRAT proof). -/
theorem card_eq_zero_of_unsat {V : ℕ} {F : CNF ℕ} (h : F.Unsat) :
    Fintype.card {a : Fin V → Bool // F.eval (ext a) = true} = 0 := by
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun a => by have := a.2; rw [h] at this; exact Bool.false_ne_true this⟩

end CountCatcher
