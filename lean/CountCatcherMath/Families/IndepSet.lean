import CountCatcherMath.Check
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Independent sets of a graph on `Fin k`

Encoder: one variable per vertex, one clause `¬u ∨ ¬v` per edge `{u, v}` with `u < v`.
Family lemma: the models correspond to Mathlib's independent sets, so a certificate for
`cnf G` proves `Nat.card {s : Finset (Fin k) // G.IsIndepSet s} = N`.
-/

open Std.Sat

namespace CountCatcher.IndepSet

variable {k : ℕ} (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]

/-- One clause per edge, in lexicographic order of `(u, v)` with `u < v`. -/
def edgeClauses : List (CNF.Clause ℕ) :=
  (List.finRange k).flatMap fun u => (List.finRange k).filterMap fun v =>
    if u < v ∧ G.Adj u v then some [(u.val, false), (v.val, false)] else none

def cnf : CNF ℕ := ⟨(edgeClauses G).toArray⟩

theorem mem_edgeClauses {c : CNF.Clause ℕ} :
    c ∈ edgeClauses G ↔ ∃ u v : Fin k, u < v ∧ G.Adj u v ∧ c = [(u.val, false), (v.val, false)] := by
  simp only [edgeClauses, List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq]
  constructor
  · rintro ⟨u, v, ⟨huv, hadj⟩, rfl⟩; exact ⟨u, v, huv, hadj, rfl⟩
  · rintro ⟨u, v, huv, hadj, rfl⟩; exact ⟨u, v, ⟨huv, hadj⟩, rfl⟩

theorem cnf_wf : CnfWF k (cnf G) := by
  intro c hc l hl
  obtain ⟨u, v, -, -, rfl⟩ := (mem_edgeClauses G).1 (by simpa [cnf] using hc)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> simp

theorem eval_iff (a : Fin k → Bool) :
    (cnf G).eval (ext a) = true ↔ ∀ u v, G.Adj u v → ¬ (a u = true ∧ a v = true) := by
  have hext : ∀ u : Fin k, ext a u.val = a u := fun u => by simp [ext]
  unfold CNF.eval
  rw [Array.all_eq_true_iff_forall_mem]
  simp only [cnf, List.mem_toArray]
  constructor
  · intro h u v hadj ⟨hu, hv⟩
    rcases lt_trichotomy u v with huv | rfl | hvu
    · have := h _ ((mem_edgeClauses G).2 ⟨u, v, huv, hadj, rfl⟩)
      simp [CNF.Clause.eval, hext, hu, hv] at this
    · exact G.irrefl hadj
    · have := h _ ((mem_edgeClauses G).2 ⟨v, u, hvu, hadj.symm, rfl⟩)
      simp [CNF.Clause.eval, hext, hu, hv] at this
  · intro h c hc
    obtain ⟨u, v, -, hadj, rfl⟩ := (mem_edgeClauses G).1 hc
    have := h u v hadj
    simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false, hext]
    cases hu : a u <;> cases hv : a v <;> simp_all

/-- Family lemma: models of the encoder are the independent sets. -/
def equiv : {a : Fin k → Bool // (cnf G).eval (ext a) = true} ≃
    {s : Finset (Fin k) // G.IsIndepSet (s : Set (Fin k))} where
  toFun a := ⟨Finset.univ.filter (fun i => a.1 i = true), by
    intro u hu v hv _ hadj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hu hv
    exact (eval_iff G a.1).1 a.2 u v hadj ⟨hu, hv⟩⟩
  invFun s := ⟨fun i => decide (i ∈ s.1), by
    rw [eval_iff]
    intro u v hadj ⟨hu, hv⟩
    simp only [decide_eq_true_eq] at hu hv
    exact s.2 hu hv (G.ne_of_adj hadj) hadj⟩
  left_inv a := by ext i; simp
  right_inv s := by ext i; simp

/-- A certificate accepted by the checker counts the independent sets of `G`. -/
theorem card_of_check {pogStr lratStr : String} {N : ℕ}
    (h : checkAll k (cnf G) pogStr lratStr N = true) :
    Nat.card {s : Finset (Fin k) // G.IsIndepSet (s : Set (Fin k))} = N := by
  rw [← Nat.card_congr (equiv G), Nat.card_eq_fintype_card, checkAll_sound h]

/-- The same with part B as a separate (streamed) refutation, for large certificates. -/
theorem card_of_checkAC {pogStr : String} {N : ℕ}
    (h : checkAllAC k (cnf G) pogStr N = true) (hB : (fwdCnfOf (cnf G) pogStr).Unsat) :
    Nat.card {s : Finset (Fin k) // G.IsIndepSet (s : Set (Fin k))} = N := by
  rw [← Nat.card_congr (equiv G), Nat.card_eq_fintype_card, checkAllAC_sound h hB]

end CountCatcher.IndepSet
