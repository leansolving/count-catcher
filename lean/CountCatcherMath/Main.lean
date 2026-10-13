import CountCatcherMath.Count

/-!
# CountCatcherMath.Main — composition

Parts A (`P.WF`, root in range), B (`Fwd F P r`) and C (`RevEval F P r`) give the number of
models of `F` over the universe `Fin V`.
-/

open Finset Std.Sat

namespace CountCatcher

/-- A CNF over `Fin V` only sees an assignment below `V`. -/
theorem cnf_eval_congr {V : ℕ} {F : CNF ℕ} (hF : CnfWF V F) {b c : ℕ → Bool}
    (h : ∀ v < V, b v = c v) : F.eval b = F.eval c := by
  unfold CNF.eval
  rw [Bool.eq_iff_iff, Array.all_eq_true_iff_forall_mem, Array.all_eq_true_iff_forall_mem]
  refine forall₂_congr fun cl hcl => ?_
  simp only [CNF.Clause.eval, List.any_eq_true]
  constructor <;> rintro ⟨l, hl, hv⟩ <;>
    exact ⟨l, hl, by simp only [h l.1 (hF cl hcl l hl)] at hv ⊢; exact hv⟩

/-- Composition: well-formedness, forward and reverse direction give the model count. -/
theorem card_models_eq_countRoot {V : ℕ} {F : CNF ℕ} {P : Pog} (hF : CnfWF V F) (hP : P.WF)
    (hV : P.V = V) {r : Literal ℕ} (hr : r.1 < P.numVars) (fwd : Fwd F P r)
    (rev : RevEval F P r) :
    Fintype.card {a : Fin V → Bool // F.eval (ext a) = true} = P.countRoot r := by
  subst hV
  rw [Fintype.card_subtype]
  have hm : (univ.filter fun a : Fin P.V → Bool => F.eval (ext a) = true) = P.modsLit r := by
    ext a
    simp only [mem_filter, mem_univ, true_and, Pog.modsLit]
    constructor
    · intro hFa
      -- the evaluation extension satisfies F and the defining clauses
      have hagree : ∀ v < P.V, P.extend (ext a) v = ext a v := fun v hv => by
        rw [P.extend_eq (by simp [Pog.numVars]; omega), Pog.evalVar, if_pos hv]
      have h := fwd (P.extend (ext a)) (by rw [cnf_eval_congr hF hagree]; exact hFa)
        (P.defs_extend hP (ext a))
      simpa [litTrue, Pog.evalLit, P.extend_eq hr] using h
    · exact rev (ext a)
  rw [hm, P.card_modsLit r (P.card_mods hP r.1 hr), Pog.countRoot]

end CountCatcher
