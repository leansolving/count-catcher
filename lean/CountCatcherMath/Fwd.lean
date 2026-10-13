import CountCatcherMath.Main
import CountCatcherChecker.Fwd

/-! Part B soundness: unsatisfiability of the augmented CNF gives the forward direction. -/

open Std.Sat

namespace CountCatcher

theorem fwd_of_unsat {F : CNF Nat} {P : Pog} {r : Literal Nat} (h : (fwdCnf F P r).Unsat) :
    Fwd F P r := by
  intro b hF hdefs
  by_contra hr
  have hb := h b
  simp only [fwdCnf, CNF.eval, Array.all_append, Bool.and_eq_false_iff] at hb
  rcases hb with (hb | hb) | hb
  · rw [CNF.eval] at hF; rw [hF] at hb; exact absurd hb (by simp)
  · have ht : P.defs.toArray.all (fun c => CNF.Clause.eval b c) = true := by
      rw [Array.all_eq_true_iff_forall_mem]
      intro c hc; exact hdefs c (by simpa using hc)
    rw [ht] at hb; exact absurd hb (by simp)
  · simp only [litTrue] at hr
    simp [CNF.Clause.eval] at hb
    cases hbr : b r.1 <;> cases hr2 : r.2 <;> simp_all

end CountCatcher
