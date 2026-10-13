import CountCatcherMath.PogSound
import CountCatcherMath.RevFast
import CountCatcherMath.Fwd
import CountCatcherChecker.Check

/-! Soundness of the complete checker. -/

open Std.Sat

namespace CountCatcher

theorem cnfWFb_sound {V : Nat} {F : CNF Nat} (h : cnfWFb V F = true) : CnfWF V F := by
  intro c hc l hl
  unfold cnfWFb at h
  rw [Array.all_eq_true_iff_forall_mem] at h
  have := List.all_eq_true.1 (h c hc) l hl
  simpa using this

/-- If the complete check accepts, `F` has exactly `N` models over the universe `Fin V`. -/
theorem checkAll_sound {V : Nat} {F : CNF Nat} {pogStr lratStr : String} {N : Nat}
    (h : checkAll V F pogStr lratStr N = true) :
    Fintype.card {a : Fin V → Bool // F.eval (ext a) = true} = N := by
  unfold checkAll at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hwf, h⟩ := h
  split at h
  · rename_i c _
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hV, hAC⟩, hB⟩ := h
    unfold checkAC at hAC
    split at hAC
    · rename_i st hst
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hAC
      obtain ⟨⟨hroot, hN⟩, hC⟩ := hAC
      obtain ⟨hP, hr, hcnt⟩ := checkPog_sound_of_fold hst hroot
      have hfwd := fwd_of_unsat (LRATCatcher.checkLratCnf_sound _ _ hB)
      have hrev := checkRevKillFast_sound hP hr hC
      rw [card_models_eq_countRoot (cnfWFb_sound hwf) hP hV hr hfwd hrev, ← hcnt, hN]
    · simp at hAC
  · simp at h

/-- Soundness of the split check: parts A and C accepted, part B given as the streamed
    refutation of `fwdCnfOf F pogStr`. -/
theorem checkAllAC_sound {V : Nat} {F : CNF Nat} {pogStr : String} {N : Nat}
    (h : checkAllAC V F pogStr N = true) (hB : (fwdCnfOf F pogStr).Unsat) :
    Fintype.card {a : Fin V → Bool // F.eval (ext a) = true} = N := by
  unfold checkAllAC at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hwf, h⟩ := h
  cases hc : parsePogCert pogStr with
  | none => rw [hc] at h; simp at h
  | some c =>
    rw [hc] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hV, hAC⟩ := h
    have hB' : (fwdCnf F c.pog c.root).Unsat := by simpa [fwdCnfOf, hc] using hB
    unfold checkAC at hAC
    split at hAC
    · rename_i st hst
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hAC
      obtain ⟨⟨hroot, hN⟩, hC⟩ := hAC
      obtain ⟨hP, hr, hcnt⟩ := checkPog_sound_of_fold hst hroot
      have hfwd := fwd_of_unsat hB'
      have hrev := checkRevKillFast_sound hP hr hC
      rw [card_models_eq_countRoot (cnfWFb_sound hwf) hP hV hr hfwd hrev, ← hcnt, hN]
    · simp at hAC

end CountCatcher
