import CountCatcherMath.Rev
import CountCatcherChecker.RevFast

/-!
# Part C with one reused occurrence table: `checkRevKillFast = checkRevKill`

Built from the zero table of size `2V`, `addBatchOcc` gives exactly the table
`Array.ofFn (n := 2 * V) fun x => occMask cs x` of `batchRefuted` (`addBatchOcc_zero`), and
`clearBatchOcc` turns it back into the zero table (`clearBatchOcc_addBatchOcc_zero`). So every
batch sees the same table as in `checkRevKill`, and the two checks agree on every input
(`checkRevKillFast_eq`); soundness follows from `checkRevKill_sound`.
-/

open Std.Sat

namespace CountCatcher

theorem getElem!_modify_nat (t : Array Nat) (i x : Nat) (f : Nat → Nat) :
    (t.modify i f)[x]! = if i = x ∧ x < t.size then f t[x]! else t[x]! := by
  by_cases hx : x < t.size
  · rw [getElem!_pos _ _ (by simpa [Array.size_modify] using hx), Array.getElem_modify,
      getElem!_pos t x hx]
    by_cases hix : i = x <;> simp [hix, hx]
  · rw [getElem!_neg _ _ (by simpa [Array.size_modify] using hx), getElem!_neg t x hx]
    simp [hx]

theorem getElem!_set!_zero (t : Array Nat) (i x : Nat) :
    (t.set! i 0)[x]! = if i = x then 0 else t[x]! := by
  unfold Array.set!
  by_cases hx : x < t.size
  · rw [getElem!_pos _ _ (by simpa [Array.size_setIfInBounds] using hx),
      Array.getElem_setIfInBounds, getElem!_pos t x hx]
  · rw [getElem!_neg _ _ (by simpa [Array.size_setIfInBounds] using hx), getElem!_neg t x hx]
    simp

/-! ## Adding a batch -/

theorem size_addClauseOcc (j : Nat) (c : CNF.Clause Nat) (t : Array Nat) :
    (addClauseOcc j t c).size = t.size := by
  unfold addClauseOcc
  induction c generalizing t with
  | nil => rfl
  | cons l ls ih => rw [List.foldl_cons, ih, Array.size_modify]

theorem testBit_addClauseOcc (j : Nat) (c : CNF.Clause Nat) (t : Array Nat) (x b : Nat) :
    (addClauseOcc j t c)[x]!.testBit b =
      (t[x]!.testBit b ||
        (decide (x < t.size) && decide (b = j) && c.any fun l => litIdx l == x)) := by
  unfold addClauseOcc
  induction c generalizing t with
  | nil => simp
  | cons l ls ih =>
    rw [List.foldl_cons, ih, Array.size_modify, getElem!_modify_nat]
    by_cases h : litIdx l = x ∧ x < t.size
    · rw [if_pos h, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
      obtain ⟨h1, h2⟩ := h
      subst h1
      by_cases hbj : b = j
      · subst hbj; simp [h2]
      · have hjb : ¬ j = b := fun h => hbj h.symm
        simp [hbj, hjb]
    · rw [if_neg h]
      by_cases hx : x < t.size
      · have h1 : (litIdx l == x) = false := beq_eq_false_iff_ne.mpr fun h1 => h ⟨h1, hx⟩
        simp [h1, hx]
      · simp [hx]

theorem size_addBatchOcc (t : Array Nat) (cs : List (CNF.Clause Nat)) :
    (addBatchOcc t cs).size = t.size := by
  unfold addBatchOcc
  generalize cs.length = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, size_addClauseOcc,
      ih]

theorem testBit_addBatchOcc (t : Array Nat) (cs : List (CNF.Clause Nat)) (x b : Nat) :
    (addBatchOcc t cs)[x]!.testBit b =
      (t[x]!.testBit b ||
        (decide (x < t.size) && decide (b < cs.length) &&
          (cs[b]!).any fun l => litIdx l == x)) := by
  unfold addBatchOcc
  suffices h : ∀ n, ((List.range n).foldl (fun t j => addClauseOcc j t (cs[j]!)) t).size =
      t.size ∧
      ((List.range n).foldl (fun t j => addClauseOcc j t (cs[j]!)) t)[x]!.testBit b =
      (t[x]!.testBit b ||
        (decide (x < t.size) && decide (b < n) && (cs[b]!).any fun l => litIdx l == x)) from
    (h _).2
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, size_addClauseOcc,
      testBit_addClauseOcc, ih.1, ih.2]
    refine ⟨rfl, ?_⟩
    by_cases hbn : b = n
    · subst hbn; simp
    · have h' : (b < n + 1) = (b < n) := propext (by omega)
      simp [hbn, h']

/-- From the zero table, `addBatchOcc` builds the occurrence table of `batchRefuted`. -/
theorem addBatchOcc_zero (V : Nat) (cs : List (CNF.Clause Nat)) :
    addBatchOcc (Array.replicate (2 * V) 0) cs =
      Array.ofFn (n := 2 * V) fun x => occMask cs x.1 := by
  apply Array.ext
  · simp [size_addBatchOcc]
  · intro x h1 h2
    apply Nat.eq_of_testBit_eq
    intro b
    have hx : x < 2 * V := by simpa [size_addBatchOcc] using h1
    rw [← getElem!_pos (addBatchOcc (Array.replicate (2 * V) 0) cs) x h1,
      testBit_addBatchOcc, Array.getElem_ofFn, testBit_occMask,
      getElem!_pos (Array.replicate (2 * V) 0) x (by simpa using hx)]
    simp [hx]

/-! ## Clearing a batch -/

theorem size_clearClauseOcc (t : Array Nat) (c : CNF.Clause Nat) :
    (clearClauseOcc t c).size = t.size := by
  unfold clearClauseOcc
  induction c generalizing t with
  | nil => rfl
  | cons l ls ih => rw [List.foldl_cons, ih]; simp [Array.set!, Array.size_setIfInBounds]

theorem getElem!_clearClauseOcc (t : Array Nat) (c : CNF.Clause Nat) (x : Nat) :
    (clearClauseOcc t c)[x]! = if c.any (fun l => litIdx l == x) then 0 else t[x]! := by
  unfold clearClauseOcc
  induction c generalizing t with
  | nil => simp
  | cons l ls ih =>
    rw [List.foldl_cons, ih, getElem!_set!_zero]
    by_cases h1 : litIdx l = x <;> by_cases h2 : (ls.any fun l => litIdx l == x) = true <;>
      simp [h1, h2]

theorem size_clearBatchOcc (t : Array Nat) (cs : List (CNF.Clause Nat)) :
    (clearBatchOcc t cs).size = t.size := by
  unfold clearBatchOcc
  induction cs generalizing t with
  | nil => rfl
  | cons c cs ih => rw [List.foldl_cons, ih, size_clearClauseOcc]

theorem getElem!_clearBatchOcc (t : Array Nat) (cs : List (CNF.Clause Nat)) (x : Nat) :
    (clearBatchOcc t cs)[x]! =
      if cs.any (fun c => c.any fun l => litIdx l == x) then 0 else t[x]! := by
  unfold clearBatchOcc
  induction cs generalizing t with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih, getElem!_clearClauseOcc]
    by_cases h1 : (c.any fun l => litIdx l == x) = true <;>
      by_cases h2 : (cs.any fun c => c.any fun l => litIdx l == x) = true <;> simp [h1, h2]

/-- Clearing the batch's literals after `addBatchOcc` gives the zero table back. -/
theorem clearBatchOcc_addBatchOcc_zero (V : Nat) (cs : List (CNF.Clause Nat)) :
    clearBatchOcc (addBatchOcc (Array.replicate (2 * V) 0) cs) cs =
      Array.replicate (2 * V) 0 := by
  apply Array.ext
  · simp [size_clearBatchOcc, size_addBatchOcc]
  · intro x h1 h2
    rw [← getElem!_pos (clearBatchOcc (addBatchOcc (Array.replicate (2 * V) 0) cs) cs) x h1,
      getElem!_clearBatchOcc, Array.getElem_replicate]
    split_ifs with h
    · rfl
    · apply Nat.eq_of_testBit_eq
      intro b
      rw [testBit_addBatchOcc, Nat.zero_testBit]
      have hz : (Array.replicate (2 * V) 0)[x]! = 0 := by
        by_cases hx : x < 2 * V
        · rw [getElem!_pos _ x (by simpa using hx)]; simp
        · rw [getElem!_neg _ x (by simpa using hx)]; rfl
      rw [hz, Nat.zero_testBit, Bool.false_or]
      by_contra hb
      simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨-, hb⟩, hany⟩ := hb
      apply h
      rw [List.any_eq_true]
      exact ⟨cs[b]!, by rw [getElem!_pos cs b hb]; exact List.getElem_mem hb, hany⟩

/-! ## Equality with `checkRevKill` -/

theorem batchesRefuted_zero (V : Nat) (P : Pog) (r : Literal Nat)
    (css : List (List (CNF.Clause Nat))) :
    batchesRefuted V P r (Array.replicate (2 * V) 0) css =
      css.all fun cs => batchRefuted V P cs r := by
  induction css with
  | nil => rfl
  | cons cs css ih =>
    simp only [batchesRefuted, List.all_cons]
    rw [clearBatchOcc_addBatchOcc_zero, ih, addBatchOcc_zero]
    have hb : batchRefutedWith V P (Array.ofFn (n := 2 * V) fun x => occMask cs x.1) cs r =
        batchRefuted V P cs r := rfl
    rw [hb]
    cases batchRefuted V P cs r <;> rfl

/-- The fast part C and the bit-parallel part C with a table per batch agree on every input. -/
theorem checkRevKillFast_eq (V : Nat) (P : Pog) (F : CNF Nat) (r : Literal Nat) :
    checkRevKillFast V P F r = checkRevKill V P F r := by
  unfold checkRevKillFast checkRevKill
  rw [batchesRefuted_zero]

/-- Part C soundness for the fast check (same statement as `checkRevKill_sound`). -/
theorem checkRevKillFast_sound {P : Pog} (hP : P.WF) {F : CNF Nat} {r : Literal Nat}
    (hr : r.1 < P.numVars) (h : checkRevKillFast P.V P F r = true) : RevEval F P r :=
  checkRevKill_sound hP hr (by rwa [checkRevKillFast_eq] at h)

end CountCatcher
