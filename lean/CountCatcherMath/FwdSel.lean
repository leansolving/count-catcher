import CountCatcherMath.Check
import CountCatcherChecker.FwdSel

/-!
# Part B on a selection: a refutation of the selected clauses refutes `fwdCnf`

Every clause that `fwdCnfSel` pushes is a clause of `F`, a defining clause of `P`, or the unit
`¬r` (`mem_fwdCnfSel`), whatever the mask. Unsatisfiability passes from a CNF to any CNF that
contains all its clauses (`unsat_of_subset`), so `fwdCnfOf_unsat_of_sel` turns a streamed
refutation of `fwdCnfOfSel F pogStr keepStr` into the hypothesis of `checkAllAC_sound` and of
the families' `card_of_checkAC`.
-/

open Std.Sat

namespace CountCatcher

variable {mask : String}

theorem mem_ite_push {b : Bool} {a : Array (CNF.Clause Nat)} {d c : CNF.Clause Nat}
    (h : c ∈ (if b = true then a.push d else a)) : c ∈ a ∨ c = d := by
  split at h
  · exact Array.mem_push.1 h
  · exact Or.inl h

theorem mem_foldl_keepStep (c : CNF.Clause Nat) :
    ∀ (l : List (CNF.Clause Nat)) (p : Nat × Array (CNF.Clause Nat)),
      c ∈ (l.foldl (keepStep mask) p).2 → c ∈ p.2 ∨ c ∈ l := by
  intro l
  induction l with
  | nil => intro p h; exact Or.inl h
  | cons d l ih =>
    intro p h
    rcases ih _ h with h | h
    · rcases mem_ite_push h with h | rfl
      · exact Or.inl h
      · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_foldl_keepArg (c : CNF.Clause Nat) (u : Nat) :
    ∀ (args : List (Literal Nat)) (p : Nat × Array (CNF.Clause Nat)),
      c ∈ (args.foldl (keepArg mask u) p).2 → c ∈ p.2 ∨ ∃ l ∈ args, c = [(u, false), l] := by
  intro args
  induction args with
  | nil => intro p h; exact Or.inl h
  | cons a args ih =>
    intro p h
    rcases ih _ h with h | ⟨l, hl, rfl⟩
    · rcases mem_ite_push h with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨a, List.mem_cons_self, rfl⟩
    · exact Or.inr ⟨l, List.mem_cons_of_mem _ hl, rfl⟩

/-- A clause pushed by `keepDefs` is a defining clause of the node. -/
theorem mem_keepDefs {c : CNF.Clause Nat} {u : Nat} {n : Node} {p : Nat × Array (CNF.Clause Nat)}
    (h : c ∈ (keepDefs mask u n p).2) : c ∈ p.2 ∨ c ∈ Pog.defClauses u n := by
  cases n with
  | prod args =>
    rcases mem_foldl_keepArg c u args _ h with h | ⟨l, hl, rfl⟩
    · rcases mem_ite_push h with h | rfl
      · exact Or.inl h
      · exact Or.inr (by simp [Pog.defClauses])
    · exact Or.inr (by simp only [Pog.defClauses, List.mem_cons, List.mem_map]; exact Or.inr ⟨l, hl, rfl⟩)
  | sum x y =>
    rcases mem_ite_push h with h | rfl
    · rcases mem_ite_push h with h | rfl
      · rcases mem_ite_push h with h | rfl
        · exact Or.inl h
        · exact Or.inr (by simp [Pog.defClauses])
      · exact Or.inr (by simp [Pog.defClauses])
    · exact Or.inr (by simp [Pog.defClauses])

theorem mem_defs_of_node {P : Pog} {i : Nat} {n : Node} (hn : P.nodes[i]? = some n)
    {c : CNF.Clause Nat} (hc : c ∈ Pog.defClauses (P.V + i) n) : c ∈ P.defs := by
  have hi : i < P.nodes.size := by
    by_contra hge; rw [Array.getElem?_eq_none (by omega)] at hn; simp at hn
  simp only [Pog.defs, List.mem_flatMap, List.mem_range]
  exact ⟨i, hi, by rw [hn]; exact hc⟩

theorem mem_keepNodes {P : Pog} (c : CNF.Clause Nat) :
    ∀ (k i : Nat) (p : Nat × Array (CNF.Clause Nat)),
      c ∈ (keepNodes mask P k i p).2 → c ∈ p.2 ∨ c ∈ P.defs := by
  intro k
  induction k with
  | zero => intro i p h; exact Or.inl h
  | succ k ih =>
    intro i p h
    unfold keepNodes at h
    split at h
    · rename_i n hn
      rcases ih _ _ h with h | h
      · rcases mem_keepDefs h with h | h
        · exact Or.inl h
        · exact Or.inr (mem_defs_of_node hn h)
      · exact Or.inr h
    · exact ih _ _ h

/-- Every selected clause is a clause of `fwdCnf F P r`, for every mask. -/
theorem mem_fwdCnfSel {F : CNF Nat} {P : Pog} {r : Literal Nat} {c : CNF.Clause Nat}
    (h : c ∈ (fwdCnfSel F P r mask).clauses) : c ∈ (fwdCnf F P r).clauses := by
  simp only [fwdCnf, Array.mem_append, List.mem_toArray]
  simp only [fwdCnfSel] at h
  have hF : ∀ d ∈ (F.clauses.foldl (keepStep mask) (0, #[])).2, d ∈ F.clauses := by
    intro d hd
    rw [← Array.foldl_toList] at hd
    rcases mem_foldl_keepStep d _ _ hd with hd | hd
    · simp at hd
    · exact Array.mem_toList_iff.1 hd
  have hrest : ∀ d ∈ (keepNodes mask P P.nodes.size 0
      (F.clauses.foldl (keepStep mask) (0, #[]))).2, d ∈ F.clauses ∨ d ∈ P.defs := by
    intro d hd
    rcases mem_keepNodes d _ _ _ hd with hd | hd
    · exact Or.inl (hF d hd)
    · exact Or.inr hd
  rcases mem_ite_push h with h | rfl
  · rcases hrest c h with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  · exact Or.inr (by simp)

/-- A CNF that contains all clauses of an unsatisfiable CNF is unsatisfiable. -/
theorem unsat_of_subset {G H : CNF Nat} (hGH : ∀ c ∈ G.clauses, c ∈ H.clauses) (hG : G.Unsat) :
    H.Unsat := by
  intro a
  have hGa := hG a
  by_contra hH
  rw [Bool.not_eq_false] at hH
  simp only [CNF.eval, Array.all_eq_true_iff_forall_mem] at hH
  have : G.eval a = true := by
    simp only [CNF.eval, Array.all_eq_true_iff_forall_mem]
    exact fun c hc => hH c (hGH c hc)
  rw [hGa] at this
  exact Bool.false_ne_true this

theorem fwdCnf_unsat_of_sel {F : CNF Nat} {P : Pog} {r : Literal Nat}
    (h : (fwdCnfSel F P r mask).Unsat) : (fwdCnf F P r).Unsat :=
  unsat_of_subset (fun _ hc => mem_fwdCnfSel hc) h

/-- File-level form: a refutation of the selection given by `keepStr` is a refutation of
    part B's CNF `fwdCnfOf F pogStr`. -/
theorem fwdCnfOf_unsat_of_sel {F : CNF Nat} {pogStr keepStr : String}
    (h : (fwdCnfOfSel F pogStr keepStr).Unsat) : (fwdCnfOf F pogStr).Unsat := by
  unfold fwdCnfOfSel at h
  unfold fwdCnfOf
  split at h
  · rename_i c hc
    rw [hc]
    exact fwdCnf_unsat_of_sel h
  · rename_i hc
    rw [hc]
    exact h

end CountCatcher
