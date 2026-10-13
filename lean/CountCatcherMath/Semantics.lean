import Mathlib.Tactic
import CountCatcherChecker.Spec

/-!
# CountCatcherMath.Semantics — basic facts about POG evaluation and supports
-/

open Std.Sat

namespace CountCatcher.Pog

variable (P : Pog)

/-- Supports lie inside the universe (no well-formedness needed). -/
theorem supp_lt (v x : Nat) (h : P.supp v x = true) : x < P.V := by
  induction v using Nat.strong_induction_on generalizing x with
  | _ v ih =>
  rw [supp] at h
  split_ifs at h with hv
  · simp at h; omega
  split at h
  · simp at h
  · simp only [List.any_eq_true] at h
    obtain ⟨l, -, hl⟩ := h
    split_ifs at hl with hlt
    exact ih _ hlt _ hl
  · simp only [Bool.or_eq_true] at h
    rcases h with h | h <;> split_ifs at h with hlt <;> exact ih _ hlt _ h

theorem supp_input {v : Nat} (hv : v < P.V) : P.supp v v = true := by
  rw [supp]; simp [hv]

theorem supp_prod {v : Nat} {args : List (Literal Nat)} {l : Literal Nat} {x : Nat}
    (hv : ¬ v < P.V) (hn : P.node? v = some (.prod args)) (hl : l ∈ args) (hlt : l.1 < v)
    (hx : P.supp l.1 x = true) : P.supp v x = true := by
  rw [supp]; simp only [hv, hn, if_false, List.any_eq_true]; exact ⟨l, hl, by simp [hlt, hx]⟩

theorem supp_sum_left {v : Nat} {y z : Literal Nat} {x : Nat}
    (hv : ¬ v < P.V) (hn : P.node? v = some (.sum y z)) (hlt : y.1 < v)
    (hx : P.supp y.1 x = true) : P.supp v x = true := by
  rw [supp]; simp [hv, hn, hlt, hx]

theorem supp_sum_right {v : Nat} {y z : Literal Nat} {x : Nat}
    (hv : ¬ v < P.V) (hn : P.node? v = some (.sum y z)) (hlt : z.1 < v)
    (hx : P.supp z.1 x = true) : P.supp v x = true := by
  rw [supp]; simp [hv, hn, hlt, hx]

/-- Locality: the value of `v` depends only on the assignment on its support. -/
theorem evalVar_congr (v : Nat) (a a' : Nat → Bool)
    (h : ∀ x, P.supp v x = true → a x = a' x) : P.evalVar a v = P.evalVar a' v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  rw [evalVar, evalVar]
  split_ifs with hv
  · exact h v (P.supp_input hv)
  split
  · rfl
  · rename_i args hn
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall₂_congr fun l hl => ?_
    split_ifs with hlt
    · rw [ih _ hlt fun x hx => h x (P.supp_prod hv hn hl hlt hx)]
    · rfl
  · rename_i y z hn
    congr 1
    · split_ifs with hlt
      · rw [ih _ hlt fun x hx => h x (P.supp_sum_left hv hn hlt hx)]
      · rfl
    · split_ifs with hlt
      · rw [ih _ hlt fun x hx => h x (P.supp_sum_right hv hn hlt hx)]
      · rfl

theorem node?_ext {i : Nat} : P.node? (P.V + i) = P.nodes[i]? := by
  simp [node?]

theorem extend_eq {a : Nat → Bool} {v : Nat} (hv : v < P.numVars) :
    P.extend a v = P.evalVar a v := by
  simp [extend, hv]

theorem evalVar_prod (a : Nat → Bool) {i : Nat} (hi : i < P.nodes.size)
    {args : List (Literal Nat)} (hn : P.nodes[i] = .prod args) :
    P.evalVar a (P.V + i) =
      args.all fun l => if _ : l.1 < P.V + i then P.evalVar a l.1 == l.2 else false := by
  rw [evalVar, if_neg (by omega), node?_ext, Array.getElem?_eq_getElem hi, hn]

theorem evalVar_sum (a : Nat → Bool) {i : Nat} (hi : i < P.nodes.size)
    {x y : Literal Nat} (hn : P.nodes[i] = .sum x y) :
    P.evalVar a (P.V + i) =
      ((if _ : x.1 < P.V + i then P.evalVar a x.1 == x.2 else false) ||
       (if _ : y.1 < P.V + i then P.evalVar a y.1 == y.2 else false)) := by
  rw [evalVar, if_neg (by omega), node?_ext, Array.getElem?_eq_getElem hi, hn]

/-- The evaluation extension satisfies all defining clauses (only needs arguments to refer to
    earlier variables). -/
theorem defs_extend' (hargs0 : ∀ i (h : i < P.nodes.size), ∀ l ∈ Node.args P.nodes[i], l.1 < P.V + i)
    (a : Nat → Bool) : clausesTrue (P.extend a) P.defs := by
  intro c hc
  simp only [defs, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨i, hi, hc⟩ := hc
  rw [Array.getElem?_eq_getElem hi] at hc
  have hargs := hargs0 i hi
  have hu : P.V + i < P.numVars := by simp [numVars]; omega
  -- the extension agrees with evaluation on the node and its arguments
  have hlt : ∀ l ∈ Node.args P.nodes[i], P.extend a l.1 = P.evalVar a l.1 := fun l hl =>
    P.extend_eq (by have := hargs l hl; simp [numVars]; omega)
  generalize hn : P.nodes[i] = n at hc hargs hlt
  cases n with
  | prod args =>
    simp only [Node.args] at hargs hlt
    have hval : P.extend a (P.V + i) = args.all fun l => P.evalVar a l.1 == l.2 := by
      rw [P.extend_eq hu, P.evalVar_prod a hi hn]
      rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      refine forall₂_congr fun l hl => ?_
      simp [hargs l hl]
    simp only [defClauses, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨l, hl, rfl⟩
    · -- u ∨ ¬l₁ ∨ … ∨ ¬lₖ
      cases hv : P.extend a (P.V + i)
      · rw [hv, eq_comm, List.all_eq_false] at hval
        obtain ⟨l, hl, hf⟩ := hval
        simp only [CNF.Clause.eval, List.any_cons, List.any_map, Bool.or_eq_true]
        right
        rw [List.any_eq_true]
        refine ⟨l, hl, ?_⟩
        simp only [Function.comp, hlt l hl]
        revert hf; cases P.evalVar a l.1 <;> cases l.2 <;> simp
      · simp [CNF.Clause.eval, hv]
    · -- ¬u ∨ lᵢ
      cases hv : P.extend a (P.V + i)
      · simp [CNF.Clause.eval, hv]
      · rw [hv, eq_comm, List.all_eq_true] at hval
        have := hval l hl
        simp [CNF.Clause.eval, hlt l hl] at this ⊢
        exact Or.inr this
  | sum x y =>
    simp only [Node.args, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hargs hlt
    have hval : P.extend a (P.V + i) = ((P.evalVar a x.1 == x.2) || (P.evalVar a y.1 == y.2)) := by
      rw [P.extend_eq hu, P.evalVar_sum a hi hn]
      simp [hargs.1, hargs.2]
    simp only [defClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      simp only [CNF.Clause.eval, List.any_cons, List.any_nil, hval, hlt.1, hlt.2] <;>
      cases P.evalVar a x.1 <;> cases P.evalVar a y.1 <;> cases x.2 <;> cases y.2 <;> simp

/-- The evaluation extension satisfies all defining clauses. -/
theorem defs_extend (hP : P.WF) (a : Nat → Bool) : clausesTrue (P.extend a) P.defs :=
  P.defs_extend' hP.args_lt a

end CountCatcher.Pog
