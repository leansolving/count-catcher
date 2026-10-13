import CountCatcherMath.Semantics
import CountCatcherMath.Indep

/-!
# CountCatcherMath.Count — the counting lemma

For a well-formed POG and a variable `v`, the number of assignments of `Fin V` on which `v`
evaluates to true is `countVar v * 2 ^ (V - suppSize v)`.
-/

open Finset Std.Sat

namespace CountCatcher

theorem card_eq_filter (n : ℕ) (f : ℕ → Bool) :
    card n f = (univ.filter fun i : Fin n => f i = true).card := by
  unfold card
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if f i = true then 1 else 0)]
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.countP_append, Finset.sum_range_succ, ih]; simp [List.countP_cons]

/-- Exactly half of all assignments set a given coordinate to true. -/
theorem card_coord_true {V : ℕ} (i : Fin V) :
    (univ.filter fun a : Fin V → Bool => a i = true).card = 2 ^ (V - 1) := by
  have hflip : (univ.filter fun a : Fin V → Bool => a i = true).card =
      (univ.filter fun a : Fin V → Bool => ¬ a i = true).card := by
    let e : (Fin V → Bool) ≃ (Fin V → Bool) :=
      { toFun := fun a => Function.update a i (!a i)
        invFun := fun a => Function.update a i (!a i)
        left_inv := fun a => by funext j; by_cases h : j = i <;> simp [Function.update, h]
        right_inv := fun a => by funext j; by_cases h : j = i <;> simp [Function.update, h] }
    apply card_equiv e
    intro a; simp [e]
  have htot := card_filter_add_card_filter_not (s := (univ : Finset (Fin V → Bool)))
    (fun a : Fin V → Bool => a i = true)
  rw [← hflip, card_univ_assign] at htot
  obtain ⟨k, rfl⟩ : ∃ k, V = k + 1 := ⟨V - 1, by have := i.pos; omega⟩
  rw [pow_succ] at htot
  simp only [Nat.add_sub_cancel]
  omega

namespace Pog

variable (P : Pog)

/-- Support of `v` as a finset of the universe. -/
def suppF (v : ℕ) : Finset (Fin P.V) := univ.filter fun i => P.supp v i = true

theorem suppSize_eq (v : ℕ) : P.suppSize v = (P.suppF v).card := card_eq_filter _ _

theorem suppSize_le (v : ℕ) : P.suppSize v ≤ P.V := by
  rw [suppSize_eq]; exact (card_le_univ _).trans (by simp)

theorem mem_suppF {v : ℕ} {i : Fin P.V} : i ∈ P.suppF v ↔ P.supp v i = true := by
  simp [suppF]

/-- Locality for assignments of the universe. -/
theorem evalVar_ext_congr (v : ℕ) (a b : Fin P.V → Bool) (h : ∀ i ∈ P.suppF v, a i = b i) :
    P.evalVar (ext a) v = P.evalVar (ext b) v := by
  apply evalVar_congr
  intro x hx
  have hxV := P.supp_lt v x hx
  have := h ⟨x, hxV⟩ (P.mem_suppF.2 hx)
  simp [ext, hxV, this]

/-- Models of a literal among the assignments of the universe. -/
abbrev modsLit (l : Literal ℕ) : Finset (Fin P.V → Bool) :=
  univ.filter fun a => P.evalLit (ext a) l = true

/-- From the count of a variable to the count of its literals. -/
theorem card_modsLit (l : Literal ℕ)
    (hvar : (P.modsLit (l.1, true)).card = P.countVar l.1 * 2 ^ (P.V - P.suppSize l.1)) :
    (P.modsLit l).card = P.countLit l * 2 ^ (P.V - P.suppSize l.1) := by
  obtain ⟨v, b⟩ := l
  cases b
  · have hc : (P.modsLit (v, false)).card = 2 ^ P.V - (P.modsLit (v, true)).card := by
      rw [← card_univ_assign, ← card_filter_add_card_filter_not
        (s := (univ : Finset (Fin P.V → Bool))) (fun a => P.evalLit (ext a) (v, true) = true)]
      simp only [modsLit, Nat.add_sub_cancel_left]
      congr 1; ext a; simp [evalLit]
    rw [hc, hvar]
    simp only [countLit, Bool.false_eq_true, if_false, Nat.sub_mul]
    rw [← pow_add, Nat.add_sub_cancel' (P.suppSize_le v)]
  · simpa [countLit] using hvar

/-- Union of the supports of a list of literals. -/
def suppU : List (Literal ℕ) → Finset (Fin P.V)
  | [] => ∅
  | l :: ls => P.suppF l.1 ∪ suppU ls

theorem mem_suppU {ls : List (Literal ℕ)} {i : Fin P.V} :
    i ∈ P.suppU ls ↔ ∃ l ∈ ls, i ∈ P.suppF l.1 := by
  induction ls with
  | nil => simp [suppU]
  | cons l ls ih => simp [suppU, ih]

/-- Product rule: literals with pairwise disjoint supports are independent. -/
theorem card_all (ls : List (Literal ℕ))
    (hlit : ∀ l ∈ ls, (P.modsLit l).card = P.countLit l * 2 ^ (P.V - P.suppSize l.1))
    (hdisj : ls.Pairwise fun l₁ l₂ => ∀ x, ¬ (P.supp l₁.1 x = true ∧ P.supp l₂.1 x = true)) :
    (univ.filter fun a : Fin P.V → Bool => ∀ l ∈ ls, P.evalLit (ext a) l = true).card =
      (ls.map P.countLit).prod * 2 ^ (P.V - (ls.map fun l => P.suppSize l.1).sum) ∧
    (P.suppU ls).card = (ls.map fun l => P.suppSize l.1).sum := by
  induction ls with
  | nil => simp [suppU]
  | cons l ls ih =>
    rw [List.pairwise_cons] at hdisj
    obtain ⟨hcard, hU⟩ := ih (fun l' hl' => hlit l' (List.mem_cons_of_mem _ hl')) hdisj.2
    have hST : Disjoint (P.suppF l.1) (P.suppU ls) := by
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨l', hl', hi'⟩ := P.mem_suppU.1 hi'
      exact hdisj.1 l' hl' i ⟨P.mem_suppF.1 hi, P.mem_suppF.1 hi'⟩
    have hUcard : (P.suppU (l :: ls)).card = P.suppSize l.1 + (P.suppU ls).card := by
      simp only [suppU]; rw [card_union_of_disjoint hST, suppSize_eq]
    refine ⟨?_, by rw [hUcard, hU]; simp⟩
    -- sizes fit into the universe
    have hle : P.suppSize l.1 + (ls.map fun l => P.suppSize l.1).sum ≤ P.V := by
      rw [← hU, ← hUcard]; exact (card_le_univ _).trans (by simp)
    have key := card_and_mul (P.suppF l.1) (P.suppU ls) hST
      (fun a => P.evalLit (ext a) l = true) (fun a => ∀ l' ∈ ls, P.evalLit (ext a) l' = true)
      (fun a b h => by simp only [evalLit]; rw [P.evalVar_ext_congr l.1 a b h])
      (fun a b h => by
        refine forall₂_congr fun l' hl' => ?_
        simp only [evalLit]
        rw [P.evalVar_ext_congr l'.1 a b fun i hi => h i (P.mem_suppU.2 ⟨l', hl', hi⟩)])
    rw [hlit l List.mem_cons_self, hcard] at key
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have hfilter : (univ.filter fun a : Fin P.V → Bool => ∀ l' ∈ l :: ls, P.evalLit (ext a) l' = true) =
        univ.filter fun a => P.evalLit (ext a) l = true ∧ ∀ l' ∈ ls, P.evalLit (ext a) l' = true := by
      ext a; simp
    rw [hfilter]
    apply Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : (0:ℕ) < 2) P.V)
    rw [key]
    set s := P.suppSize l.1
    set t := (ls.map fun l => P.suppSize l.1).sum
    have e : P.V - (s + t) + P.V = (P.V - s) + (P.V - t) := by omega
    calc P.countLit l * 2 ^ (P.V - s) * ((ls.map P.countLit).prod * 2 ^ (P.V - t))
        = P.countLit l * (ls.map P.countLit).prod * 2 ^ ((P.V - s) + (P.V - t)) := by
          rw [pow_add]; ring
      _ = P.countLit l * (ls.map P.countLit).prod * 2 ^ (P.V - (s + t)) * 2 ^ P.V := by
          rw [← e, pow_add]; ring

theorem countVar_prod {i : ℕ} (hi : i < P.nodes.size) {args : List (Literal ℕ)}
    (hn : P.nodes[i] = .prod args) (hargs : ∀ l ∈ args, l.1 < P.V + i) :
    P.countVar (P.V + i) = (args.map P.countLit).prod := by
  rw [countVar, if_neg (by omega), node?_ext, Array.getElem?_eq_getElem hi, hn]
  simp only
  suffices h : ∀ (ls : List (Literal ℕ)) (c : ℕ), (∀ l ∈ ls, l.1 < P.V + i) →
      ls.foldl (fun acc l => if _ : l.1 < P.V + i then acc * (if l.2 then P.countVar l.1
        else 2 ^ P.suppSize l.1 - P.countVar l.1) else 0) c = c * (ls.map P.countLit).prod by
    simpa using h args 1 hargs
  intro ls
  induction ls with
  | nil => simp
  | cons l ls ih =>
    intro c h
    simp only [List.foldl_cons, dif_pos (h l List.mem_cons_self), List.map_cons, List.prod_cons]
    rw [ih _ fun l' hl' => h l' (List.mem_cons_of_mem _ hl')]
    simp only [countLit]; ring

theorem supp_prod_iff {i : ℕ} (hi : i < P.nodes.size) {args : List (Literal ℕ)}
    (hn : P.nodes[i] = .prod args) (hargs : ∀ l ∈ args, l.1 < P.V + i) (x : ℕ) :
    P.supp (P.V + i) x = true ↔ ∃ l ∈ args, P.supp l.1 x = true := by
  rw [supp, if_neg (by omega), node?_ext, Array.getElem?_eq_getElem hi, hn]
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨l, hl, h⟩; rw [dif_pos (hargs l hl)] at h; exact ⟨l, hl, h⟩
  · rintro ⟨l, hl, h⟩; exact ⟨l, hl, by rw [dif_pos (hargs l hl)]; exact h⟩

theorem countVar_sum {i : ℕ} (hi : i < P.nodes.size) {x y : Literal ℕ}
    (hn : P.nodes[i] = .sum x y) (hx : x.1 < P.V + i) (hy : y.1 < P.V + i) :
    P.countVar (P.V + i) = P.countLit x * 2 ^ (P.suppSize (P.V + i) - P.suppSize x.1) +
      P.countLit y * 2 ^ (P.suppSize (P.V + i) - P.suppSize y.1) := by
  rw [countVar, if_neg (by omega), node?_ext, Array.getElem?_eq_getElem hi, hn]
  simp [hx, hy, countLit]

theorem supp_sum_iff {i : ℕ} (hi : i < P.nodes.size) {x y : Literal ℕ}
    (hn : P.nodes[i] = .sum x y) (hx : x.1 < P.V + i) (hy : y.1 < P.V + i) (z : ℕ) :
    P.supp (P.V + i) z = true ↔ P.supp x.1 z = true ∨ P.supp y.1 z = true := by
  rw [supp, if_neg (by omega), node?_ext, Array.getElem?_eq_getElem hi, hn]
  simp [hx, hy]

/-- Counting lemma for variables. -/
theorem card_mods (hP : P.WF) (v : ℕ) (hv : v < P.numVars) :
    (P.modsLit (v, true)).card = P.countVar v * 2 ^ (P.V - P.suppSize v) := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  by_cases hvV : v < P.V
  · have hc : P.countVar v = 1 := by rw [countVar]; simp [hvV]
    have hs : P.suppSize v = 1 := by
      rw [suppSize_eq]
      have : P.suppF v = {⟨v, hvV⟩} := by
        ext j; simp only [suppF, mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
        rw [supp]; simp [hvV]
      rw [this, card_singleton]
    have hm : P.modsLit (v, true) = univ.filter fun a : Fin P.V → Bool => a ⟨v, hvV⟩ = true := by
      ext a; simp only [modsLit, evalLit, mem_filter, mem_univ, true_and]
      rw [evalVar]; simp [hvV, ext]
    rw [hc, hs, hm, card_coord_true, one_mul]
  obtain ⟨i, rfl⟩ : ∃ i, v = P.V + i := ⟨v - P.V, by omega⟩
  have hi : i < P.nodes.size := by simp [numVars] at hv; omega
  have hargs := hP.args_lt i hi
  have hlit : ∀ l ∈ Node.args P.nodes[i],
      (P.modsLit l).card = P.countLit l * 2 ^ (P.V - P.suppSize l.1) := fun l hl =>
    P.card_modsLit l (ih l.1 (hargs l hl) (by simp [numVars]; have := hargs l hl; omega))
  have hdisj := hP.prod_disjoint i hi
  have hexcl := hP.sum_excl i hi
  generalize hn : P.nodes[i] = n at hargs hlit hdisj hexcl
  cases n with
  | prod args =>
    simp only [Node.args] at hargs hlit
    obtain ⟨hcard, hU⟩ := P.card_all args hlit (hdisj args rfl)
    have hm : P.modsLit (P.V + i, true) =
        univ.filter fun a : Fin P.V → Bool => ∀ l ∈ args, P.evalLit (ext a) l = true := by
      ext a
      simp only [modsLit, evalLit, mem_filter, mem_univ, true_and, P.evalVar_prod _ hi hn,
        beq_true, List.all_eq_true]
      exact forall₂_congr fun l hl => by simp [hargs l hl]
    have hs : P.suppSize (P.V + i) = (args.map fun l => P.suppSize l.1).sum := by
      rw [← hU, suppSize_eq]; congr 1; ext j
      rw [mem_suppF, P.supp_prod_iff hi hn hargs, P.mem_suppU]
      simp [mem_suppF]
    rw [hm, hcard, P.countVar_prod hi hn hargs, hs]
  | sum x y =>
    simp only [Node.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hargs hlit
    have hm : P.modsLit (P.V + i, true) = P.modsLit x ∪ P.modsLit y := by
      ext a
      simp only [modsLit, evalLit, mem_filter, mem_univ, true_and, mem_union,
        P.evalVar_sum _ hi hn, dif_pos hargs.1, dif_pos hargs.2, beq_true, Bool.or_eq_true]
    have hd : Disjoint (P.modsLit x) (P.modsLit y) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [modsLit, mem_filter, mem_univ, true_and] at ha hb
      exact hexcl x y rfl (ext a) ⟨ha, hb⟩
    have hsub : ∀ z, P.supp x.1 z = true ∨ P.supp y.1 z = true ↔ P.supp (P.V + i) z = true :=
      fun z => (P.supp_sum_iff hi hn hargs.1 hargs.2 z).symm
    have hsx : P.suppSize x.1 ≤ P.suppSize (P.V + i) := by
      rw [suppSize_eq, suppSize_eq]; apply card_le_card
      intro j hj; rw [mem_suppF] at hj ⊢; exact (hsub j).1 (Or.inl hj)
    have hsy : P.suppSize y.1 ≤ P.suppSize (P.V + i) := by
      rw [suppSize_eq, suppSize_eq]; apply card_le_card
      intro j hj; rw [mem_suppF] at hj ⊢; exact (hsub j).1 (Or.inr hj)
    have hsV := P.suppSize_le (P.V + i)
    rw [hm, card_union_of_disjoint hd, hlit.1, hlit.2, P.countVar_sum hi hn hargs.1 hargs.2]
    set s := P.suppSize (P.V + i)
    rw [add_mul, mul_assoc, mul_assoc, ← pow_add, ← pow_add]
    congr 3 <;> omega

end Pog

end CountCatcher
