import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.List.Sort
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.Algebra.Group.Pointwise.Set.Card

/-!
# Burnside's lemma over the symmetric group, grouped by cycle type

Generic, independent of the checker. For an action of `Perm (Fin n)` on a finite type `X`, the
number of fixed points of `g` depends only on the conjugacy class of `g`, that is on its cycle
type. Burnside's sum over the `n!` permutations therefore regroups into one term per cycle type:

    orbits · n! = Σ over cycle types l of classSize n l · |fixedBy X (rep n l)|,

where `rep n l` is a concrete representative (cycles on consecutive blocks of `Fin n`,
`cycleType_rep`) and `classSize n l` is Mathlib's class size (`Equiv.Perm.card_of_cycleType`)
as a computable function (`card_cycleType_eq_classSize`).

A list of cycle types is complete when the class sizes add up to `n!`: the fibres of
`cycleType` are disjoint, so they then cover the group (`card_orbits_mul_factorial`). The final
lemma `card_orbits_eq` takes the fixed-point counts as a list `L` of pairs (cycle type, count)
and a Boolean check `checkClasses n N L` (cycle types valid, sorted and distinct, class sizes
summing to `n!`, Burnside sum `N · n!`), which `decide` evaluates for concrete `L`.

Cycle types are lists of the cycle lengths `≥ 2` (fixed points are not listed), in decreasing
order; the identity is `[]`.
-/

open Equiv Equiv.Perm MulAction
open scoped Nat

namespace CountCatcher.CycleType

/-! ## Representatives -/

/-- The elements `s, s + 1, …, s + k - 1` of `Fin n` (fewer if `n < s + k`). -/
def block (n s k : ℕ) : List (Fin n) := ((List.finRange n).drop s).take k

theorem block_nodup (n s k : ℕ) : (block n s k).Nodup :=
  (List.nodup_finRange n).sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))

theorem length_block {n s k : ℕ} (h : s + k ≤ n) : (block n s k).length = k := by
  simp only [block, List.length_take, List.length_drop, List.length_finRange]
  omega

theorem val_of_mem_block {n s k : ℕ} {x : Fin n} (h : x ∈ block n s k) :
    s ≤ x.val ∧ x.val < s + k := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  simp only [block, List.length_take, List.length_drop, List.length_finRange] at hi
  simp only [block, List.getElem_take, List.getElem_drop, List.getElem_finRange, Fin.val_cast]
  omega

/-- Cycles on the consecutive blocks of the lengths `l`, the first block starting at `s`. -/
def repFrom (n : ℕ) : ℕ → List ℕ → Perm (Fin n)
  | _, [] => 1
  | s, k :: l => (block n s k).formPerm * repFrom n (s + k) l

/-- The representative of the cycle type `l = [k₁, k₂, …]`: cycles on the blocks
    `0, …, k₁ - 1`, then `k₁, …, k₁ + k₂ - 1`, and so on; the remaining points are fixed. -/
def rep (n : ℕ) (l : List ℕ) : Perm (Fin n) := repFrom n 0 l

theorem repFrom_apply_of_lt {n : ℕ} :
    ∀ (s : ℕ) (l : List ℕ) (x : Fin n), x.val < s → repFrom n s l x = x
  | _, [], _, _ => rfl
  | s, k :: l, x, h => by
    rw [repFrom, Perm.mul_apply, repFrom_apply_of_lt (s + k) l x (by omega)]
    exact List.formPerm_apply_of_notMem fun hx => by
      have := val_of_mem_block hx
      omega

theorem cycleType_repFrom {n : ℕ} :
    ∀ (s : ℕ) (l : List ℕ), (∀ k ∈ l, 2 ≤ k) → s + l.sum ≤ n →
      (repFrom n s l).cycleType = (l : Multiset ℕ)
  | _, [], _, _ => cycleType_one
  | s, k :: l, h2, hs => by
    have hk : 2 ≤ k := h2 k List.mem_cons_self
    simp only [List.sum_cons] at hs
    have hsk : s + k ≤ n := by omega
    have hdisj : Disjoint (block n s k).formPerm (repFrom n (s + k) l) := by
      intro x
      by_cases hx : x.val < s + k
      · exact Or.inr (repFrom_apply_of_lt _ _ x hx)
      · exact Or.inl (List.formPerm_apply_of_notMem fun hm => hx (val_of_mem_block hm).2)
    have hnd := block_nodup n s k
    have hlen := length_block hsk
    rw [repFrom, hdisj.cycleType_mul,
      cycleType_repFrom (s + k) l (fun j hj => h2 j (List.mem_cons_of_mem _ hj)) (by omega),
      (List.isCycle_formPerm hnd (by rw [hlen]; exact hk)).cycleType,
      List.support_formPerm_of_nodup _ hnd (fun x hx => by
        have := congrArg List.length hx
        rw [hlen] at this
        simp at this
        omega),
      List.toFinset_card_of_nodup hnd, hlen]
    simp

theorem cycleType_rep {n : ℕ} {l : List ℕ} (h2 : ∀ k ∈ l, 2 ≤ k) (hs : l.sum ≤ n) :
    (rep n l).cycleType = (l : Multiset ℕ) :=
  cycleType_repFrom 0 l h2 (by omega)

/-! ## Class sizes -/

/-- The number of permutations of `Fin n` with cycle type `l` (Mathlib's
    `Equiv.Perm.card_of_cycleType`, over lists). -/
def classSize (n : ℕ) (l : List ℕ) : ℕ :=
  n ! / ((n - l.sum)! * l.prod * (l.dedup.map fun k => (l.count k)!).prod)

theorem card_cycleType_eq_classSize {n : ℕ} {l : List ℕ} (h2 : ∀ k ∈ l, 2 ≤ k)
    (hs : l.sum ≤ n) :
    (Finset.univ.filter fun g : Perm (Fin n) => g.cycleType = (l : Multiset ℕ)).card =
      classSize n l := by
  rw [card_of_cycleType, if_pos ⟨by simpa using hs, by simpa using h2⟩]
  simp only [Fintype.card_fin, Multiset.sum_coe, Multiset.prod_coe, Multiset.coe_count,
    classSize]
  congr 3

/-! ## Burnside by cycle type -/

section Burnside

variable {n : ℕ} {X : Type*} [MulAction (Perm (Fin n)) X]

theorem card_fixedBy_conj (g h : Perm (Fin n)) :
    Nat.card (fixedBy X (h * g * h⁻¹)) = Nat.card (fixedBy X g) := by
  rw [← MulAction.smul_fixedBy X g h, Set.natCard_smul_set]

/-- Permutations of the same cycle type have equally many fixed points. -/
theorem card_fixedBy_of_cycleType_eq {g h : Perm (Fin n)} (hc : g.cycleType = h.cycleType) :
    Nat.card (fixedBy X g) = Nat.card (fixedBy X h) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 hc)
  exact (card_fixedBy_conj g c).symm

/-- Burnside's lemma regrouped by cycle type, for a list `T` of valid, pairwise distinct cycle
    types whose class sizes add up to `n!` (so that it lists every cycle type). -/
theorem card_orbits_mul_factorial [Finite X] (T : List (List ℕ))
    (hv : ∀ l ∈ T, (∀ k ∈ l, 2 ≤ k) ∧ l.sum ≤ n)
    (hnd : (T.map Multiset.ofList).Nodup)
    (hsum : (T.map (classSize n)).sum = n !) :
    Nat.card (orbitRel.Quotient (Perm (Fin n)) X) * n ! =
      (T.map fun l => classSize n l * Nat.card (fixedBy X (rep n l))).sum := by
  classical
  have : Fintype X := Fintype.ofFinite X
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (Perm (Fin n)) X
  rw [Fintype.card_perm, Fintype.card_fin] at hB
  simp only [Fintype.card_eq_nat_card] at hB
  rw [← hB]
  set M := (T.map Multiset.ofList).toFinset with hM
  let fib : Multiset ℕ → Finset (Perm (Fin n)) := fun m => Finset.univ.filter fun g =>
    g.cycleType = m
  have hfib : ∀ l ∈ T, (fib l).card = classSize n l := fun l hl =>
    card_cycleType_eq_classSize (hv l hl).1 (hv l hl).2
  -- the fibres of the listed cycle types cover the group
  have hcov : ∀ g : Perm (Fin n), g.cycleType ∈ M := by
    have hcard : (M.biUnion fib).card = Fintype.card (Perm (Fin n)) := by
      rw [Finset.card_biUnion]
      · rw [hM, List.sum_toFinset _ hnd, List.map_map, Fintype.card_perm, Fintype.card_fin,
          ← hsum]
        congr 1
        exact List.map_congr_left fun l hl => hfib l hl
      · intro m _ m' _ hmm'
        simp only [Function.onFun, fib]
        rw [Finset.disjoint_filter]
        intro g _ h1 h2
        exact hmm' (h1.symm.trans h2)
    have huniv := Finset.eq_univ_of_card _ hcard
    intro g
    obtain ⟨m, hm, hgm⟩ := Finset.mem_biUnion.1 (huniv ▸ Finset.mem_univ g)
    simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hgm
    rw [hgm]
    exact hm
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := M) (g := cycleType)
    (fun g _ => hcov g), hM, List.sum_toFinset _ hnd, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  simp only [Function.comp_apply]
  rw [Finset.sum_congr rfl (g := fun _ => Nat.card (fixedBy X (rep n l))), Finset.sum_const,
    smul_eq_mul, ← hfib l hl]
  intro g hg
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
  exact card_fixedBy_of_cycleType_eq (hg.trans (cycleType_rep (hv l hl).1 (hv l hl).2).symm)

/-- The Boolean side conditions of `card_orbits_eq`: every cycle type is valid (parts `≥ 2`,
    sum `≤ n`) and sorted decreasingly, the cycle types are distinct, their class sizes add up
    to `n!`, and Burnside's sum is `N · n!`. -/
def checkClasses (n N : ℕ) (L : List (List ℕ × ℕ)) : Bool :=
  L.all (fun p => p.1.all (2 ≤ ·) && decide (p.1.sum ≤ n) && decide (p.1.Pairwise (· ≥ ·))) &&
    decide (L.map Prod.fst).Nodup &&
    (L.map fun p => classSize n p.1).sum == n ! &&
    (L.map fun p => classSize n p.1 * p.2).sum == N * n !

/-- The number of orbits from one fixed-point count per cycle type: `L` lists pairs
    (cycle type `l`, number of points fixed by `rep n l`). -/
theorem card_orbits_eq [Finite X] (N : ℕ) (L : List (List ℕ × ℕ))
    (hfix : ∀ p ∈ L, Nat.card (fixedBy X (rep n p.1)) = p.2)
    (hc : checkClasses n N L = true) :
    Nat.card (orbitRel.Quotient (Perm (Fin n)) X) = N := by
  simp only [checkClasses, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
    at hc
  obtain ⟨⟨⟨hv, hnd⟩, hsum⟩, hB⟩ := hc
  have hv' : ∀ l ∈ L.map Prod.fst, (∀ k ∈ l, 2 ≤ k) ∧ l.sum ≤ n := by
    intro l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
    have := hv p hp
    exact ⟨this.1.1, this.1.2⟩
  have hnd' : ((L.map Prod.fst).map Multiset.ofList).Nodup := by
    refine hnd.map_on fun l hl l' hl' h => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
    obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hl'
    have s := (hv p hp).2
    have s' := (hv p' hp').2
    exact List.Perm.eq_of_pairwise' s s' (Multiset.coe_eq_coe.1 h)
  have h := card_orbits_mul_factorial (X := X) (L.map Prod.fst) hv' hnd'
    (by rw [List.map_map]; exact hsum)
  rw [List.map_map] at h
  rw [List.map_congr_left (g := fun p => classSize n p.1 * p.2) (fun p hp => by
    simp only [Function.comp_apply, hfix p hp]), hB] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos n) h

end Burnside

end CountCatcher.CycleType
