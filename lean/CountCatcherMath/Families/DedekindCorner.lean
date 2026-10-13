import CountCatcherMath.Split
import CountCatcherMath.Families.Dedekind
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.GroupTheory.Perm.Fin

/-!
# Dedekind numbers by the classes of the lower corner

A monotone `f` on `n + 2` Boolean variables is four monotone functions on the `n` inner
variables (the values of the two top variables `n`, `n + 1`). Fixing the lower corner
`f00 = a` (the points `u < 2 ^ n`, bits `n` and `n + 1` clear) splits the models of
`Dedekind.cnf (n + 2)` into the leaves `cube (Dedekind.cnf (n + 2)) (lits n a)`, where `a` is a
mask (bit `u` of `a` is the value at the point `u`) and `lits n a` fixes the `2 ^ n` corner
points by unit literals (`card_eq_sum_corner`, `card_monotone_succ_succ`). The leaf of a
non-monotone `a` is empty (`leafCount_eq_zero`), the leaf of a monotone one is not
(`leafCount_pos`).

`S_n` permutes the inner coordinates. On masks it acts by `act n σ m` (bit `u` of the result is
bit `ptMap n σ u` of `m`), and the leaf count is invariant (`leafCount_act`): the map
`x ↦ x ∘ (point permutation of σ extended by the identity on n, n + 1)` carries the models of
one leaf injectively into the other.

Completeness by counting (`card_eq_of_classes`): chunks of pairs `(r, o)` (representative mask,
orbit size), such that every `r` is a monotone mask and the smallest of its orbit, the `r` are
strictly increasing (so pairwise inequivalent), `o · |Stab r| = n!`, and the `o` add up to
`M(n)` (a certified count of `Dedekind.cnf n`). Then the orbits are disjoint, have the claimed
sizes and cover the monotone masks, so `M(n + 2)` is the sum over the chunks of `Σ o · c`, `c`
the leaf count of `r` (`chunkSum_cons`: the leaf theorems, one per class; a split class by a
`SplitTree` of sub-cubes, `leafCount_of_tree`).

The per-representative side check `repOk` depends only on the class list. It runs over all `n!`
permutations as a walk of adjacent transpositions `path` (checked once to visit every
permutation exactly once, `pathOk`). Each step is one delta swap of the current mask
(`deltaSwap s M m`, five `Nat` operations) with the shift and mask of a table `T` (checked once
against the point permutation, `tableOk`); monotonicity is `n` shifted masks (`monoOk`, table
`Ls`, `monoTableOk`). So the side check costs `n!` delta swaps per representative and evaluates
with `decide +kernel`, in chunks of representatives (`hreps` is stated per chunk; for `n = 6`
about 0.2 s of kernel time per representative).
-/

open Std.Sat Equiv
open scoped Nat

namespace CountCatcher.DedekindCorner

/-! ## Corner literals and the partition -/

/-- Unit literals fixing the variables `0, …, K - 1` to the bits of the mask `m`. -/
def cornerLits (K m : ℕ) : List (ℕ × Bool) := (List.range K).map fun u => (u, m.testBit u)

/-- The lower corner of `Dedekind.cnf (n + 2)`: the points `u < 2 ^ n` get bit `u` of `m`. -/
def lits (n m : ℕ) : List (ℕ × Bool) := cornerLits (2 ^ n) m

theorem card_cube_congr {V : ℕ} {F : CNF ℕ} {ls ls' : List (ℕ × Bool)}
    (h : ∀ v : ℕ → Bool, (ls.all fun l => v l.1 == l.2) = (ls'.all fun l => v l.1 == l.2)) :
    Fintype.card {x : Fin V → Bool // (cube F ls).eval (ext x) = true} =
      Fintype.card {x : Fin V → Bool // (cube F ls').eval (ext x) = true} :=
  Fintype.card_congr (Equiv.subtypeEquivRight fun x => by rw [eval_cube, eval_cube, h])

theorem cornerLits_succ (K m : ℕ) :
    cornerLits (K + 1) m = cornerLits K m ++ [(K, m.testBit K)] := by
  simp [cornerLits, List.range_succ]

theorem cornerLits_two_pow_add (K m : ℕ) : cornerLits K (2 ^ K + m) = cornerLits K m := by
  unfold cornerLits
  apply List.map_congr_left
  intro u hu
  rw [List.mem_range] at hu
  rw [Nat.testBit_two_pow_add_gt hu]

theorem all_append_one (ls : List (ℕ × Bool)) (l : ℕ × Bool) (v : ℕ → Bool) :
    ((ls ++ [l]).all fun l => v l.1 == l.2) = ((l :: ls).all fun l => v l.1 == l.2) := by
  simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  rw [Bool.and_comm]

/-- The models of `F` split by the values of the variables `0, …, K - 1`. -/
theorem card_eq_sum_corner (V : ℕ) (F : CNF ℕ) (K : ℕ) :
    Fintype.card {x : Fin V → Bool // F.eval (ext x) = true} =
      ∑ m ∈ Finset.range (2 ^ K),
        Fintype.card {x : Fin V → Bool // (cube F (cornerLits K m)).eval (ext x) = true} := by
  induction K with
  | zero =>
    simp only [pow_zero, Finset.range_one, Finset.sum_singleton]
    exact (card_cube_nil V F).symm
  | succ K ih =>
    rw [ih, pow_succ, mul_two, Finset.sum_range_add, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_range] at hm
    rw [cornerLits_succ, cornerLits_succ, cornerLits_two_pow_add, Nat.testBit_two_pow_add_eq,
      Nat.testBit_lt_two_pow hm, Bool.not_false, card_split V F (cornerLits K m) K, add_comm]
    congr 1
    · exact card_cube_congr fun v => (all_append_one _ _ v).symm
    · exact card_cube_congr fun v => (all_append_one _ _ v).symm

/-! ## Leaves -/

/-- The mask `m` is monotone on `n` variables. -/
def IsMono (n m : ℕ) : Prop :=
  ∀ u < 2 ^ n, ∀ b < n, u.testBit b = false → m.testBit u = true → m.testBit (u ||| 2 ^ b) = true

instance (n m : ℕ) : Decidable (IsMono n m) := by unfold IsMono; infer_instance

/-- The leaf count of the mask `m`: the models of `Dedekind.cnf (n + 2)` whose lower corner is
    `m` (by `leafEquiv`, the monotone functions on `n + 2` variables with lower corner `m`). -/
def leafCount (n m : ℕ) : ℕ :=
  Fintype.card
    {x : Fin (2 ^ (n + 2)) → Bool // (cube (Dedekind.cnf (n + 2)) (lits n m)).eval (ext x) = true}

theorem all_cornerLits {K m : ℕ} {v : ℕ → Bool} :
    ((cornerLits K m).all fun l => v l.1 == l.2) = true ↔ ∀ u < K, v u = m.testBit u := by
  simp [cornerLits, List.all_map]

theorem two_pow_lt_two_pow_add_two (n : ℕ) : 2 ^ n < 2 ^ (n + 2) :=
  Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem or_two_pow_lt {u b k : ℕ} (hu : u < 2 ^ k) (hb : b < k) : u ||| 2 ^ b < 2 ^ k :=
  Nat.or_lt_two_pow hu (Nat.pow_lt_pow_right (by norm_num) hb)

theorem testBit_eq_false_of_lt {x i k : ℕ} (hx : x < 2 ^ k) (hi : k ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))

theorem isMono_of_model {n m : ℕ} {x : Fin (2 ^ (n + 2)) → Bool}
    (hx : (cube (Dedekind.cnf (n + 2)) (lits n m)).eval (ext x) = true) : IsMono n m := by
  rw [eval_cube, Bool.and_eq_true, Dedekind.eval_iff, lits, all_cornerLits] at hx
  obtain ⟨hF, hL⟩ := hx
  intro u hu b hb hub hm
  have hu' : u < 2 ^ (n + 2) := lt_trans hu (two_pow_lt_two_pow_add_two n)
  rw [← hL u hu] at hm
  rw [← hL _ (or_two_pow_lt hu hb)]
  exact hF u hu' b (by omega) hub hm

/-- The leaf of a non-monotone mask is empty. -/
theorem leafCount_eq_zero {n m : ℕ} (h : ¬ IsMono n m) : leafCount n m = 0 := by
  rw [leafCount, Fintype.card_eq_zero_iff]
  exact ⟨fun x => h (isMono_of_model x.2)⟩

/-- The leaf of a monotone mask is not empty: `m` below, constant `true` above. -/
theorem leafCount_pos {n m : ℕ} (h : IsMono n m) : 0 < leafCount n m := by
  rw [leafCount, Fintype.card_pos_iff]
  let x : Fin (2 ^ (n + 2)) → Bool := fun u => if (u : ℕ) < 2 ^ n then m.testBit u else true
  have hext : ∀ u < 2 ^ (n + 2), ext x u = if u < 2 ^ n then m.testBit u else true := by
    intro u hu; simp [ext, hu, x]
  refine ⟨⟨x, ?_⟩⟩
  rw [eval_cube, Bool.and_eq_true, Dedekind.eval_iff, lits, all_cornerLits]
  constructor
  · intro u hu b hb hub hv
    rw [hext _ (or_two_pow_lt hu hb)]
    rw [hext _ hu] at hv
    by_cases h2 : u ||| 2 ^ b < 2 ^ n
    · have hu2 : u < 2 ^ n := lt_of_le_of_lt Nat.left_le_or h2
      have hb2 : b < n := by
        by_contra hbn
        have h3 : 2 ^ n ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h4 : 2 ^ b ≤ u ||| 2 ^ b := Nat.right_le_or
        omega
      rw [if_pos h2]
      rw [if_pos hu2] at hv
      exact h u hu2 b hb2 hub hv
    · rw [if_neg h2]
  · intro u hu
    rw [hext u (lt_trans hu (two_pow_lt_two_pow_add_two n)), if_pos hu]

theorem leafCount_ne_zero_iff {n m : ℕ} : leafCount n m ≠ 0 ↔ IsMono n m :=
  ⟨fun h => by_contra fun h' => h (leafCount_eq_zero h'), fun h => (leafCount_pos h).ne'⟩

/-- A cube fixing every variable of `Dedekind.cnf n` has one model if the mask is monotone,
    else none. -/
theorem card_cube_full (n m : ℕ) :
    Fintype.card {x : Fin (2 ^ n) → Bool //
      (cube (Dedekind.cnf n) (cornerLits (2 ^ n) m)).eval (ext x) = true} =
      if IsMono n m then 1 else 0 := by
  have key : ∀ x : Fin (2 ^ n) → Bool,
      (cube (Dedekind.cnf n) (cornerLits (2 ^ n) m)).eval (ext x) = true ↔
        IsMono n m ∧ x = fun u : Fin (2 ^ n) => m.testBit u := by
    intro x
    rw [eval_cube, Bool.and_eq_true, Dedekind.eval_iff, all_cornerLits]
    have hx : (∀ u < 2 ^ n, ext x u = m.testBit u) ↔ x = fun u : Fin (2 ^ n) => m.testBit u := by
      constructor
      · intro h
        funext u
        have := h u u.2
        simpa [ext, u.2] using this
      · rintro rfl u hu
        simp [ext, hu]
    rw [hx]
    constructor
    · rintro ⟨hF, rfl⟩
      refine ⟨fun u hu b hb hub hm => ?_, rfl⟩
      have := hF u hu b hb hub (by simp [ext, hu, hm])
      simpa [ext, or_two_pow_lt hu hb] using this
    · rintro ⟨hm, rfl⟩
      refine ⟨fun u hu b hb hub hv => ?_, rfl⟩
      simp only [ext, hu, dite_true] at hv
      simp only [ext, or_two_pow_lt hu hb, dite_true]
      exact hm u hu b hb hub hv
  split_ifs with hm
  · rw [Fintype.card_congr (Equiv.subtypeEquivRight fun x => (key x).trans (and_iff_right hm))]
    exact Fintype.card_subtype_eq _
  · rw [Fintype.card_eq_zero_iff]
    exact ⟨fun x => hm ((key x.1).1 x.2).1⟩

/-- The monotone masks. -/
def monoMasks (n : ℕ) : Finset ℕ := (Finset.range (2 ^ 2 ^ n)).filter (IsMono n)

/-- `M(n)` counts the monotone masks. -/
theorem card_monotone_eq (n : ℕ) :
    Nat.card {f : (Fin n → Bool) → Bool // Monotone f} = (monoMasks n).card := by
  rw [← Nat.card_congr (Dedekind.equiv (n := n)), Nat.card_eq_fintype_card,
    card_eq_sum_corner (2 ^ n) (Dedekind.cnf n) (2 ^ n), monoMasks, Finset.card_filter]
  exact Finset.sum_congr rfl fun m _ => card_cube_full n m

/-- `M(n + 2)` is the sum of the leaf counts over the monotone masks. -/
theorem card_monotone_succ_succ (n : ℕ) :
    Nat.card {f : (Fin (n + 2) → Bool) → Bool // Monotone f} =
      ∑ m ∈ monoMasks n, leafCount n m := by
  rw [← Nat.card_congr (Dedekind.equiv (n := n + 2)), Nat.card_eq_fintype_card,
    card_eq_sum_corner (2 ^ (n + 2)) (Dedekind.cnf (n + 2)) (2 ^ n), monoMasks,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  split_ifs with h
  · rfl
  · exact leafCount_eq_zero h

/-! ## Leaf theorems (for `count_models … via`) -/

theorem leaf_card_of_check {n : ℕ} {ls : List (ℕ × Bool)} {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (2 ^ (n + 2)) (cube (Dedekind.cnf (n + 2)) ls) pogStr lratStr N = true) :
    Fintype.card
      {x : Fin (2 ^ (n + 2)) → Bool // (cube (Dedekind.cnf (n + 2)) ls).eval (ext x) = true} = N :=
  checkAll_sound h

theorem leaf_card_of_checkAC {n : ℕ} {ls : List (ℕ × Bool)} {pogStr : String} {N : ℕ}
    (h : checkAllAC (2 ^ (n + 2)) (cube (Dedekind.cnf (n + 2)) ls) pogStr N = true)
    (hB : (fwdCnfOf (cube (Dedekind.cnf (n + 2)) ls) pogStr).Unsat) :
    Fintype.card
      {x : Fin (2 ^ (n + 2)) → Bool // (cube (Dedekind.cnf (n + 2)) ls).eval (ext x) = true} = N :=
  checkAllAC_sound h hB

theorem leaf_card_of_unsat {n : ℕ} {ls : List (ℕ × Bool)}
    (h : (cube (Dedekind.cnf (n + 2)) ls).Unsat) :
    Fintype.card
      {x : Fin (2 ^ (n + 2)) → Bool // (cube (Dedekind.cnf (n + 2)) ls).eval (ext x) = true} = 0 :=
  card_eq_zero_of_unsat h

/-! ## Coordinate permutations on points and masks -/

variable {n : ℕ}

theorem testBit_binEquiv {k : ℕ} (y : Fin k → Bool) (i : ℕ) :
    (binEquiv k y : ℕ).testBit i = if h : i < k then y ⟨i, h⟩ else false := by
  split_ifs with h
  · have := Dedekind.binEquiv_symm_apply (binEquiv k y) ⟨i, h⟩
    rw [Equiv.symm_apply_apply] at this
    exact this.symm
  · exact testBit_eq_false_of_lt (binEquiv k y).2 (by omega)

/-- The point whose bit `i < n` is bit `τ i` of `u` (the point `u ∘ τ`). -/
def ptMap (n : ℕ) (τ : Fin n → Fin n) (u : ℕ) : ℕ := (binEquiv n fun i => u.testBit (τ i) : ℕ)

theorem testBit_ptMap (τ : Fin n → Fin n) (u i : ℕ) :
    (ptMap n τ u).testBit i = if h : i < n then u.testBit (τ ⟨i, h⟩) else false :=
  testBit_binEquiv _ _

theorem ptMap_lt (τ : Fin n → Fin n) (u : ℕ) : ptMap n τ u < 2 ^ n := (binEquiv n _).2

theorem ptMap_ptMap (τ τ' : Fin n → Fin n) (u : ℕ) :
    ptMap n τ (ptMap n τ' u) = ptMap n (τ' ∘ τ) u := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ptMap, testBit_ptMap]
  split_ifs with h
  · rw [testBit_ptMap, dif_pos (τ _).2]
    rfl
  · rfl

theorem ptMap_id {u : ℕ} (hu : u < 2 ^ n) : ptMap n id u = u := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ptMap]
  split_ifs with h
  · rfl
  · exact (testBit_eq_false_of_lt hu (by omega)).symm

theorem ptMap_binEquiv (τ : Fin n → Fin n) (z : Fin n → Bool) :
    ptMap n τ (binEquiv n z) = binEquiv n (z ∘ τ) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ptMap, testBit_binEquiv]
  split_ifs with h
  · rw [testBit_binEquiv, dif_pos (τ _).2]
    rfl
  · rfl

/-- The mask action: bit `u < 2 ^ n` of `act n σ m` is bit `ptMap n σ u` of `m`, that is
    `(σ • f) x = f (x ∘ σ)` for the function `f` of `m`. -/
def act (n : ℕ) (σ : Perm (Fin n)) (m : ℕ) : ℕ :=
  (binEquiv (2 ^ n) fun u => m.testBit (ptMap n σ u) : ℕ)

theorem testBit_act (σ : Perm (Fin n)) (m u : ℕ) :
    (act n σ m).testBit u = if u < 2 ^ n then m.testBit (ptMap n σ u) else false := by
  rw [act, testBit_binEquiv]
  split_ifs <;> rfl

theorem act_lt (σ : Perm (Fin n)) (m : ℕ) : act n σ m < 2 ^ 2 ^ n := (binEquiv _ _).2

theorem act_mul (σ τ : Perm (Fin n)) (m : ℕ) : act n σ (act n τ m) = act n (σ * τ) m := by
  apply Nat.eq_of_testBit_eq
  intro u
  rw [testBit_act, testBit_act, if_pos (ptMap_lt _ _), testBit_act]
  split_ifs with h
  · rw [ptMap_ptMap, Perm.coe_mul]
  · rfl

theorem act_one {m : ℕ} (hm : m < 2 ^ 2 ^ n) : act n 1 m = m := by
  apply Nat.eq_of_testBit_eq
  intro u
  rw [testBit_act]
  split_ifs with h
  · rw [Perm.coe_one, ptMap_id h]
  · exact (testBit_eq_false_of_lt hm (by omega)).symm

theorem act_inv_act (σ : Perm (Fin n)) {m : ℕ} (hm : m < 2 ^ 2 ^ n) : act n σ⁻¹ (act n σ m) = m := by
  rw [act_mul, inv_mul_cancel, act_one hm]

/-! ## The leaf as a set of monotone functions -/

/-- The point `y` of the inner cube in the lower corner (bits `n` and `n + 1` clear). -/
def lowPt (y : Fin n → Bool) : Fin (n + 2) → Bool :=
  fun i => if h : (i : ℕ) < n then y ⟨i, h⟩ else false

theorem binEquiv_lowPt (y : Fin n → Bool) :
    (binEquiv (n + 2) (lowPt y) : ℕ) = binEquiv n y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_binEquiv, testBit_binEquiv]
  by_cases hi : i < n
  · rw [dif_pos (by omega), dif_pos hi]
    simp [lowPt, hi]
  · rw [dif_neg hi]
    split_ifs with h
    · simp [lowPt, hi]
    · rfl

/-- The models of the leaf of `m` are the monotone functions on `n + 2` variables whose lower
    corner is `m`: the value at the point `y` of the inner cube is bit `y` of `m`. -/
def leafEquiv (n m : ℕ) :
    {x : Fin (2 ^ (n + 2)) → Bool //
      (cube (Dedekind.cnf (n + 2)) (lits n m)).eval (ext x) = true} ≃
      {f : (Fin (n + 2) → Bool) → Bool //
        Monotone f ∧ ∀ y : Fin n → Bool, f (lowPt y) = m.testBit (binEquiv n y)} :=
  Equiv.subtypeEquiv (Equiv.arrowCongr (binEquiv (n + 2)).symm (Equiv.refl Bool)) fun x => by
    rw [eval_cube, Bool.and_eq_true, Dedekind.model_iff, lits, all_cornerLits]
    apply and_congr Iff.rfl
    have hpt : ∀ y : Fin n → Bool, binEquiv (n + 2) (lowPt y) =
        ⟨binEquiv n y, lt_trans (binEquiv n y).2 (two_pow_lt_two_pow_add_two n)⟩ :=
      fun y => Fin.ext (binEquiv_lowPt y)
    simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.refl_apply, Function.comp_apply]
    constructor
    · intro h y
      rw [hpt, ← h _ (binEquiv n y).2]
      simp [ext, lt_trans (binEquiv n y).2 (two_pow_lt_two_pow_add_two n)]
    · intro h u hu
      have := h ((binEquiv n).symm ⟨u, hu⟩)
      rw [hpt, Equiv.apply_symm_apply] at this
      simp only at this
      simp [ext, lt_trans hu (two_pow_lt_two_pow_add_two n), this]

/-- The leaf count is the number of monotone functions with the given lower corner. -/
theorem leafCount_eq_card (n m : ℕ) :
    leafCount n m = Nat.card {f : (Fin (n + 2) → Bool) → Bool //
      Monotone f ∧ ∀ y : Fin n → Bool, f (lowPt y) = m.testBit (binEquiv n y)} := by
  rw [leafCount, ← Nat.card_eq_fintype_card, Nat.card_congr (leafEquiv n m)]

/-! ## Invariance of the leaf count -/

/-- `τ` on the inner coordinates, the identity on `n` and `n + 1`. -/
def hat (τ : Fin n → Fin n) (i : Fin (n + 2)) : Fin (n + 2) :=
  if h : (i : ℕ) < n then Fin.castLE (by omega) (τ ⟨i, h⟩) else i

theorem hat_inv (σ : Perm (Fin n)) (i : Fin (n + 2)) : hat (⇑σ⁻¹) (hat σ i) = i := by
  unfold hat
  by_cases h : (i : ℕ) < n
  · rw [dif_pos h, dif_pos (by simp)]
    apply Fin.ext
    simp
  · rw [dif_neg h, dif_neg h]

theorem ptMap_hat_of_lt (τ : Fin n → Fin n) {u : ℕ} (hu : u < 2 ^ n) :
    ptMap (n + 2) (hat τ) u = ptMap n τ u := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ptMap, testBit_ptMap]
  by_cases hi : i < n
  · rw [dif_pos (by omega), dif_pos hi]
    simp [hat, hi]
  · rw [dif_neg hi]
    split_ifs with h2
    · simp only [hat, hi, dite_false]
      exact testBit_eq_false_of_lt hu (by omega)
    · rfl

/-- Models of the leaf of `m`, pulled back along the point permutation of `σ`. -/
def pull (σ : Perm (Fin n)) (x : Fin (2 ^ (n + 2)) → Bool) : Fin (2 ^ (n + 2)) → Bool :=
  fun u => x ⟨ptMap (n + 2) (hat σ) u, ptMap_lt _ _⟩

theorem ext_pull (σ : Perm (Fin n)) (x : Fin (2 ^ (n + 2)) → Bool) {u : ℕ}
    (hu : u < 2 ^ (n + 2)) : ext (pull σ x) u = ext x (ptMap (n + 2) (hat σ) u) := by
  simp [ext, hu, pull, ptMap_lt]

theorem pull_model (σ : Perm (Fin n)) {m : ℕ} {x : Fin (2 ^ (n + 2)) → Bool}
    (hx : (cube (Dedekind.cnf (n + 2)) (lits n m)).eval (ext x) = true) :
    (cube (Dedekind.cnf (n + 2)) (lits n (act n σ m))).eval (ext (pull σ x)) = true := by
  rw [eval_cube, Bool.and_eq_true, lits, all_cornerLits] at hx ⊢
  obtain ⟨hF, hL⟩ := hx
  constructor
  · rw [Dedekind.model_iff] at hF ⊢
    have hp : (fun z => pull σ x (binEquiv (n + 2) z)) =
        (fun z => x (binEquiv (n + 2) z)) ∘ fun z => z ∘ hat σ := by
      funext z
      simp only [pull, Function.comp_apply]
      congr 1
      apply Fin.ext
      exact ptMap_binEquiv _ _
    rw [hp]
    exact hF.comp fun z z' hz i => hz (hat σ i)
  · intro u hu
    rw [ext_pull σ x (lt_trans hu (two_pow_lt_two_pow_add_two n)), ptMap_hat_of_lt _ hu,
      hL _ (ptMap_lt _ _), testBit_act, if_pos hu]

theorem pull_injective (σ : Perm (Fin n)) : Function.Injective (pull σ) := by
  intro x x' h
  funext v
  have hv : ptMap (n + 2) (hat σ) (ptMap (n + 2) (hat (⇑σ⁻¹)) v) = v := by
    rw [ptMap_ptMap]
    have : (hat (⇑σ⁻¹) ∘ hat σ) = id := funext (hat_inv σ)
    rw [this, ptMap_id v.2]
  have := congrFun h ⟨ptMap (n + 2) (hat (⇑σ⁻¹)) v, ptMap_lt _ _⟩
  simp only [pull] at this
  have e : (⟨ptMap (n + 2) (hat σ) (ptMap (n + 2) (hat (⇑σ⁻¹)) v), ptMap_lt _ _⟩ :
      Fin (2 ^ (n + 2))) = v := Fin.ext hv
  rwa [e] at this

theorem leafCount_le_act (σ : Perm (Fin n)) (m : ℕ) : leafCount n m ≤ leafCount n (act n σ m) :=
  Fintype.card_le_of_injective (fun x => ⟨pull σ x.1, pull_model σ x.2⟩)
    fun _ _ h => Subtype.ext (pull_injective σ (congrArg Subtype.val h))

/-- The leaf count depends only on the orbit of the mask. -/
theorem leafCount_act (σ : Perm (Fin n)) {m : ℕ} (hm : m < 2 ^ 2 ^ n) :
    leafCount n (act n σ m) = leafCount n m := by
  apply le_antisymm _ (leafCount_le_act σ m)
  have := leafCount_le_act σ⁻¹ (act n σ m)
  rwa [act_inv_act σ hm] at this

theorem act_mem_monoMasks (σ : Perm (Fin n)) {m : ℕ} (hm : m ∈ monoMasks n) :
    act n σ m ∈ monoMasks n := by
  simp only [monoMasks, Finset.mem_filter, Finset.mem_range] at hm ⊢
  refine ⟨act_lt σ m, leafCount_ne_zero_iff.1 ?_⟩
  rw [leafCount_act σ hm.1]
  exact leafCount_ne_zero_iff.2 hm.2

/-! ## Delta swaps for adjacent transpositions -/

/-- Exchange bits `u` and `s + u` of `m` for every set bit `u` of `M`. -/
def deltaSwap (s M m : ℕ) : ℕ :=
  let d := ((m >>> s) ^^^ m) &&& M
  m ^^^ d ^^^ (d <<< s)

/-- The point `u` with bits `j` and `j + 1` exchanged. -/
def swapBits (j u : ℕ) : ℕ :=
  if u.testBit j == u.testBit (j + 1) then u else u ^^^ (2 ^ j ||| 2 ^ (j + 1))

/-- The entry `(s, M)` swaps bit `u` with bit `swapBits j u` for every point `u < 2 ^ n`. -/
def entryOk (n j s M : ℕ) : Bool :=
  decide (M < 2 ^ 2 ^ n) && (List.range (2 ^ n)).all fun u =>
    if M.testBit u then
      decide (s + u < 2 ^ n) && !(decide (s ≤ u) && M.testBit (u - s)) && swapBits j u == s + u
    else if decide (s ≤ u) && M.testBit (u - s) then swapBits j u == u - s
    else swapBits j u == u

/-- One entry per adjacent transposition `(j, j + 1)`, `j < n - 1`. -/
def tableOk (n : ℕ) (T : List (ℕ × ℕ)) : Bool :=
  T.length == n - 1 &&
    (List.range (n - 1)).all fun j => entryOk n j (T.getD j (0, 0)).1 (T.getD j (0, 0)).2

/-- One step of the walk: the delta swap of entry `j` of `T`. -/
def stepMask (T : List (ℕ × ℕ)) (j m : ℕ) : ℕ :=
  deltaSwap (T.getD j (0, 0)).1 (T.getD j (0, 0)).2 m

/-- The transposition of the coordinates `j` and `j + 1`. -/
def adjSwap (n j : ℕ) : Perm (Fin n) :=
  if h : j + 1 < n then Equiv.swap ⟨j, by omega⟩ ⟨j + 1, h⟩ else 1

theorem ptMap_adjSwap {j u : ℕ} (hj : j + 1 < n) (hu : u < 2 ^ n) :
    ptMap n (adjSwap n j) u = swapBits j u := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ptMap]
  simp only [adjSwap, dif_pos hj, swapBits]
  by_cases hi : i < n
  · rw [dif_pos hi, Equiv.swap_apply_def]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      split_ifs with h
      · simpa using (beq_iff_eq.1 h).symm
      · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow_self]
        simp only [beq_iff_eq] at h
        cases h1 : u.testBit i <;> cases h2 : u.testBit (i + 1) <;> simp_all
    · rw [if_neg (fun h => hij (congrArg Fin.val h))]
      by_cases hij1 : i = j + 1
      · subst hij1
        rw [if_pos rfl]
        split_ifs with h
        · simpa using beq_iff_eq.1 h
        · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true,
            Bool.xor_true, Nat.testBit_two_pow_of_ne (show j ≠ j + 1 by omega)]
          simp only [beq_iff_eq] at h
          cases h1 : u.testBit j <;> cases h2 : u.testBit (j + 1) <;> simp_all
      · rw [if_neg (fun h => hij1 (congrArg Fin.val h))]
        split_ifs with h
        · rfl
        · simp [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow_of_ne (Ne.symm hij),
            Nat.testBit_two_pow_of_ne (Ne.symm hij1)]
  · rw [dif_neg hi]
    have hu' : u.testBit i = false := testBit_eq_false_of_lt hu (by omega)
    split_ifs with h
    · exact hu'.symm
    · simp [Nat.testBit_xor, Nat.testBit_or, hu', Nat.testBit_two_pow_of_ne (show j ≠ i by omega),
        Nat.testBit_two_pow_of_ne (show j + 1 ≠ i by omega)]

theorem deltaSwap_eq {j s M : ℕ} (h : entryOk n j s M = true) (hj : j + 1 < n) {m : ℕ}
    (hm : m < 2 ^ 2 ^ n) : deltaSwap s M m = act n (adjSwap n j) m := by
  simp only [entryOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hM, hall⟩ := h
  rw [List.all_eq_true] at hall
  have hMhi : ∀ v, 2 ^ n ≤ v → M.testBit v = false := fun v hv => testBit_eq_false_of_lt hM hv
  have hmhi : ∀ v, 2 ^ n ≤ v → m.testBit v = false := fun v hv => testBit_eq_false_of_lt hm hv
  apply Nat.eq_of_testBit_eq
  intro u
  rw [testBit_act]
  simp only [deltaSwap, Nat.testBit_xor, Nat.testBit_land, Nat.testBit_shiftRight,
    Nat.testBit_shiftLeft]
  split_ifs with hu
  · rw [ptMap_adjSwap hj hu]
    have hc := hall u (List.mem_range.2 hu)
    by_cases hMu : M.testBit u = true
    · rw [if_pos hMu] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq] at hc
      obtain ⟨⟨-, hno⟩, hsw⟩ := hc
      rw [hsw, hMu]
      have h3 : (decide (u ≥ s) && ((m.testBit (s + (u - s)) ^^ m.testBit (u - s)) &&
          M.testBit (u - s))) = false := by
        by_cases hsu : s ≤ u
        · have : M.testBit (u - s) = false := by
            simpa [hsu] using hno
          simp [this]
        · simp [hsu]
      rw [h3]
      cases m.testBit u <;> cases m.testBit (s + u) <;> rfl
    · rw [if_neg hMu] at hc
      have hMu' : M.testBit u = false := by simpa using hMu
      rw [hMu']
      by_cases hb : s ≤ u ∧ M.testBit (u - s) = true
      · rw [if_pos hb, beq_iff_eq] at hc
        rw [hc, Nat.add_sub_cancel' hb.1, hb.2]
        simp only [ge_iff_le, hb.1, decide_true, Bool.true_and, Bool.and_true, Bool.and_false,
          Bool.xor_false]
        cases m.testBit u <;> cases m.testBit (u - s) <;> rfl
      · rw [if_neg hb, beq_iff_eq] at hc
        rw [hc]
        have h3 : (decide (u ≥ s) && ((m.testBit (s + (u - s)) ^^ m.testBit (u - s)) &&
            M.testBit (u - s))) = false := by
          by_cases hsu : s ≤ u
          · have : M.testBit (u - s) = false := by simpa [hsu] using hb
            simp [this]
          · simp [hsu]
        rw [h3]
        simp
  · have hu' : 2 ^ n ≤ u := by omega
    rw [hmhi u hu', hMhi u hu']
    have h3 : (decide (u ≥ s) && ((m.testBit (s + (u - s)) ^^ m.testBit (u - s)) &&
        M.testBit (u - s))) = false := by
      by_cases hsu : s ≤ u
      · have : M.testBit (u - s) = false := by
          by_cases hv : u - s < 2 ^ n
          · have hc := hall (u - s) (List.mem_range.2 hv)
            by_contra hne
            have hne' : M.testBit (u - s) = true := by simpa using hne
            rw [if_pos hne'] at hc
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            omega
          · exact hMhi _ (by omega)
        simp [this]
      · simp [hsu]
    rw [h3]
    simp

theorem stepMask_eq {T : List (ℕ × ℕ)} (hT : tableOk n T = true) {j : ℕ} (hj : j + 1 < n)
    {m : ℕ} (hm : m < 2 ^ 2 ^ n) : stepMask T j m = act n (adjSwap n j) m := by
  simp only [tableOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hT
  exact deltaSwap_eq (hT.2 j (by omega)) hj hm

/-! ## A walk through all permutations -/

/-- The permutations along the walk: `σ₀ = 1`, `σ_{k+1} = (j_k, j_k + 1) * σ_k`. -/
def pathPerms (n : ℕ) (path : List ℕ) : List (Perm (Fin n)) :=
  path.scanl (fun σ j => adjSwap n j * σ) 1

/-- Exchange the values `j` and `j + 1` in a list. -/
def swapVals (j : ℕ) (l : List ℕ) : List ℕ :=
  l.map fun v => if v = j then j + 1 else if v = j + 1 then j else v

/-- The permutations along the walk as value lists. -/
def pathVals (n : ℕ) (path : List ℕ) : List (List ℕ) :=
  path.scanl (fun l j => swapVals j l) (List.range n)

/-- The walk uses adjacent transpositions only and visits `n!` distinct permutations. -/
def pathOk (n : ℕ) (path : List ℕ) : Bool :=
  path.all (· + 1 < n) && (pathVals n path).length == n ! && decide (pathVals n path).Nodup

/-- The value list of a permutation. -/
def valsOf (σ : Perm (Fin n)) : List ℕ := List.ofFn fun i => (σ i : ℕ)

theorem map_scanl {α β γ : Type*} (f : α → β → α) (g : γ → β → γ) (F : α → γ) :
    ∀ (l : List β) (a : α), (∀ a, ∀ b ∈ l, F (f a b) = g (F a) b) →
      (l.scanl f a).map F = l.scanl g (F a)
  | [], a, _ => by simp
  | b :: l, a, h => by
    rw [List.scanl_cons, List.scanl_cons, List.map_cons,
      map_scanl f g F l (f a b) fun a' b' hb' => h a' b' (List.mem_cons_of_mem _ hb'),
      h a b List.mem_cons_self]

theorem valsOf_one : valsOf (1 : Perm (Fin n)) = List.range n := by
  apply List.ext_getElem (by simp [valsOf])
  intro i h1 h2
  simp [valsOf]

theorem valsOf_adjSwap_mul {j : ℕ} (hj : j + 1 < n) (σ : Perm (Fin n)) :
    valsOf (adjSwap n j * σ) = swapVals j (valsOf σ) := by
  simp only [valsOf, swapVals, List.map_ofFn, Perm.mul_apply, adjSwap, dif_pos hj]
  congr 1
  funext i
  simp only [Function.comp_apply, Equiv.swap_apply_def]
  by_cases h1 : σ i = ⟨j, by omega⟩
  · rw [if_pos h1, if_pos (congrArg Fin.val h1)]
  · rw [if_neg h1, if_neg (fun h => h1 (Fin.ext h))]
    by_cases h2 : σ i = ⟨j + 1, hj⟩
    · rw [if_pos h2, if_pos (congrArg Fin.val h2)]
    · rw [if_neg h2, if_neg (fun h => h2 (Fin.ext h))]

theorem valsOf_injective : Function.Injective (valsOf (n := n)) := by
  intro σ τ h
  have h' := List.ofFn_injective h
  ext i
  exact congrFun h' i

theorem map_valsOf_pathPerms {path : List ℕ} (h : path.all (· + 1 < n) = true) :
    (pathPerms n path).map valsOf = pathVals n path := by
  rw [pathPerms, pathVals, ← valsOf_one]
  apply map_scanl
  intro σ j hj
  exact valsOf_adjSwap_mul (by simpa using List.all_eq_true.1 h j hj) σ

theorem pathPerms_spec {path : List ℕ} (h : pathOk n path = true) :
    (pathPerms n path).Nodup ∧ ∀ σ, σ ∈ pathPerms n path := by
  simp only [pathOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hj, hlen⟩, hnd⟩ := h
  have hmap := map_valsOf_pathPerms hj
  have hnd' : (pathPerms n path).Nodup := by
    rw [← hmap] at hnd
    exact hnd.of_map _
  refine ⟨hnd', fun σ => ?_⟩
  have hl : (pathPerms n path).length = n ! := by
    rw [← List.length_map (f := valsOf), hmap, hlen]
  have hcard : (pathPerms n path).toFinset.card = Fintype.card (Perm (Fin n)) := by
    rw [List.toFinset_card_of_nodup hnd', hl, Fintype.card_perm, Fintype.card_fin]
  have := Finset.eq_univ_of_card _ hcard
  rw [← List.mem_toFinset, this]
  exact Finset.mem_univ σ

/-! ## The per-representative check -/

/-- The masks visited from `t` along the walk. -/
def visit (T : List (ℕ × ℕ)) (t : ℕ) (path : List ℕ) : List ℕ :=
  path.scanl (fun t j => stepMask T j t) t

/-- Walk from the mask `t`: `none` as soon as a mask below `r` appears, else `c` plus the number
    of visited masks (after `t`) equal to `r`. -/
def scan (T : List (ℕ × ℕ)) (r : ℕ) : List ℕ → ℕ → ℕ → Option ℕ
  | [], _, c => some c
  | j :: path, t, c =>
    let t' := stepMask T j t
    if t' < r then none else scan T r path t' (if t' = r then c + 1 else c)

theorem scan_spec (T : List (ℕ × ℕ)) (r : ℕ) :
    ∀ (path : List ℕ) (t c c' : ℕ), scan T r path t c = some c' →
      (∀ x ∈ (visit T t path).tail, r ≤ x) ∧ c' = c + (visit T t path).tail.count r
  | [], t, c, c', h => by
    simp only [scan, Option.some.injEq] at h
    simp [visit, h]
  | j :: path, t, c, c', h => by
    simp only [scan] at h
    by_cases hlt : stepMask T j t < r
    · rw [if_pos hlt] at h
      exact absurd h (by simp)
    rw [if_neg hlt] at h
    have ih := scan_spec T r path _ _ c' h
    have hv : visit T t (j :: path) = t :: visit T (stepMask T j t) path := by
      simp [visit, List.scanl_cons]
    have hv' : visit T (stepMask T j t) path =
        stepMask T j t :: (visit T (stepMask T j t) path).tail := by
      simp [visit]
      cases path <;> simp [List.scanl_cons]
    rw [hv, List.tail_cons, hv']
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · exact ih.1 x hx
    · rw [ih.2, List.count_cons]
      by_cases h1 : stepMask T j t = r <;> simp [h1] <;> omega

/-! ## Monotonicity of a mask by shifts -/

/-- Entry `(s, L)` for the coordinate `b`: `L` holds the points with bit `b` clear, and for
    those `s + u` is the point `u` with bit `b` set. -/
def monoEntryOk (n b s L : ℕ) : Bool :=
  decide (L < 2 ^ 2 ^ n) && (List.range (2 ^ n)).all fun u =>
    (L.testBit u == !u.testBit b) && (!L.testBit u || s + u == (u ||| 2 ^ b))

/-- One entry per coordinate `b < n`. -/
def monoTableOk (n : ℕ) (Ls : List (ℕ × ℕ)) : Bool :=
  Ls.length == n &&
    (List.range n).all fun b => monoEntryOk n b (Ls.getD b (0, 0)).1 (Ls.getD b (0, 0)).2

/-- The mask `m` is closed under setting one clear bit of a point: for every entry `(s, L)`, the
    points of `m` in `L` shifted by `s` lie in `m`. -/
def monoOk (Ls : List (ℕ × ℕ)) (m : ℕ) : Bool :=
  Ls.all fun e => ((m &&& e.2) <<< e.1) &&& m == (m &&& e.2) <<< e.1

theorem isMono_of_monoOk {Ls : List (ℕ × ℕ)} (hL : monoTableOk n Ls = true) {m : ℕ}
    (h : monoOk Ls m = true) : IsMono n m := by
  simp only [monoTableOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hL
  obtain ⟨hlen, hent⟩ := hL
  intro u hu b hb hub hm
  have hmem : Ls.getD b (0, 0) ∈ Ls := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have he := hent b hb
  simp only [monoEntryOk, Bool.and_eq_true] at he
  have hu' := List.all_eq_true.1 he.2 u (List.mem_range.2 hu)
  rw [hub, Bool.not_false, Bool.and_eq_true, beq_iff_eq] at hu'
  obtain ⟨hLu, hsu⟩ := hu'
  rw [hLu, Bool.not_true, Bool.false_or, beq_iff_eq] at hsu
  have hx := List.all_eq_true.1 h _ hmem
  rw [beq_iff_eq] at hx
  have := congrArg (fun x => x.testBit ((Ls.getD b (0, 0)).1 + u)) hx
  simp only [Nat.testBit_land, Nat.testBit_shiftLeft, Nat.add_sub_cancel_left, hm, hLu,
    ge_iff_le, Nat.le_add_right, decide_true, Bool.true_and, Bool.and_true] at this
  rw [← hsu]
  exact this

/-! ## The per-representative check -/

/-- The side check of one class `(r, o)`: `r` is a monotone mask, the smallest of its orbit, and
    `o · |Stab r| = n!` (the stabiliser counted along the walk). -/
def repOk (n : ℕ) (T Ls : List (ℕ × ℕ)) (path : List ℕ) (p : ℕ × ℕ) : Bool :=
  decide (p.1 < 2 ^ 2 ^ n) && monoOk Ls p.1 &&
    match scan T p.1 path p.1 1 with
    | some c => p.2 * c == n !
    | none => false

theorem visit_eq {T : List (ℕ × ℕ)} (hT : tableOk n T = true) {path : List ℕ}
    (hp : path.all (· + 1 < n) = true) {r : ℕ} (hr : r < 2 ^ 2 ^ n) :
    visit T r path = (pathPerms n path).map fun σ => act n σ r := by
  rw [visit, pathPerms]
  have := map_scanl (fun σ j => adjSwap n j * σ) (fun t j => stepMask T j t)
    (fun σ => act n σ r) path 1 fun σ j hj => by
      simp only
      rw [stepMask_eq hT (by simpa using List.all_eq_true.1 hp j hj) (act_lt _ _), act_mul]
  rw [this]
  congr 1
  exact (act_one hr).symm

/-- What `repOk` checks, given the table and the walk. -/
theorem repOk_spec {T Ls : List (ℕ × ℕ)} (hT : tableOk n T = true)
    (hL : monoTableOk n Ls = true) {path : List ℕ}
    (hpath : pathOk n path = true) {p : ℕ × ℕ} (h : repOk n T Ls path p = true) :
    p.1 ∈ monoMasks n ∧ (∀ σ : Perm (Fin n), p.1 ≤ act n σ p.1) ∧
      p.2 * (Finset.univ.filter fun σ : Perm (Fin n) => act n σ p.1 = p.1).card = n ! := by
  obtain ⟨r, o⟩ := p
  simp only [repOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hr, hc⟩, hs⟩ := h
  have hmono : r ∈ monoMasks n := by
    simp only [monoMasks, Finset.mem_filter, Finset.mem_range]
    exact ⟨hr, isMono_of_monoOk hL hc⟩
  split at hs
  · rename_i c0 hscan
    simp only [beq_iff_eq] at hs
    have hp : path.all (· + 1 < n) = true := by
      simp only [pathOk, Bool.and_eq_true] at hpath
      exact hpath.1.1
    obtain ⟨hnd, hall⟩ := pathPerms_spec hpath
    obtain ⟨hle, hcnt⟩ := scan_spec T r path r 1 c0 hscan
    have hvis := visit_eq hT hp hr
    have hfull : visit T r path = r :: (visit T r path).tail := by
      cases path <;> simp [visit, List.scanl_cons]
    refine ⟨hmono, fun σ => ?_, ?_⟩
    · have hm : act n σ r ∈ visit T r path := by
        rw [hvis]
        exact List.mem_map_of_mem (hall σ)
      rw [hfull] at hm
      rcases List.mem_cons.1 hm with h1 | h1
      · rw [h1]
      · exact hle _ h1
    · have hc0 : c0 = (visit T r path).count r := by
        rw [hcnt]
        conv_rhs => rw [hfull]
        rw [List.count_cons]
        simp [add_comm]
      have hcount : (visit T r path).count r =
          (Finset.univ.filter fun σ : Perm (Fin n) => act n σ r = r).card := by
        rw [hvis, List.count_eq_countP, List.countP_map, List.countP_eq_length_filter,
          ← List.toFinset_card_of_nodup (hnd.filter _)]
        congr 1
        ext σ
        simp [hall σ]
      rw [← hcount, ← hc0]
      exact hs
  · simp at hs

/-! ## Completeness by counting -/

/-- The orbit of the mask `r`. -/
def orbit (n r : ℕ) : Finset ℕ := Finset.univ.image fun σ : Perm (Fin n) => act n σ r

theorem card_orbit_mul {r : ℕ} (hr : r < 2 ^ 2 ^ n) :
    (orbit n r).card * (Finset.univ.filter fun σ : Perm (Fin n) => act n σ r = r).card = n ! := by
  have h := Finset.card_eq_sum_card_image (fun σ : Perm (Fin n) => act n σ r) Finset.univ
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h
  rw [h, orbit, ← smul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hm
  apply Finset.card_nbij' (fun σ => τ * σ) (fun σ => τ⁻¹ * σ)
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    rw [← act_mul, hσ]
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    rw [← act_mul, hσ, act_inv_act τ hr]
  · intro σ _
    simp
  · intro σ _
    simp

theorem stab_pos {r : ℕ} (hr : r < 2 ^ 2 ^ n) :
    0 < (Finset.univ.filter fun σ : Perm (Fin n) => act n σ r = r).card :=
  Finset.card_pos.2 ⟨1, by simp [act_one hr]⟩

theorem orbit_subset {r : ℕ} (hr : r ∈ monoMasks n) : orbit n r ⊆ monoMasks n := by
  intro m hm
  obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hm
  exact act_mem_monoMasks σ hr

theorem eq_of_mem_orbit {r r' : ℕ} (hr : r < 2 ^ 2 ^ n) (hr' : r' < 2 ^ 2 ^ n)
    (hc : ∀ σ : Perm (Fin n), r ≤ act n σ r) (hc' : ∀ σ : Perm (Fin n), r' ≤ act n σ r')
    {m : ℕ} (hm : m ∈ orbit n r) (hm' : m ∈ orbit n r') : r = r' := by
  obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hm
  obtain ⟨τ, -, he⟩ := Finset.mem_image.1 hm'
  have h1 : r' = act n (τ⁻¹ * σ) r := by rw [← act_mul, ← he, act_inv_act τ hr']
  have h2 : r = act n (σ⁻¹ * τ) r' := by rw [← act_mul, he, act_inv_act σ hr]
  have := hc (τ⁻¹ * σ)
  have := hc' (σ⁻¹ * τ)
  omega

/-- The sum of an invariant function over the monotone masks from one representative per
    orbit, with the orbit sizes. -/
theorem sum_eq_of_reps (L : ℕ → ℕ)
    (hL : ∀ σ : Perm (Fin n), ∀ m < 2 ^ 2 ^ n, L (act n σ m) = L m)
    (R : List (ℕ × ℕ)) (hR : ∀ p ∈ R, p.1 ∈ monoMasks n)
    (hcan : ∀ p ∈ R, ∀ σ : Perm (Fin n), p.1 ≤ act n σ p.1)
    (hnd : (R.map Prod.fst).Nodup)
    (horb : ∀ p ∈ R,
      p.2 * (Finset.univ.filter fun σ : Perm (Fin n) => act n σ p.1 = p.1).card = n !)
    (hsum : (R.map Prod.snd).sum = (monoMasks n).card) :
    ∑ m ∈ monoMasks n, L m = (R.map fun p => p.2 * L p.1).sum := by
  have hlt : ∀ p ∈ R, p.1 < 2 ^ 2 ^ n := fun p hp => by
    have := hR p hp
    simp only [monoMasks, Finset.mem_filter, Finset.mem_range] at this
    exact this.1
  have hcard : ∀ p ∈ R, (orbit n p.1).card = p.2 := fun p hp => by
    have h1 := card_orbit_mul (hlt p hp)
    rw [← horb p hp] at h1
    exact Nat.eq_of_mul_eq_mul_right (stab_pos (hlt p hp)) h1
  set S := (R.map Prod.fst).toFinset with hS
  have hmemS : ∀ r ∈ S, ∃ p ∈ R, p.1 = r := fun r hr => by
    simpa [hS] using hr
  have hdisj : (S : Set ℕ).PairwiseDisjoint (orbit n) := by
    intro r hr r' hr' hne
    obtain ⟨p, hp, rfl⟩ := hmemS r hr
    obtain ⟨p', hp', rfl⟩ := hmemS r' hr'
    rw [Function.onFun, Finset.disjoint_left]
    intro m hm hm'
    exact hne (eq_of_mem_orbit (hlt p hp) (hlt p' hp') (hcan p hp) (hcan p' hp') hm hm')
  -- the orbits cover the monotone masks
  have hsub : S.biUnion (orbit n) ⊆ monoMasks n := by
    intro m hm
    obtain ⟨r, hr, hm⟩ := Finset.mem_biUnion.1 hm
    obtain ⟨p, hp, rfl⟩ := hmemS r hr
    exact orbit_subset (hR p hp) hm
  have hsumS : ∀ g : ℕ → ℕ, ∑ r ∈ S, g r = (R.map fun p => g p.1).sum := fun g => by
    rw [hS, List.sum_toFinset _ hnd, List.map_map]
    rfl
  have hcov : S.biUnion (orbit n) = monoMasks n := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_biUnion hdisj, hsumS, ← hsum]
    apply le_of_eq
    congr 1
    exact List.map_congr_left fun p hp => (hcard p hp).symm
  rw [← hcov, Finset.sum_biUnion hdisj, hsumS]
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [Finset.sum_congr rfl (g := fun _ => L p.1), Finset.sum_const, smul_eq_mul, hcard p hp]
  intro m hm
  obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hm
  exact hL σ p.1 (hlt p hp)

/-- Strictly increasing. -/
def sortedB : List ℕ → Bool
  | a :: b :: l => decide (a < b) && sortedB (b :: l)
  | _ => true

theorem lt_of_sortedB : ∀ {a : ℕ} {l : List ℕ}, sortedB (a :: l) = true → ∀ x ∈ l, a < x
  | _, [], _, x, hx => by simp at hx
  | a, b :: l, h, x, hx => by
    simp only [sortedB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (lt_of_sortedB h.2 x hx)

theorem nodup_of_sortedB : ∀ {l : List ℕ}, sortedB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [a], _ => List.nodup_singleton a
  | a :: b :: l, h => by
    have h' := h
    simp only [sortedB, Bool.and_eq_true] at h'
    exact List.nodup_cons.2 ⟨fun hm => lt_irrefl a (lt_of_sortedB h a hm),
      nodup_of_sortedB h'.2⟩

/-- **Completeness by counting.** `Ks` lists the classes in chunks: each chunk is a list of
    pairs `(r, o)` (representative mask, orbit size) with the claimed sum `s` of `o · c` over the
    chunk, `c` the leaf count of `r`. The side checks (`hreps`, one `decide +kernel` per chunk)
    make each `r` a monotone mask that is the smallest of its orbit with orbit size `o`; with the
    representatives strictly increasing and the orbit sizes adding up to `M(n)`, the classes
    cover the monotone masks and `M(n + 2)` is the sum of the chunk sums. -/
theorem card_eq_of_classes (n : ℕ) (T Ls : List (ℕ × ℕ)) (hT : tableOk n T = true)
    (hL : monoTableOk n Ls = true) (path : List ℕ) (hpath : pathOk n path = true)
    (Ks : List (List (ℕ × ℕ) × ℕ))
    (hreps : ∀ K ∈ Ks, K.1.all (repOk n T Ls path) = true)
    (hsort : sortedB ((Ks.map Prod.fst).flatten.map Prod.fst) = true)
    (hM : Nat.card {f : (Fin n → Bool) → Bool // Monotone f} =
      ((Ks.map Prod.fst).flatten.map Prod.snd).sum)
    (hS : ∀ K ∈ Ks, (K.1.map fun p => p.2 * leafCount n p.1).sum = K.2) :
    Nat.card {f : (Fin (n + 2) → Bool) → Bool // Monotone f} = (Ks.map Prod.snd).sum := by
  set R := (Ks.map Prod.fst).flatten with hR
  have hspec : ∀ p ∈ R, p.1 ∈ monoMasks n ∧ (∀ σ : Perm (Fin n), p.1 ≤ act n σ p.1) ∧
      p.2 * (Finset.univ.filter fun σ : Perm (Fin n) => act n σ p.1 = p.1).card = n ! := by
    intro p hp
    obtain ⟨C, hC, hpC⟩ := List.mem_flatten.1 hp
    obtain ⟨K, hK, rfl⟩ := List.mem_map.1 hC
    exact repOk_spec hT hL hpath (List.all_eq_true.1 (hreps K hK) p hpC)
  rw [card_monotone_succ_succ,
    sum_eq_of_reps (leafCount n) (fun σ m hm => leafCount_act σ hm) R
      (fun p hp => (hspec p hp).1) (fun p hp => (hspec p hp).2.1) (nodup_of_sortedB hsort)
      (fun p hp => (hspec p hp).2.2) (by rw [← card_monotone_eq, hM])]
  rw [hR, List.map_flatten, List.sum_flatten, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro K hK
  exact hS K hK

theorem chunkSum_nil : (([] : List (ℕ × ℕ)).map fun p => p.2 * leafCount n p.1).sum = 0 := rfl

/-- One step of a chunk sum: the leaf theorem of `r` and the sum of the rest. -/
theorem chunkSum_cons {r o c s : ℕ} {Q : List (ℕ × ℕ)} (h : leafCount n r = c)
    (hs : (Q.map fun p => p.2 * leafCount n p.1).sum = s) :
    (((r, o) :: Q).map fun p => p.2 * leafCount n p.1).sum = o * c + s := by
  rw [List.map_cons, List.sum_cons, h, hs]

/-- The leaf count of a split class from the leaf theorems of a `SplitTree` rooted at the
    corner literals. -/
theorem leafCount_of_tree {m N : ℕ} (t : SplitTree)
    (h : t.Holds (2 ^ (n + 2)) (Dedekind.cnf (n + 2)) (lits n m)) (hN : t.total = N) :
    leafCount n m = N :=
  (SplitTree.card_eq_total t (lits n m) h).trans hN

end CountCatcher.DedekindCorner
