import CountCatcherMath.Family
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Antichain
import Mathlib.Data.List.Nodup
import Mathlib.Order.Partition.Finpartition

/-!
# Family: antichains of the Kreweras lattice NC(n) (OEIS A358391)

Objects: antichains of noncrossing set partitions of `Fin n` under refinement, with the set
partitions given either as Mathlib's `Finpartition (Finset.univ : Finset (Fin n))` (`Fp.card_of_check`)
or as equivalence relations `Setoid (Fin n)` (`card_of_check`); in both, Mathlib's `≤` is
refinement. The one new definition is the noncrossing condition (`Finpartition.IsNoncrossing`,
`Setoid.IsNoncrossing`). The count includes the empty antichain (A358391: a(1) = 2, a(2) = 3).

Encoder (as `scripts/showcase/oeis/gen_A358391.py`): one variable per noncrossing partition,
in lexicographic order of leader lists (entry `i` = least element of the block of `i`, which is
the order of the generator's `set_partitions`), and one clause `¬x_i ∨ ¬x_j` per strictly
comparable pair `i < j`, in the order `i`, then `j`. No auxiliary variables.

The family lemma is generic in `n`: `gen n` lists the leader lists of length `n` with a proved
membership lemma and `Nodup`; `ofSetoid`/`toSetoid` are inverse on valid leader lists, and
refinement and noncrossing are computed on leader lists (`le_iff`, `ncB_iff`). No per-`n`
kernel enumeration.
-/

open Std.Sat

/-- Noncrossing: no `a < b < c < d` with `a ~ c`, `b ~ d` in two different blocks. -/
def Setoid.IsNoncrossing {n : ℕ} (r : Setoid (Fin n)) : Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d → r a c → r b d → r a b

/-- Noncrossing set partition: no `a < b < c < d` with `a, c` in one block and `b, d` in
    another. -/
def Finpartition.IsNoncrossing {n : ℕ} (P : Finpartition (Finset.univ : Finset (Fin n))) :
    Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d → P.part a = P.part c → P.part b = P.part d →
    P.part a = P.part b

namespace CountCatcher.Kreweras

/-! ## Leader lists -/

/-- A leader list: entry `i` is the least element of the block of `i`. -/
def Valid (w : List ℕ) : Prop :=
  ∀ i < w.length, w.getD i 0 ≤ i ∧ w.getD (w.getD i 0) 0 = w.getD i 0

/-- All leader lists of length `k`, in lexicographic order. -/
def gen : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (gen k).flatMap fun w =>
      ((List.range (k + 1)).filter fun x => x == k || w.getD x 0 == x).map fun x => w ++ [x]

theorem getD_concat_of_lt {v : List ℕ} {x i : ℕ} (h : i < v.length) :
    (v ++ [x]).getD i 0 = v.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_concat_length {v : List ℕ} {x : ℕ} : (v ++ [x]).getD v.length 0 = x := by
  simp [List.getD_eq_getElem?_getD]

theorem valid_concat {v : List ℕ} {x : ℕ} :
    Valid (v ++ [x]) ↔ Valid v ∧ x ≤ v.length ∧ (x = v.length ∨ v.getD x 0 = x) := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := h i (by simp; omega)
      rw [getD_concat_of_lt hi] at h1 h2
      rw [getD_concat_of_lt (by omega)] at h2
      exact ⟨h1, h2⟩
    · obtain ⟨h1, h2⟩ := h v.length (by simp)
      rw [getD_concat_length] at h1 h2
      refine ⟨h1, ?_⟩
      rcases Nat.lt_or_ge x v.length with hx | hx
      · right; rwa [getD_concat_of_lt hx] at h2
      · left; omega
  · rintro ⟨hv, hx, hc⟩ i hi
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge i v.length with hi' | hi'
    · obtain ⟨h1, h2⟩ := hv i hi'
      rw [getD_concat_of_lt hi', getD_concat_of_lt (by omega)]
      exact ⟨h1, h2⟩
    · obtain rfl : i = v.length := by omega
      rw [getD_concat_length]
      refine ⟨hx, ?_⟩
      rcases hc with rfl | hc
      · exact getD_concat_length
      · rcases Nat.lt_or_ge x v.length with hx' | hx'
        · rw [getD_concat_of_lt hx']; exact hc
        · obtain rfl : x = v.length := by omega
          exact getD_concat_length

theorem mem_gen {k : ℕ} {w : List ℕ} : w ∈ gen k ↔ w.length = k ∧ Valid w := by
  induction k generalizing w with
  | zero =>
    simp only [gen, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨rfl, fun i hi => by simp at hi⟩
    · exact fun h => List.eq_nil_of_length_eq_zero h.1
  | succ k ih =>
    simp only [gen, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
      Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨v, hv, x, ⟨hx, hc⟩, rfl⟩
      obtain ⟨hl, hval⟩ := ih.1 hv
      subst hl
      exact ⟨by simp, valid_concat.2 ⟨hval, by omega, hc⟩⟩
    · rintro ⟨hl, hval⟩
      rcases List.eq_nil_or_concat w with rfl | ⟨v, x, rfl⟩
      · simp at hl
      · rw [List.concat_eq_append] at hval hl ⊢
        obtain ⟨hv, hx, hc⟩ := valid_concat.1 hval
        have hvl : v.length = k := by simpa using hl
        subst hvl
        exact ⟨v, ih.2 ⟨rfl, hv⟩, x, ⟨by omega, hc⟩, rfl⟩

theorem nodup_gen (k : ℕ) : (gen k).Nodup := by
  induction k with
  | zero => simp [gen]
  | succ k ih =>
    rw [gen, List.nodup_flatMap]
    refine ⟨fun v _ => (List.nodup_range.filter _).map fun x y h => by simpa using h, ?_⟩
    refine ih.pairwise_of_forall_ne fun a _ b _ hab => ?_
    rw [Function.onFun]
    intro l hla hlb
    simp only [List.mem_map] at hla hlb
    obtain ⟨x, -, rfl⟩ := hla
    obtain ⟨y, -, hy⟩ := hlb
    exact hab (List.append_inj_left' hy rfl).symm

/-! ## Leader lists and equivalence relations -/

/-- The equivalence relation of a leader list: same leader. -/
def toSetoid (n : ℕ) (w : List ℕ) : Setoid (Fin n) := Setoid.ker fun i : Fin n => w.getD i 0

theorem toSetoid_rel {n : ℕ} {w : List ℕ} {i j : Fin n} :
    toSetoid n w i j ↔ w.getD i 0 = w.getD j 0 := Setoid.ker_def

section
open Classical

variable {n : ℕ} (r : Setoid (Fin n))

/-- The least element of the block of `i`. -/
noncomputable def lead (i : Fin n) : ℕ :=
  Nat.find (⟨i, i.2, r.refl' i⟩ : ∃ j, ∃ h : j < n, r i ⟨j, h⟩)

theorem lead_spec (i : Fin n) : ∃ h : lead r i < n, r i ⟨lead r i, h⟩ :=
  Nat.find_spec (⟨i, i.2, r.refl' i⟩ : ∃ j, ∃ h : j < n, r i ⟨j, h⟩)

theorem lead_lt (i : Fin n) : lead r i < n := (lead_spec r i).1

theorem rel_lead (i : Fin n) : r i ⟨lead r i, lead_lt r i⟩ := (lead_spec r i).2

theorem lead_le (i : Fin n) : lead r i ≤ i := Nat.find_min' _ ⟨i.2, r.refl' i⟩

theorem lead_eq_of_rel {i j : Fin n} (h : r i j) : lead r i = lead r j := by
  apply le_antisymm
  · exact Nat.find_min' _ ⟨lead_lt r j, r.trans' h (rel_lead r j)⟩
  · exact Nat.find_min' _ ⟨lead_lt r i, r.trans' (r.symm' h) (rel_lead r i)⟩

theorem rel_iff_lead {i j : Fin n} : r i j ↔ lead r i = lead r j := by
  refine ⟨lead_eq_of_rel r, fun h => ?_⟩
  have h1 := rel_lead r i
  have h2 := rel_lead r j
  have : (⟨lead r i, lead_lt r i⟩ : Fin n) = ⟨lead r j, lead_lt r j⟩ := Fin.ext h
  rw [this] at h1
  exact r.trans' h1 (r.symm' h2)

/-- The leader list of an equivalence relation. -/
noncomputable def ofSetoid : List ℕ := List.ofFn (lead r)

theorem length_ofSetoid : (ofSetoid r).length = n := List.length_ofFn

theorem getD_ofSetoid {i : ℕ} (hi : i < n) : (ofSetoid r).getD i 0 = lead r ⟨i, hi⟩ := by
  simp [ofSetoid, List.getD_eq_getElem?_getD, hi]

theorem valid_ofSetoid : Valid (ofSetoid r) := by
  intro i hi
  rw [length_ofSetoid] at hi
  rw [getD_ofSetoid r hi, getD_ofSetoid r (lead_lt r _)]
  exact ⟨lead_le r _, (lead_eq_of_rel r (rel_lead r _)).symm⟩

theorem toSetoid_ofSetoid : toSetoid n (ofSetoid r) = r := by
  ext i j
  rw [toSetoid_rel, getD_ofSetoid r i.2, getD_ofSetoid r j.2, rel_iff_lead r]

theorem lead_toSetoid {w : List ℕ} (hl : w.length = n) (hw : Valid w) (i : Fin n) :
    lead (toSetoid n w) i = w.getD i 0 := by
  have hi : (i : ℕ) < w.length := hl ▸ i.2
  obtain ⟨h1, h2⟩ := hw i hi
  unfold lead
  rw [Nat.find_eq_iff]
  refine ⟨⟨by omega, ?_⟩, fun m hm ⟨hmn, hrel⟩ => ?_⟩
  · rw [toSetoid_rel]; exact h2.symm
  · rw [toSetoid_rel] at hrel
    have := (hw m (hl ▸ hmn)).1
    simp only at hrel
    omega

theorem ofSetoid_toSetoid {w : List ℕ} (hl : w.length = n) (hw : Valid w) :
    ofSetoid (toSetoid n w) = w := by
  apply List.ext_getElem (by rw [length_ofSetoid, hl])
  intro i h1 h2
  have h3 : i < n := by rwa [length_ofSetoid] at h1
  have := getD_ofSetoid (toSetoid n w) h3
  rw [lead_toSetoid hl hw] at this
  simpa [List.getD_eq_getElem?_getD, h1, h2] using this

end

/-- Equivalence relations on `Fin n` are the leader lists of length `n`. -/
noncomputable def leaderEquiv (n : ℕ) : {w : List ℕ // w.length = n ∧ Valid w} ≃ Setoid (Fin n) where
  toFun w := toSetoid n w
  invFun r := ⟨ofSetoid r, length_ofSetoid r, valid_ofSetoid r⟩
  left_inv w := Subtype.ext (ofSetoid_toSetoid w.2.1 w.2.2)
  right_inv r := toSetoid_ofSetoid r

/-! ## Refinement and noncrossing, computed on leader lists -/

/-- `v` refines `w`: every element has the `w`-leader of its `v`-leader. -/
def leB (v w : List ℕ) : Bool :=
  (List.range v.length).all fun i => w.getD (v.getD i 0) 0 == w.getD i 0

theorem le_iff {n : ℕ} {v w : List ℕ} (hl : v.length = n) (hv : Valid v) :
    toSetoid n v ≤ toSetoid n w ↔ leB v w = true := by
  simp only [leB, List.all_eq_true, List.mem_range, beq_iff_eq, Setoid.le_def, toSetoid_rel]
  constructor
  · intro h i hi
    obtain ⟨h1, h2⟩ := hv i hi
    exact (@h ⟨i, by omega⟩ ⟨v.getD i 0, by omega⟩ h2.symm).symm
  · intro h x y hxy
    rw [← h x (by omega), ← h y (by omega), hxy]

/-- Noncrossing test on a leader list. -/
def ncB (w : List ℕ) : Bool :=
  (List.range w.length).all fun a => (List.range w.length).all fun b =>
    (List.range w.length).all fun c => (List.range w.length).all fun d =>
      decide (a < b → b < c → c < d → w.getD a 0 = w.getD c 0 → w.getD b 0 = w.getD d 0 →
        w.getD a 0 = w.getD b 0)

theorem ncB_iff {n : ℕ} {w : List ℕ} (hl : w.length = n) :
    ncB w = true ↔ (toSetoid n w).IsNoncrossing := by
  subst hl
  simp only [ncB, List.all_eq_true, List.mem_range, decide_eq_true_eq, Setoid.IsNoncrossing,
    toSetoid_rel]
  constructor
  · intro h a b c d
    exact h a a.2 b b.2 c c.2 d d.2
  · intro h a ha b hb c hc d hd
    exact h ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩

/-! ## The noncrossing partitions, enumerated -/

/-- The noncrossing leader lists of length `n` (the elements of NC(n)), lexicographic. -/
def ncList (n : ℕ) : List (List ℕ) := (gen n).filter ncB

theorem mem_ncList {n : ℕ} {w : List ℕ} :
    w ∈ ncList n ↔ (w.length = n ∧ Valid w) ∧ ncB w = true := by
  simp [ncList, mem_gen]

theorem nodup_ncList (n : ℕ) : (ncList n).Nodup := (nodup_gen n).filter _

/-- Index `i` of `ncList n` is the `i`-th noncrossing partition. -/
noncomputable def ncEquiv (n : ℕ) :
    Fin (ncList n).length ≃ {r : Setoid (Fin n) // r.IsNoncrossing} where
  toFun i := ⟨toSetoid n (ncList n)[i], by
    obtain ⟨⟨hl, -⟩, hnc⟩ := mem_ncList.1 (List.getElem_mem i.2)
    exact (ncB_iff hl).1 hnc⟩
  invFun r := ⟨(ncList n).idxOf (ofSetoid r.1), List.idxOf_lt_length_iff.2 (mem_ncList.2
      ⟨⟨length_ofSetoid _, valid_ofSetoid _⟩,
        (ncB_iff (length_ofSetoid _)).2 (by rw [toSetoid_ofSetoid]; exact r.2)⟩)⟩
  left_inv i := by
    obtain ⟨⟨hl, hv⟩, -⟩ := mem_ncList.1 (List.getElem_mem i.2)
    apply Fin.ext
    simp only [Fin.getElem_fin]
    rw [ofSetoid_toSetoid hl hv]
    exact (nodup_ncList n).idxOf_getElem i i.2
  right_inv r := by
    apply Subtype.ext
    simp only [Fin.getElem_fin, List.getElem_idxOf, toSetoid_ofSetoid]

/-- The comparison used by the encoder: indices into `ncList n`, either direction. -/
def cmp (L : List (List ℕ)) (i j : ℕ) : Bool := leB (L.getD i []) (L.getD j [])

theorem cmp_iff (n : ℕ) (i j : Fin (ncList n).length) :
    cmp (ncList n) i j = true ↔ ncEquiv n i ≤ ncEquiv n j := by
  obtain ⟨⟨hl, hv⟩, -⟩ := mem_ncList.1 (List.getElem_mem i.2)
  have : ncEquiv n i ≤ ncEquiv n j ↔ toSetoid n (ncList n)[i] ≤ toSetoid n (ncList n)[j] :=
    Iff.rfl
  rw [this, Fin.getElem_fin, Fin.getElem_fin, le_iff hl hv, cmp]
  simp [List.getD_eq_getElem?_getD, i.2, j.2]

/-! ## Antichains of a finite poset enumerated by `Fin N` -/

section Antichain

variable {X : Type*} [PartialOrder X] {N : ℕ}

/-- One clause `¬x_i ∨ ¬x_j` per comparable pair `i < j` (order `i`, then `j`). -/
def acClauses (N : ℕ) (c : ℕ → ℕ → Bool) : List (CNF.Clause ℕ) :=
  (List.range N).flatMap fun i =>
    ((List.range N).filter fun j => decide (i < j) && (c i j || c j i)).map fun j =>
      [(i, false), (j, false)]

/-- The antichain CNF for the comparison `c` on `Fin N`. -/
def acCnf (N : ℕ) (c : ℕ → ℕ → Bool) : CNF ℕ := ⟨(acClauses N c).toArray⟩

theorem mem_acClauses {c : ℕ → ℕ → Bool} {cl : CNF.Clause ℕ} :
    cl ∈ acClauses N c ↔ ∃ i < N, ∃ j < N, i < j ∧ (c i j || c j i) = true ∧
      cl = [(i, false), (j, false)] := by
  simp only [acClauses, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, j, ⟨hj, hij, hc⟩, rfl⟩; exact ⟨i, hi, j, hj, hij, hc, rfl⟩
  · rintro ⟨i, hi, j, hj, hij, hc, rfl⟩; exact ⟨i, hi, j, ⟨hj, hij, hc⟩, rfl⟩

theorem acCnf_eval_iff (c : ℕ → ℕ → Bool) (a : Fin N → Bool) :
    (acCnf N c).eval (ext a) = true ↔
      ∀ i j : Fin N, i < j → (c i j || c j i) = true → ¬ (a i = true ∧ a j = true) := by
  have hext : ∀ i (hi : i < N), ext a i = a ⟨i, hi⟩ := fun i hi => by simp [ext, hi]
  unfold CNF.eval
  rw [Array.all_eq_true_iff_forall_mem]
  simp only [acCnf, List.mem_toArray]
  constructor
  · intro h i j hij hc ⟨hi, hj⟩
    have := h _ (mem_acClauses.2 ⟨i, i.2, j, j.2, hij, hc, rfl⟩)
    simp [CNF.Clause.eval, hext, hi, hj] at this
  · intro h cl hcl
    obtain ⟨i, hi, j, hj, hij, hc, rfl⟩ := mem_acClauses.1 hcl
    have := h ⟨i, hi⟩ ⟨j, hj⟩ hij hc
    simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false, hext i hi,
      hext j hj]
    cases hu : a ⟨i, hi⟩ <;> cases hv : a ⟨j, hj⟩ <;> simp_all

open Classical in
/-- Models of the antichain CNF are the antichains of `X`, for an enumeration `e` whose
    comparison `c` is correct. -/
noncomputable def acEquiv (e : Fin N ≃ X) (c : ℕ → ℕ → Bool)
    (hc : ∀ i j : Fin N, c i j = true ↔ e i ≤ e j) :
    {a : Fin N → Bool // (acCnf N c).eval (ext a) = true} ≃
      {A : Set X // IsAntichain (· ≤ ·) A} where
  toFun a := ⟨{x | a.1 (e.symm x) = true}, by
    intro x hx y hy hxy hle
    simp only [Set.mem_setOf_eq] at hx hy
    have h := (acCnf_eval_iff c a.1).1 a.2
    have hne : e.symm x ≠ e.symm y := fun h' => hxy (e.symm.injective h')
    have hcmp : c (e.symm x) (e.symm y) = true := by rw [hc]; simpa using hle
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h _ _ hlt (by simp [hcmp]) ⟨hx, hy⟩
    · exact h _ _ hlt (by simp [hcmp]) ⟨hy, hx⟩⟩
  invFun A := ⟨fun i => decide (e i ∈ A.1), by
    rw [acCnf_eval_iff]
    rintro i j hij hcij ⟨hi, hj⟩
    simp only [decide_eq_true_eq] at hi hj
    have hne : e i ≠ e j := fun h => (ne_of_lt hij) (e.injective h)
    rw [Bool.or_eq_true, hc, hc] at hcij
    rcases hcij with h | h
    · exact A.2 hi hj hne h
    · exact A.2 hj hi hne.symm h⟩
  left_inv a := by ext i; simp
  right_inv A := by ext x; simp

end Antichain

/-! ## The encoder and the family lemma -/

/-- The encoder: one variable per noncrossing partition of `Fin n`, one clause `¬x_i ∨ ¬x_j` per
    comparable pair `i < j`. -/
def cnf (n : ℕ) : CNF ℕ := acCnf (ncList n).length (cmp (ncList n))

/-- Family lemma: models of the encoder are the antichains of NC(n). -/
noncomputable def equiv (n : ℕ) :
    {a : Fin (ncList n).length → Bool // (cnf n).eval (ext a) = true} ≃
      {A : Set {r : Setoid (Fin n) // r.IsNoncrossing} // IsAntichain (· ≤ ·) A} :=
  acEquiv (ncEquiv n) (cmp (ncList n)) (cmp_iff n)

/-- A certificate for the encoder counts the antichains of the Kreweras lattice NC(n). -/
theorem card_of_check {n : ℕ} {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (ncList n).length (cnf n) pogStr lratStr N = true) :
    Nat.card {A : Set {r : Setoid (Fin n) // r.IsNoncrossing} // IsAntichain (· ≤ ·) A} = N :=
  Family.card_of_check (equiv n) h

/-- The same with part B as a separate (streamed) refutation, for large certificates. -/
theorem card_of_checkAC {n : ℕ} {pogStr : String} {N : ℕ}
    (h : checkAllAC (ncList n).length (cnf n) pogStr N = true)
    (hB : (fwdCnfOf (cnf n) pogStr).Unsat) :
    Nat.card {A : Set {r : Setoid (Fin n) // r.IsNoncrossing} // IsAntichain (· ≤ ·) A} = N :=
  Family.card_of_checkAC (equiv n) h hB

/-! ## The same statement over `Finpartition`

Mathlib's `Finpartition (Finset.univ : Finset α)` with its refinement order is order-isomorphic
to `Setoid α` (`P ↦ Setoid.ker P.part`); the noncrossing condition reads the same through
`P.part`. The same encoder and certificate then count the antichains of NC(n) as a poset of
`Finpartition`s. -/

section Finpartition

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem fp_mem_part_iff (P : Finpartition (Finset.univ : Finset α)) {a b : α} :
    b ∈ P.part a ↔ P.part a = P.part b := by
  rw [P.mem_part_iff_part_eq_part (Finset.mem_univ b) (Finset.mem_univ a), eq_comm]

theorem fp_ext_part {P Q : Finpartition (Finset.univ : Finset α)} (h : ∀ a, P.part a = Q.part a) :
    P = Q := by
  have key : ∀ R : Finpartition (Finset.univ : Finset α), R.parts = Finset.univ.image R.part := by
    intro R
    ext t
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro ht
      obtain ⟨a, -, ha⟩ := R.part_surjOn ht
      exact ⟨a, ha⟩
    · rintro ⟨a, rfl⟩
      exact R.part_mem.2 (Finset.mem_univ a)
  apply Finpartition.ext
  rw [key P, key Q]
  simp only [funext h]

open Classical in
/-- Finpartitions of `univ` are the equivalence relations, refinement for refinement. -/
noncomputable def finpartitionOrderIso : Finpartition (Finset.univ : Finset α) ≃o Setoid α where
  toFun P := Setoid.ker P.part
  invFun r := Finpartition.ofSetoid r
  left_inv P := by
    apply fp_ext_part
    intro a
    ext b
    rw [Finpartition.mem_part_ofSetoid_iff_rel, Setoid.ker_def, fp_mem_part_iff]
  right_inv r := by
    ext a b
    rw [Setoid.ker_def, ← fp_mem_part_iff, Finpartition.mem_part_ofSetoid_iff_rel]
  map_rel_iff' {P Q} := by
    simp only [Equiv.coe_fn_mk, Setoid.le_def, Setoid.ker_def]
    constructor
    · intro h b hb
      obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hb
      have hbx : P.part x = b := P.part_eq_of_mem hb hx
      refine ⟨Q.part x, Q.part_mem.2 (Finset.mem_univ x), fun y hy => ?_⟩
      have hy' : P.part x = P.part y := by rw [hbx]; exact (P.part_eq_of_mem hb hy).symm
      rw [fp_mem_part_iff]
      exact h hy'
    · intro h x y hxy
      obtain ⟨c, hc, hsub⟩ := h (P.part_mem.2 (Finset.mem_univ x))
      have hx : Q.part x = c := Q.part_eq_of_mem hc (hsub (P.mem_part (Finset.mem_univ x)))
      have hy : Q.part y = c :=
        Q.part_eq_of_mem hc (hsub (by rw [hxy]; exact P.mem_part (Finset.mem_univ y)))
      rw [hx, hy]

end Finpartition

namespace Fp

/-- Index `i` of `ncList n` as a noncrossing `Finpartition`. -/
noncomputable def ncEquiv (n : ℕ) :
    Fin (ncList n).length ≃ {P : Finpartition (Finset.univ : Finset (Fin n)) // P.IsNoncrossing} :=
  (Kreweras.ncEquiv n).trans (finpartitionOrderIso.symm.toEquiv.subtypeEquiv fun r => by
    change r.IsNoncrossing ↔ (finpartitionOrderIso (finpartitionOrderIso.symm r)).IsNoncrossing
    rw [OrderIso.apply_symm_apply])

theorem cmp_iff (n : ℕ) (i j : Fin (ncList n).length) :
    cmp (ncList n) i j = true ↔ ncEquiv n i ≤ ncEquiv n j := by
  rw [Kreweras.cmp_iff]
  exact (finpartitionOrderIso.symm.le_iff_le).symm

/-- Family lemma over `Finpartition`: the same encoder. -/
noncomputable def equiv (n : ℕ) :
    {a : Fin (ncList n).length → Bool // (cnf n).eval (ext a) = true} ≃
      {A : Set {P : Finpartition (Finset.univ : Finset (Fin n)) // P.IsNoncrossing} //
        IsAntichain (· ≤ ·) A} :=
  acEquiv (ncEquiv n) (cmp (ncList n)) (cmp_iff n)

/-- A certificate for the encoder counts the antichains of NC(n), as `Finpartition`s. -/
theorem card_of_check {n : ℕ} {pogStr lratStr : String} {N : ℕ}
    (h : checkAll (ncList n).length (cnf n) pogStr lratStr N = true) :
    Nat.card {A : Set {P : Finpartition (Finset.univ : Finset (Fin n)) // P.IsNoncrossing} //
      IsAntichain (· ≤ ·) A} = N :=
  Family.card_of_check (equiv n) h

/-- The same with part B as a separate (streamed) refutation. -/
theorem card_of_checkAC {n : ℕ} {pogStr : String} {N : ℕ}
    (h : checkAllAC (ncList n).length (cnf n) pogStr N = true)
    (hB : (fwdCnfOf (cnf n) pogStr).Unsat) :
    Nat.card {A : Set {P : Finpartition (Finset.univ : Finset (Fin n)) // P.IsNoncrossing} //
      IsAntichain (· ≤ ·) A} = N :=
  Family.card_of_checkAC (equiv n) h hB

end Fp

/-- The two statements have the same count (both are the models of `cnf n`), so a theorem for
    one gives the other without a second check. -/
theorem card_eq_card_fp (n : ℕ) :
    Nat.card {A : Set {r : Setoid (Fin n) // r.IsNoncrossing} // IsAntichain (· ≤ ·) A} =
      Nat.card {A : Set {P : Finpartition (Finset.univ : Finset (Fin n)) // P.IsNoncrossing} //
        IsAntichain (· ≤ ·) A} :=
  Nat.card_congr ((equiv n).symm.trans (Fp.equiv n))

end CountCatcher.Kreweras
