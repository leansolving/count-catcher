import CountCatcherMath.Symmetry
import CountCatcherMath.Families.Queens
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# n-queens up to the symmetries of the square

The dihedral group `DihedralGroup 4` acts on the cells `Fin n × Fin n` of the board: `r 1`
is the quarter turn `(r, c) ↦ (c, n - 1 - r)`, `sr 0` the reflection `(r, c) ↦ (r, n - 1 - c)`,
and `sr i = sr 0 * r i`. It acts on the n-queens solutions, taken as sets of `n` cells no two
of which attack each other (`Solution n`), by moving every queen. The solutions correspond to
the models of the encoder `cnf n` (`solEquiv`, and `solEquivSafe` to the placements of
`Queens.card_of_check`), the action of `g` on a solution is the variable map `cellPerm n g` on
its model, and `card_orbits_mul_eight` gives the number of orbits (OEIS A002562) as one eighth
of the sum of the certified model counts of `symCnf (cnf n) (n * n) (cellPerm n g)`.
-/

open Std.Sat
open scoped Pointwise

namespace CountCatcher.Queens

variable {n : ℕ}

/-! ## The symmetries of the board -/

/-- A symmetry of the board as `(t, u, w)`: transpose if `t`, then reverse the row index if `u`
    and the column index if `w`. -/
abbrev BoardSym := Bool × Bool × Bool

def BoardSym.apply (s : BoardSym) (p : Fin n × Fin n) : Fin n × Fin n :=
  let q := if s.1 then (p.2, p.1) else p
  (if s.2.1 then q.1.rev else q.1, if s.2.2 then q.2.rev else q.2)

/-- Composition: `(s.comp t).apply = s.apply ∘ t.apply`. -/
def BoardSym.comp (s t : BoardSym) : BoardSym :=
  (s.1 != t.1, s.2.1 != (if s.1 then t.2.2 else t.2.1), s.2.2 != (if s.1 then t.2.1 else t.2.2))

theorem BoardSym.apply_comp (s t : BoardSym) (p : Fin n × Fin n) :
    (s.comp t).apply p = s.apply (t.apply p) := by
  obtain ⟨a, b, c⟩ := s
  obtain ⟨d, e, f⟩ := t
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    simp [BoardSym.apply, BoardSym.comp]

/-- The elements of `DihedralGroup 4` as board symmetries: `r i` is `i` quarter turns
    `(r, c) ↦ (c, n - 1 - r)`, and `sr i` is `r i` followed by `(r, c) ↦ (r, n - 1 - c)`. -/
def symOf : DihedralGroup 4 → BoardSym
  | .r i => match i.val with
    | 0 => (false, false, false)
    | 1 => (true, false, true)
    | 2 => (false, true, true)
    | _ => (true, true, false)
  | .sr i => match i.val with
    | 0 => (false, false, true)
    | 1 => (true, false, false)
    | 2 => (false, true, false)
    | _ => (true, true, true)

theorem symOf_mul : ∀ g h : DihedralGroup 4, symOf (g * h) = (symOf g).comp (symOf h) := by
  decide

instance : MulAction (DihedralGroup 4) (Fin n × Fin n) where
  smul g p := (symOf g).apply p
  one_smul p := by
    show (symOf 1).apply p = p
    rw [show symOf 1 = (false, false, false) from rfl]
    simp [BoardSym.apply]
  mul_smul g h p := by
    show (symOf (g * h)).apply p = (symOf g).apply ((symOf h).apply p)
    rw [symOf_mul, BoardSym.apply_comp]

theorem smul_def (g : DihedralGroup 4) (p : Fin n × Fin n) : g • p = (symOf g).apply p := rfl

/-- `r 1` is the quarter turn. -/
theorem r_one_smul (p : Fin n × Fin n) : (DihedralGroup.r 1 : DihedralGroup 4) • p = (p.2, p.1.rev) :=
  rfl

/-- `sr 0` is the reflection that reverses the columns. -/
theorem sr_zero_smul (p : Fin n × Fin n) :
    (DihedralGroup.sr 0 : DihedralGroup 4) • p = (p.1, p.2.rev) :=
  rfl

/-! ## Solutions as sets of cells -/

/-- Two cells in a common row, column, diagonal or anti-diagonal. -/
def Attack (p q : Fin n × Fin n) : Prop :=
  p.1 = q.1 ∨ p.2 = q.2 ∨ (p.1 : ℕ) + q.2 = q.1 + p.2 ∨ (p.1 : ℕ) + p.2 = q.1 + q.2

/-- An n-queens solution: `n` cells, no two of which attack each other. -/
def IsSolution (s : Finset (Fin n × Fin n)) : Prop :=
  s.card = n ∧ ∀ p ∈ s, ∀ q ∈ s, p ≠ q → ¬ Attack p q

/-- The n-queens solutions. -/
abbrev Solution (n : ℕ) := {s : Finset (Fin n × Fin n) // IsSolution s}

theorem BoardSym.attack_apply (s : BoardSym) (p q : Fin n × Fin n) :
    Attack (s.apply p) (s.apply q) ↔ Attack p q := by
  obtain ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩ := p
  obtain ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ := q
  obtain ⟨a, b, c⟩ := s
  cases a <;> cases b <;> cases c <;>
    simp only [Attack, BoardSym.apply, Fin.ext_iff, Fin.val_rev, ite_true, ite_false,
      Bool.false_eq_true] <;> omega

theorem attack_smul (g : DihedralGroup 4) (p q : Fin n × Fin n) :
    Attack (g • p) (g • q) ↔ Attack p q := BoardSym.attack_apply _ p q

theorem isSolution_smul (g : DihedralGroup 4) {s : Finset (Fin n × Fin n)} (h : IsSolution s) :
    IsSolution (g • s) := by
  refine ⟨by rw [Finset.card_smul_finset]; exact h.1, ?_⟩
  intro p hp q hq hpq
  obtain ⟨p', hp', rfl⟩ := Finset.mem_smul_finset.1 hp
  obtain ⟨q', hq', rfl⟩ := Finset.mem_smul_finset.1 hq
  rw [attack_smul]
  exact h.2 p' hp' q' hq' fun h' => hpq (h' ▸ rfl)

/-- The dihedral group moves every queen of a solution. -/
instance : MulAction (DihedralGroup 4) (Solution n) where
  smul g s := ⟨g • s.1, isSolution_smul g s.2⟩
  one_smul s := Subtype.ext (one_smul _ s.1)
  mul_smul g h s := Subtype.ext (mul_smul g h s.1)

theorem coe_smul_solution (g : DihedralGroup 4) (s : Solution n) : (g • s).1 = g • s.1 := rfl

/-! ## Cells and variables -/

/-- The variable of cell `p` in the encoder. -/
def cellVar (p : Fin n × Fin n) : ℕ := p.1 * n + p.2

theorem cellVar_lt (p : Fin n × Fin n) : cellVar p < n * n := cell_lt p.1.2 p.2.2

/-- The cell of a variable `x < n * n`. -/
def varCell (x : ℕ) (hx : x < n * n) : Fin n × Fin n :=
  (⟨x / n, Nat.div_lt_of_lt_mul hx⟩,
    ⟨x % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.div_lt_of_lt_mul hx))⟩)

theorem cellVar_varCell (x : ℕ) (hx : x < n * n) : cellVar (varCell x hx) = x :=
  Nat.div_add_mod' x n

theorem varCell_cellVar (p : Fin n × Fin n) : varCell (cellVar p) (cellVar_lt p) = p := by
  obtain ⟨r, c⟩ := p
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) r.2
  simp only [varCell, cellVar, Prod.mk.injEq, Fin.ext_iff]
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt c.2, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt c.2]

theorem varCell_eq_iff {x : ℕ} (hx : x < n * n) {p : Fin n × Fin n} :
    varCell x hx = p ↔ x = cellVar p := by
  constructor
  · rintro rfl; exact (cellVar_varCell x hx).symm
  · rintro rfl; exact varCell_cellVar p

/-- The variable map of `g`: the variable of cell `p` goes to the variable of `g • p`. -/
def cellPerm (n : ℕ) (g : DihedralGroup 4) (x : ℕ) : ℕ :=
  if hx : x < n * n then cellVar (g • varCell x hx) else x

/-! ## Solutions and models -/

/-- The model of a set of cells. -/
def solModel (s : Finset (Fin n × Fin n)) (x : Fin (n * n)) : Bool := decide (varCell x x.2 ∈ s)

theorem ext_solModel (s : Finset (Fin n × Fin n)) (p : Fin n × Fin n) :
    ext (solModel s) (cellVar p) = decide (p ∈ s) := by
  simp [ext, cellVar_lt p, solModel, varCell_cellVar]

/-- The cells set to true by a model. -/
def modelSol (a : Fin (n * n) → Bool) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => ext a (cellVar p) = true

theorem ext_cell (v : ℕ → Bool) {r c : ℕ} (hr : r < n) (hc : c < n) :
    v (r * n + c) = v (cellVar ((⟨r, hr⟩, ⟨c, hc⟩) : Fin n × Fin n)) := rfl

theorem solModel_model {s : Finset (Fin n × Fin n)} (hs : IsSolution s) :
    (cnf n).eval (ext (solModel s)) = true := by
  have hinj : ∀ p ∈ s, ∀ q ∈ s, Attack p q → p = q := fun p hp q hq h =>
    Classical.byContradiction fun hpq => hs.2 p hp q hq hpq h
  rw [eval_iff]
  refine ⟨fun r hr => ?_, fun r c r' c' hr hc hr' hc' hv hv' ht => ?_⟩
  · -- every row holds a queen: the rows of the `n` queens are distinct
    have himg : s.image Prod.fst = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn fun p hp q hq h => hinj p hp q hq (Or.inl h), hs.1,
        Fintype.card_fin]
    obtain ⟨p, hp, hpr⟩ := Finset.mem_image.1 (himg ▸ Finset.mem_univ (⟨r, hr⟩ : Fin n))
    refine ⟨p.2, p.2.2, ?_⟩
    have : p = (⟨r, hr⟩, p.2) := Prod.ext hpr rfl
    rw [ext_cell (ext (solModel s)) hr p.2.2, ← this, ext_solModel]
    simpa using hp
  · rw [ext_cell (ext (solModel s)) hr hc, ext_solModel, decide_eq_true_eq] at hv
    rw [ext_cell (ext (solModel s)) hr' hc', ext_solModel, decide_eq_true_eq] at hv'
    have := hinj _ hv _ hv' (by simpa [Attack] using ht)
    simp only [Prod.mk.injEq, Fin.mk.injEq] at this
    exact this

theorem modelSol_isSolution {a : Fin (n * n) → Bool} (ha : (cnf n).eval (ext a) = true) :
    IsSolution (modelSol a) := by
  obtain ⟨halo, hatt⟩ := (eval_iff _).1 ha
  have hmem : ∀ p, p ∈ modelSol a ↔ ext a (cellVar p) = true := by simp [modelSol]
  have heq : ∀ p ∈ modelSol a, ∀ q ∈ modelSol a, Attack p q → p = q := by
    intro p hp q hq h
    obtain ⟨h1, h2⟩ := hatt p.1 p.2 q.1 q.2 p.1.2 p.2.2 q.1.2 q.2.2 ((hmem p).1 hp)
      ((hmem q).1 hq) (by simpa [Attack, Fin.ext_iff] using h)
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  refine ⟨?_, fun p hp q hq hpq h => hpq (heq p hp q hq h)⟩
  calc (modelSol a).card = (Finset.univ : Finset (Fin n)).card := by
        apply Finset.card_bij (fun p _ => p.1) (fun _ _ => Finset.mem_univ _)
        · intro p hp q hq h
          exact heq p hp q hq (Or.inl h)
        · intro r _
          obtain ⟨c, hc, hv⟩ := halo r r.2
          exact ⟨(r, ⟨c, hc⟩), (hmem _).2 hv, rfl⟩
    _ = n := by simp

/-- Family lemma: the solutions are the models of the encoder. -/
def solEquiv : Solution n ≃ {a : Fin (n * n) → Bool // (cnf n).eval (ext a) = true} where
  toFun s := ⟨solModel s.1, solModel_model s.2⟩
  invFun a := ⟨modelSol a.1, modelSol_isSolution a.2⟩
  left_inv s := by
    apply Subtype.ext
    ext p
    simp [modelSol, ext_solModel]
  right_inv a := by
    apply Subtype.ext
    funext x
    show decide (varCell x x.2 ∈ modelSol a.1) = a.1 x
    have h : ext a.1 (cellVar (varCell x x.2)) = a.1 x := by
      rw [cellVar_varCell]; simp [ext, x.2]
    simp [modelSol, h]

/-- The link to the placements of `Queens.card_of_check`. -/
noncomputable def solEquivSafe : Solution n ≃ {f : Fin n → Fin n // Safe f} :=
  solEquiv.trans equiv

theorem solEquiv_smul (g : DihedralGroup 4) (s : Solution n) (i : ℕ) (hi : i < n * n) :
    ext (solEquiv (g • s)).1 (cellPerm n g i) = ext (solEquiv s).1 i := by
  show ext (solModel (g • s.1)) _ = ext (solModel s.1) i
  have h := ext_solModel s.1 (varCell i hi)
  rw [cellVar_varCell] at h
  rw [cellPerm, dif_pos hi, ext_solModel, h]
  simp only [Finset.smul_mem_smul_finset_iff]

theorem cellPerm_onto (g : DihedralGroup 4) (j : ℕ) (hj : j < n * n) :
    ∃ i < n * n, cellPerm n g i = j := by
  refine ⟨cellVar (g⁻¹ • varCell j hj), cellVar_lt _, ?_⟩
  rw [cellPerm, dif_pos (cellVar_lt _), varCell_cellVar, smul_inv_smul, cellVar_varCell]

/-- Burnside for n-queens: eight times the number of solutions up to symmetry is the sum of
    the model counts of the fixed-point formulas. -/
theorem card_orbits_mul_eight :
    Nat.card (MulAction.orbitRel.Quotient (DihedralGroup 4) (Solution n)) * 8 =
      ∑ g : DihedralGroup 4, Fintype.card
        {a : Fin (n * n) → Bool // (symCnf (cnf n) (n * n) (cellPerm n g)).eval (ext a) = true} := by
  have h := card_orbits_mul_card_group solEquiv (cellPerm n) (fun g => cellPerm_onto g)
    (fun g s => solEquiv_smul g s)
  rwa [DihedralGroup.nat_card] at h

/-- The identity term of Burnside's sum is the number of placements of `Queens.card_of_check`. -/
theorem card_fix_one : Fintype.card
    {a : Fin (n * n) → Bool // (symCnf (cnf n) (n * n) (cellPerm n (.r 0))).eval (ext a) = true} =
      Nat.card {f : Fin n → Fin n // Safe f} := by
  rw [← card_fixedBy_eq solEquiv (DihedralGroup.r 0 : DihedralGroup 4) (cellPerm n (.r 0)) (cellPerm_onto _)
    (solEquiv_smul _), DihedralGroup.r_zero, MulAction.fixedBy_one_eq_univ,
    Nat.card_univ, Nat.card_congr solEquivSafe]

/-- The eight elements of `DihedralGroup 4`. -/
theorem sum_dihedral4 {M : Type*} [AddCommMonoid M] (f : DihedralGroup 4 → M) :
    ∑ g, f g = f (.r 0) + f (.r 1) + f (.r 2) + f (.r 3) +
      (f (.sr 0) + f (.sr 1) + f (.sr 2) + f (.sr 3)) := by
  rw [← DihedralGroup.equivSum.symm.sum_comp, Fintype.sum_sum_type]
  exact congrArg₂ (· + ·) (Fin.sum_univ_four _) (Fin.sum_univ_four _)

/-- The number of solutions up to symmetry from the eight terms of Burnside's sum: the
    placement count (`Queens.card_of_check`) and the model counts of the seven fixed-point
    formulas of `g ≠ 1`. -/
theorem card_orbits_eq (N c0 c1 c2 c3 d0 d1 d2 d3 : ℕ)
    (h0 : Nat.card {f : Fin n → Fin n // Safe f} = c0)
    (h1 : Fintype.card {a : Fin (n * n) → Bool //
      (symCnf (cnf n) (n * n) (cellPerm n (.r 1))).eval (ext a) = true} = c1)
    (h2 : Fintype.card {a : Fin (n * n) → Bool //
      (symCnf (cnf n) (n * n) (cellPerm n (.r 2))).eval (ext a) = true} = c2)
    (h3 : Fintype.card {a : Fin (n * n) → Bool //
      (symCnf (cnf n) (n * n) (cellPerm n (.r 3))).eval (ext a) = true} = c3)
    (k0 : Fintype.card {a : Fin (n * n) → Bool //
      (symCnf (cnf n) (n * n) (cellPerm n (.sr 0))).eval (ext a) = true} = d0)
    (k1 : Fintype.card {a : Fin (n * n) → Bool //
      (symCnf (cnf n) (n * n) (cellPerm n (.sr 1))).eval (ext a) = true} = d1)
    (k2 : Fintype.card {a : Fin (n * n) → Bool //
      (symCnf (cnf n) (n * n) (cellPerm n (.sr 2))).eval (ext a) = true} = d2)
    (k3 : Fintype.card {a : Fin (n * n) → Bool //
      (symCnf (cnf n) (n * n) (cellPerm n (.sr 3))).eval (ext a) = true} = d3)
    (hsum : c0 + c1 + c2 + c3 + (d0 + d1 + d2 + d3) = N * 8) :
    Nat.card (MulAction.orbitRel.Quotient (DihedralGroup 4) (Solution n)) = N := by
  have h := card_orbits_mul_eight (n := n)
  rw [sum_dihedral4, card_fix_one, h0, h1, h2, h3, k0, k1, k2, k3, hsum] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

end CountCatcher.Queens
