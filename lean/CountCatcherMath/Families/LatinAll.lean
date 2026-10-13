import CountCatcherMath.Families.Latin

/-!
# All Latin squares from the reduced ones

The standard normalization: permute the columns of a Latin square `L` so that row `0` becomes
the identity (`α`, row `0` of `L` as a permutation), then the rows so that column `0` becomes the
identity (`β`, column `α⁻¹ 0` of `L`, a permutation fixing `0`). This is a bijection

  `{L // IsLatin L} ≃ Perm (Fin n) × {β : Perm (Fin n) // β 0 = 0} × {R // IsReducedLatin R}`

(`normEquiv`; inverse `L i j = R (β i) (α j)`), so the number of Latin squares of order `n` is
`n! · (n - 1)!` times the number of reduced ones (`card_latin_eq`). Kept apart from `Latin.lean`
so that the fibre theorems compiled against `Latin.lean` stay valid.
-/

open Equiv

namespace CountCatcher.Latin

variable {n : ℕ}

theorem isLatin_relabel {L : Fin n → Fin n → Fin n} (hL : IsLatin L) (ρ γ : Perm (Fin n)) :
    IsLatin fun i j => L (ρ i) (γ j) :=
  ⟨fun i => (hL.1 (ρ i)).comp γ.bijective, fun j => (hL.2 (γ j)).comp ρ.bijective⟩

section Normalize
variable [NeZero n]

/-- Row `0` of a Latin square as a permutation. -/
noncomputable def row0 (L : {L : Fin n → Fin n → Fin n // IsLatin L}) : Perm (Fin n) :=
  Equiv.ofBijective (L.1 0) (L.2.1 0)

/-- Column `j` of a Latin square as a permutation. -/
noncomputable def colPerm (L : {L : Fin n → Fin n → Fin n // IsLatin L}) (j : Fin n) :
    Perm (Fin n) :=
  Equiv.ofBijective (fun i => L.1 i j) (L.2.2 j)

@[simp] theorem row0_apply (L : {L : Fin n → Fin n → Fin n // IsLatin L}) (j : Fin n) :
    row0 L j = L.1 0 j := rfl

omit [NeZero n] in
@[simp] theorem colPerm_apply (L : {L : Fin n → Fin n → Fin n // IsLatin L}) (j i : Fin n) :
    colPerm L j i = L.1 i j := rfl

/-- The row permutation `β`: column `α⁻¹ 0`, which fixes `0`. -/
noncomputable def beta (L : {L : Fin n → Fin n → Fin n // IsLatin L}) :
    {β : Perm (Fin n) // β 0 = 0} :=
  ⟨colPerm L ((row0 L).symm 0), by
    rw [colPerm_apply, ← row0_apply, Equiv.apply_symm_apply]⟩

/-- The reduced square `R i j = L (β⁻¹ i) (α⁻¹ j)`. -/
noncomputable def reduce (L : {L : Fin n → Fin n → Fin n // IsLatin L}) :
    {R : Fin n → Fin n → Fin n // IsReducedLatin R} :=
  ⟨fun i j => L.1 ((beta L).1.symm i) ((row0 L).symm j),
    isLatin_relabel L.2 _ _,
    fun j => by
      have h0 : (beta L).1.symm 0 = 0 := by
        rw [Equiv.symm_apply_eq]; exact (beta L).2.symm
      simp only [h0]
      rw [← row0_apply, Equiv.apply_symm_apply],
    fun i => by
      show L.1 ((beta L).1.symm i) ((row0 L).symm 0) = i
      rw [← colPerm_apply]
      exact (beta L).1.apply_symm_apply i⟩

/-- The square of a column permutation `α`, a row permutation `β` fixing `0`, and a reduced
    square `R`: `L i j = R (β i) (α j)`. -/
def unreduce (x : Perm (Fin n) × {β : Perm (Fin n) // β 0 = 0} ×
    {R : Fin n → Fin n → Fin n // IsReducedLatin R}) :
    {L : Fin n → Fin n → Fin n // IsLatin L} :=
  ⟨fun i j => x.2.2.1 (x.2.1.1 i) (x.1 j), isLatin_relabel x.2.2.2.1 _ _⟩

/-- The normalization bijection. -/
noncomputable def normEquiv :
    {L : Fin n → Fin n → Fin n // IsLatin L} ≃
      Perm (Fin n) × {β : Perm (Fin n) // β 0 = 0} ×
        {R : Fin n → Fin n → Fin n // IsReducedLatin R} where
  toFun L := (row0 L, beta L, reduce L)
  invFun := unreduce
  left_inv L := by
    apply Subtype.ext
    funext i j
    simp only [unreduce, reduce, Equiv.symm_apply_apply]
  right_inv x := by
    obtain ⟨α, ⟨β, hβ⟩, ⟨R, hR⟩⟩ := x
    set L := unreduce (α, ⟨β, hβ⟩, ⟨R, hR⟩) with hL
    have hLv : ∀ i j, L.1 i j = R (β i) (α j) := fun _ _ => rfl
    have hα : row0 L = α := by
      ext j
      simp only [row0_apply, hLv, hβ, hR.2.1]
    have hb : (beta L).1 = β := by
      ext i
      simp only [beta, hα, colPerm_apply, hLv, Equiv.apply_symm_apply, hR.2.2]
    refine Prod.ext hα (Prod.ext (Subtype.ext hb) (Subtype.ext ?_))
    funext i j
    simp only [reduce, hα, hb, hLv, Equiv.apply_symm_apply]

/-- The permutations of `Fin (m + 1)` fixing `0` are as many as the permutations of `Fin m`. -/
theorem card_perm_fix_zero (m : ℕ) :
    Fintype.card {β : Perm (Fin (m + 1)) // β 0 = 0} = m.factorial := by
  classical
  have e : {β : Perm (Fin (m + 1)) // β 0 = 0} ≃ Perm (Fin m) :=
    (Equiv.subtypeEquiv Equiv.Perm.decomposeFin.symm
      (p := fun x : Fin (m + 1) × Perm (Fin m) => x.1 = 0)
      (q := fun β : Perm (Fin (m + 1)) => β 0 = 0)
      (fun ⟨p, σ⟩ => by simp [Equiv.Perm.decomposeFin_symm_apply_zero])).symm.trans
      { toFun := fun x => x.1.2
        invFun := fun σ => ⟨(0, σ), rfl⟩
        left_inv := fun x => by obtain ⟨⟨p, σ⟩, hp⟩ := x; obtain rfl : p = 0 := hp; rfl
        right_inv := fun σ => rfl }
  rw [Fintype.card_congr e, Fintype.card_perm, Fintype.card_fin]

/-- The number of Latin squares of order `n` is `n! · (n - 1)!` times the number of reduced ones. -/
theorem card_latin_eq :
    Nat.card {L : Fin n → Fin n → Fin n // IsLatin L} =
      n.factorial * (n - 1).factorial *
        Nat.card {L : Fin n → Fin n → Fin n // IsReducedLatin L} := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩
  rw [Nat.card_congr normEquiv, Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin, Nat.card_eq_fintype_card (α := {β : Perm (Fin (m + 1)) // β 0 = 0}),
    card_perm_fix_zero, Nat.add_sub_cancel, Nat.mul_assoc]

end Normalize

end CountCatcher.Latin
