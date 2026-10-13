import CountCatcherMath.Check
import CountCatcherMath.Symmetry

/-!
# Generic family lemmas: a family is an encoder and an equivalence

For objects `X` and an encoder `F` over the universe `Fin V`, the family lemma is an
equivalence `e : {a : Fin V → Bool // F.eval (ext a) = true} ≃ X`. The three lemmas below turn
the checker's verdicts into `Nat.card X = N`, for embedded certificates (`card_of_check`),
streamed ones (`card_of_checkAC`), and LRAT refutations of `F` (`card_of_unsat`, count 0).

With them a new family needs only the encoder and `e`; `count_models` takes
`via (Family.card_of_check e)` and finds the other two by name (`CountCatcherMath.Command`).
-/

open Std.Sat

namespace CountCatcher.Family

variable {X : Type*} {V : ℕ} {F : CNF ℕ}

theorem card_of_check (e : {a : Fin V → Bool // F.eval (ext a) = true} ≃ X)
    {pogStr lratStr : String} {N : ℕ} (h : checkAll V F pogStr lratStr N = true) :
    Nat.card X = N := by
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, checkAll_sound h]

theorem card_of_checkAC (e : {a : Fin V → Bool // F.eval (ext a) = true} ≃ X)
    {pogStr : String} {N : ℕ} (h : checkAllAC V F pogStr N = true)
    (hB : (fwdCnfOf F pogStr).Unsat) : Nat.card X = N := by
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, checkAllAC_sound h hB]

theorem card_of_unsat (e : {a : Fin V → Bool // F.eval (ext a) = true} ≃ X)
    (h : F.Unsat) : Nat.card X = 0 := by
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, card_eq_zero_of_unsat h]

end CountCatcher.Family
