import Mathlib.Tactic

/-!
# CountCatcherMath.Indep — independence of events on disjoint coordinate sets

For assignments `Fin V → Bool`: if `p` depends only on the coordinates in `S`, `q` only on
those in `T`, and `S`, `T` are disjoint, then `#{p ∧ q} · 2^V = #{p} · #{q}`.
Proof: the involution `(a, b) ↦ (splice a b, splice b a)` on pairs, where `splice a b` takes
`S` from `a` and the rest from `b`, maps `{p a ∧ q b}` onto `{p c ∧ q c}`.
-/

open Finset

namespace CountCatcher

variable {V : Nat}

/-- Take the coordinates in `S` from `a` and the others from `b`. -/
def splice (S : Finset (Fin V)) (a b : Fin V → Bool) : Fin V → Bool :=
  fun i => if i ∈ S then a i else b i

theorem splice_splice (S : Finset (Fin V)) (a b : Fin V → Bool) :
    splice S (splice S a b) (splice S b a) = a := by
  funext i; simp only [splice]; split_ifs <;> rfl

/-- The swap of `S`-parts as an equivalence on pairs (an involution). -/
def spliceEquiv (S : Finset (Fin V)) : (Fin V → Bool) × (Fin V → Bool) ≃ (Fin V → Bool) × (Fin V → Bool) where
  toFun x := (splice S x.1 x.2, splice S x.2 x.1)
  invFun x := (splice S x.1 x.2, splice S x.2 x.1)
  left_inv x := by simp [splice_splice]
  right_inv x := by simp [splice_splice]

theorem card_univ_assign : (univ : Finset (Fin V → Bool)).card = 2 ^ V := by
  simp

theorem card_and_mul (S T : Finset (Fin V)) (hST : Disjoint S T)
    (p q : (Fin V → Bool) → Prop) [DecidablePred p] [DecidablePred q]
    (hp : ∀ a b, (∀ i ∈ S, a i = b i) → (p a ↔ p b))
    (hq : ∀ a b, (∀ i ∈ T, a i = b i) → (q a ↔ q b)) :
    (univ.filter fun a => p a ∧ q a).card * 2 ^ V = (univ.filter p).card * (univ.filter q).card := by
  -- pairs with p on the first and q on the second component
  have h1 : (univ.filter fun x : (Fin V → Bool) × (Fin V → Bool) => p x.1 ∧ q x.2).card =
      (univ.filter p).card * (univ.filter q).card := by
    rw [← card_product]; congr 1; ext x; simp
  -- pairs with p and q on the first component
  have h2 : (univ.filter fun x : (Fin V → Bool) × (Fin V → Bool) => p x.1 ∧ q x.1).card =
      (univ.filter fun a => p a ∧ q a).card * 2 ^ V := by
    rw [← card_univ_assign, ← card_product]; congr 1; ext x; simp
  -- the swap maps one set onto the other
  have h3 : (univ.filter fun x : (Fin V → Bool) × (Fin V → Bool) => p x.1 ∧ q x.2).card =
      (univ.filter fun x : (Fin V → Bool) × (Fin V → Bool) => p x.1 ∧ q x.1).card := by
    apply card_equiv (spliceEquiv S)
    intro x
    simp only [mem_filter, mem_univ, true_and, spliceEquiv, Equiv.coe_fn_mk]
    have e1 : p (splice S x.1 x.2) ↔ p x.1 :=
      hp _ _ fun i hi => by simp [splice, hi]
    have e2 : q (splice S x.1 x.2) ↔ q x.2 :=
      hq _ _ fun i hi => by simp [splice, Finset.disjoint_right.1 hST hi]
    rw [e1, e2]
  rw [← h2, ← h3, h1]

end CountCatcher
