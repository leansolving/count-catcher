import CountCatcherMath.Check
import CountCatcherMath.Symmetry
import CountCatcherMath.Family

/-!
# Certified divide-and-conquer counting

For a formula `F` over the universe `Fin V`, a list `ls` of literals and a variable `x`,

  `#(F ∧ ls) = #(F ∧ ls ∧ x) + #(F ∧ ls ∧ ¬x)`   (`card_split`)

over the same universe: the assigned variables stay in the universe and are fixed by unit
clauses (`cube F ls = F ++ units`), so no variable is eliminated and no multiplicity
correction is needed. `x` need not lie in the universe (outside it `ext` is `false`, and the
identity still holds).

A `SplitTree` is a complete binary tree whose inner nodes name the split variable and whose
leaves carry claimed counts. `SplitTree.Holds V F ls t` says that every leaf count is the
model count of `F` plus the unit clauses of its path (the literals from the leaf up to the
root, then `ls`). `card_eq_total` composes the leaf theorems into the count of `cube F ls`,
and `card_eq_of_tree` into the count of `F`. Coverage and disjointness follow from the tree
shape alone, so the heuristic that chose the variables is not trusted. Leaf theorems come from
`count_models` (a certificate) or from an LRAT refutation (count 0), stated for the term
`cube F ls` with the leaf's literal list written out.
-/

open Std.Sat

namespace CountCatcher

/-- `F` followed by one unit clause per literal of `ls`, in list order. -/
def cube (F : CNF ℕ) (ls : List (ℕ × Bool)) : CNF ℕ :=
  F ++ ⟨(ls.map fun l => [l]).toArray⟩

theorem eval_cube (F : CNF ℕ) (ls : List (ℕ × Bool)) (v : ℕ → Bool) :
    (cube F ls).eval v = (F.eval v && ls.all fun l => v l.1 == l.2) := by
  simp only [cube, CNF.eval_append]
  congr 1
  simp [CNF.eval, CNF.Clause.eval, Function.comp_def]

theorem eval_cube_nil (F : CNF ℕ) (v : ℕ → Bool) : (cube F []).eval v = F.eval v := by
  simp [eval_cube]

theorem eval_cube_cons (F : CNF ℕ) (l : ℕ × Bool) (ls : List (ℕ × Bool)) (v : ℕ → Bool) :
    (cube F (l :: ls)).eval v = ((v l.1 == l.2) && (cube F ls).eval v) := by
  simp only [eval_cube, List.all_cons]
  cases F.eval v <;> cases (v l.1 == l.2) <;> simp

/-- One split: the models of `cube F ls` are those with `x` true plus those with `x` false. -/
theorem card_split (V : ℕ) (F : CNF ℕ) (ls : List (ℕ × Bool)) (x : ℕ) :
    Fintype.card {a : Fin V → Bool // (cube F ls).eval (ext a) = true} =
      Fintype.card {a : Fin V → Bool // (cube F ((x, true) :: ls)).eval (ext a) = true} +
      Fintype.card {a : Fin V → Bool // (cube F ((x, false) :: ls)).eval (ext a) = true} := by
  classical
  rw [← Fintype.card_subtype_or_disjoint]
  · apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro a
    simp only [eval_cube_cons]
    cases ext a x <;> simp
  · rw [disjoint_iff]
    funext a
    simp only [Pi.inf_apply, Pi.bot_apply, inf_Prop_eq, Prop.bot_eq_false, eq_iff_iff,
      iff_false, eval_cube_cons]
    cases ext a x <;> simp

theorem card_cube_nil (V : ℕ) (F : CNF ℕ) :
    Fintype.card {a : Fin V → Bool // (cube F []).eval (ext a) = true} =
      Fintype.card {a : Fin V → Bool // F.eval (ext a) = true} := by
  simp only [eval_cube_nil]

/-- A binary partition tree: inner nodes name the split variable (left: true, right: false),
    leaves carry the claimed model count of their cube. -/
inductive SplitTree where
  | leaf (N : ℕ)
  | node (x : ℕ) (pos neg : SplitTree)

namespace SplitTree

/-- The sum of the leaf counts. -/
def total : SplitTree → ℕ
  | leaf N => N
  | node _ p n => p.total + n.total

/-- Every leaf's count is the model count over `Fin V` of `F` plus the unit clauses of its
    path; the literal of the deepest split comes first, `ls` last. -/
def Holds (V : ℕ) (F : CNF ℕ) : List (ℕ × Bool) → SplitTree → Prop
  | ls, leaf N => Fintype.card {a : Fin V → Bool // (cube F ls).eval (ext a) = true} = N
  | ls, node x p n => Holds V F ((x, true) :: ls) p ∧ Holds V F ((x, false) :: ls) n

theorem Holds.mk_leaf {V : ℕ} {F : CNF ℕ} {ls : List (ℕ × Bool)} {N : ℕ}
    (h : Fintype.card {a : Fin V → Bool // (cube F ls).eval (ext a) = true} = N) :
    (leaf N).Holds V F ls := h

theorem Holds.mk_node {V : ℕ} {F : CNF ℕ} {ls : List (ℕ × Bool)} {x : ℕ} {p n : SplitTree}
    (hp : p.Holds V F ((x, true) :: ls)) (hn : n.Holds V F ((x, false) :: ls)) :
    (node x p n).Holds V F ls := ⟨hp, hn⟩

/-- Composition along the tree. -/
theorem card_eq_total {V : ℕ} {F : CNF ℕ} :
    ∀ (t : SplitTree) (ls : List (ℕ × Bool)), t.Holds V F ls →
      Fintype.card {a : Fin V → Bool // (cube F ls).eval (ext a) = true} = t.total
  | leaf _, _, h => h
  | node x p n, ls, h => by
    rw [card_split V F ls x, card_eq_total p _ h.1, card_eq_total n _ h.2]
    rfl

/-- The count of `F` from the leaf theorems of a tree rooted at `F` itself. -/
theorem card_eq_of_tree {V : ℕ} {F : CNF ℕ} (t : SplitTree) (h : t.Holds V F []) {N : ℕ}
    (hN : t.total = N) : Fintype.card {a : Fin V → Bool // F.eval (ext a) = true} = N := by
  rw [← card_cube_nil, card_eq_total t [] h, hN]

/-- The same for a family: `e` identifies the models of the encoder with the objects. -/
theorem natCard_eq_of_tree {X : Type*} {V : ℕ} {F : CNF ℕ}
    (e : {a : Fin V → Bool // F.eval (ext a) = true} ≃ X) (t : SplitTree)
    (h : t.Holds V F []) {N : ℕ} (hN : t.total = N) : Nat.card X = N := by
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, card_eq_of_tree t h hN]

/-- Number of leaves. -/
def leaves : SplitTree → ℕ
  | leaf _ => 1
  | node _ p n => p.leaves + n.leaves

end SplitTree

end CountCatcher
