import CountCatcherMath.Families.GraphIso
import CountCatcherMath.Families.Latin

/-! The Boolean side conditions of the composition theorems reject incomplete or inconsistent
    data. Each group starts with a positive control (the data of a committed theorem), then
    changes one thing so that, where possible, only one conjunct fails. Further cases are in
    `GraphOrbits5.lean` (wrong count, missing, duplicated and unsorted cycle type; missing
    neighbourhood size), `GraphTree5.lean` (wrong cell count, split vertex inside the cell,
    `cellOk`, `patEquiv`) and `Latin5.lean` (a row replaced by a duplicate). -/

open CountCatcher CountCatcher.GraphIso CountCatcher.CycleType CountCatcher.Latin

/-! Burnside (`checkClasses`, `CycleType.card_orbits_eq`) with the triangle-free data of
    `GraphOrbits5.lean` (14 classes; class sizes in `S_5`: 24, 30, 20, 20, 15, 10, 1). -/

example : checkClasses 5 14
    [([5], 3), ([4], 4), ([3, 2], 3), ([3], 7), ([2, 2], 28), ([2], 48), ([], 388)] = true := by
  decide

-- The cycle type `[3, 2]` is missing and its share of Burnside's sum (20 · 3) moved to `[3]`
-- (also 20 elements): the sum is still `14 · 5!`, the class sizes add up to 100, not 120.
example : checkClasses 5 14
    [([5], 3), ([4], 4), ([3], 10), ([2, 2], 28), ([2], 48), ([], 388)] = false := by
  decide

-- Not a cycle type: a part of size 1, and parts that add up to more than 5.
example : checkClasses 5 14
    [([5], 3), ([4], 4), ([3, 2], 3), ([3], 7), ([2, 2], 28), ([2, 1], 48), ([], 388)] = false := by
  decide
example : checkClasses 5 14
    [([5], 3), ([4], 4), ([3, 3], 3), ([3], 7), ([2, 2], 28), ([2], 48), ([], 388)] = false := by
  decide

/-! Neighbourhood split (`checkSplit`, `GraphIso.card_eq_of_split`) with the data of
    `tri5_split`: a permuted list, a size outside `0, …, 4`, and a wrong total. -/

example : checkSplit 5 388 [(0, 41), (1, 41), (2, 25), (3, 8), (4, 1)] = true := by decide
example : checkSplit 5 388 [(0, 41), (2, 25), (1, 41), (3, 8), (4, 1)] = false := by decide
example : checkSplit 5 388 [(0, 41), (1, 41), (2, 25), (3, 8), (4, 1), (5, 0)] = false := by
  decide
example : checkSplit 5 389 [(0, 41), (1, 41), (2, 25), (3, 8), (4, 1)] = false := by decide

/-! Cell split (`checkCell`, `GraphIso.card_eq_of_cell`) with the patterns of `GraphTree5.lean`:
    `p4` says `N(0) = {1, 2, 3}`, `p7` adds `N(1) ∩ {2, 3} = {2}`, after which `{2, 3}` is no
    longer a cell. With a split vertex outside the cell and a consistent count list, only
    `cellOk` fails. -/

def p4 : Pattern 5 := star 0 [1, 2, 3, 4] 3
def p7 : Pattern 5 := p4 ++ star 1 [2, 3] 1

example : checkCell p4 1 [2, 3] 56 [(0, 16), (1, 16), (2, 8)] = true := by decide +kernel
example : checkCell p7 4 [2, 3] 56 [(0, 16), (1, 16), (2, 8)] = false := by decide +kernel
example : checkCell p4 4 [2, 3] 56 [(0, 16), (1, 16), (2, 8)] = true := by decide +kernel

/-! Latin fibres (`hrows` of `Latin.card_eq_of_rows`): the admissible second rows of order 5
    with the last one missing, and the 309 rows of order 7 with one missing. -/

example : ([(![1, 0, 3, 4, 2], 4), (![1, 0, 4, 2, 3], 4), (![1, 2, 0, 4, 3], 4),
    (![1, 2, 3, 4, 0], 6), (![1, 2, 4, 0, 3], 6), (![1, 3, 0, 4, 2], 6), (![1, 3, 4, 0, 2], 4),
    (![1, 3, 4, 2, 0], 6), (![1, 4, 0, 2, 3], 6), (![1, 4, 3, 0, 2], 6)] :
    List ((Fin 5 → Fin 5) × ℕ)).map (fun p => rowList p.1) ≠ rows 5 := by decide +kernel
example : (rows 7).eraseIdx 154 ≠ rows 7 := by decide +kernel

/-! Divide and conquer (`SplitTree.card_eq_of_tree`): coverage comes from the tree shape, the
    decidable side condition is the total; a tree that lost a leaf has a different total. -/

example : (SplitTree.node 0 (.leaf 3) (.node 1 (.leaf 2) (.leaf 1))).total = 6 := by decide
example : (SplitTree.node 0 (.leaf 3) (.leaf 2)).total ≠ 6 := by decide
