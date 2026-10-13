import CountCatcher
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-! New families with no new certificate code. Perfect matchings of `K_8` through the generic
    matching layer (`CountCatcherMath/Families/Complete.lean`: the edge list and its listing proof);
    independent sets of Mathlib's `cycleGraph 10` and perfect matchings of the 6 × 2 ladder
    (the domino board `pathGraph 6 □ pathGraph 2`) with no new Lean code at all. -/

open CountCatcher SimpleGraph

count_models k8 via (Matching.card_of_check (Complete.listing 8)) "data/k8.pog" "data/k8.lrat"

count_models cycle10 via (IndepSet.card_of_check (cycleGraph 10)) "data/cyc10.pog" "data/cyc10.lrat"

count_models ladder6 via (Domino.card_of_check (R := 6) (C := 2)) "data/ladder6.pog" "data/ladder6.lrat"

/-- Downstream: the perfect matchings of `K_8` number `7‼ = 7 · 5 · 3 · 1` (`Nat.doubleFactorial`). -/
theorem k8_doubleFactorial :
    Nat.card {M : (⊤ : SimpleGraph (Fin 8)).Subgraph // M.IsPerfectMatching} = Nat.doubleFactorial 7 := by
  rw [k8]; rfl

/-- Downstream: the independent sets of the 10-cycle number `F_9 + F_11` (Lucas number `L_10`). -/
theorem cycle10_lucas :
    Nat.card {s : Finset (Fin 10) // (cycleGraph 10).IsIndepSet (s : Set (Fin 10))} =
      Nat.fib 9 + Nat.fib 11 := by
  rw [cycle10]; rfl

/-- Downstream: the perfect matchings of the 6 × 2 ladder number `F_7`. -/
theorem ladder6_fib :
    Nat.card {M : (pathGraph 6 □ pathGraph 2).Subgraph // M.IsPerfectMatching} = Nat.fib 7 := by
  rw [ladder6]; rfl

#print axioms k8
#print axioms cycle10
#print axioms ladder6
#print axioms k8_doubleFactorial
#print axioms cycle10_lucas
#print axioms ladder6_fib
