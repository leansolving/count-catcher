import LRATCatcher.Reflect

/-! Smoke test: the lrat-catcher dependency builds and its LRAT check runs natively. -/

open Std.Sat LRATCatcher

-- PHP(2,1): two pigeons, one hole. Variables are 0-indexed (DIMACS variable k is k - 1).
def php21 : CNF Nat := ⟨#[[(0, true)], [(1, true)], [(0, false), (1, false)]]⟩

-- LRAT: clause 4 is the empty clause, RUP from clauses 1, 2, 3.
theorem php21_unsat : php21.Unsat :=
  checkLratCnf_sound php21 "4 0 1 2 3 0\n" (by native_decide)
