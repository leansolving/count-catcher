import CountCatcherChecker.Spec

/-!
# CountCatcherChecker.Fwd — part B: the forward refutation's CNF

The forward direction is the unsatisfiability of `F ∧ defs(P) ∧ ¬r`, checked by
lrat-catcher. The CNF is built here from the Lean-side `F` and the checked POG `P`, in the
clause order that `scripts/cpog2lrat.py` uses for the LRAT proof: `F`, then the defining
clauses in declaration order (CPOG Table 2), then the unit `¬r`.
-/

open Std.Sat

namespace CountCatcher

def fwdCnf (F : CNF Nat) (P : Pog) (r : Literal Nat) : CNF Nat :=
  ⟨F.clauses ++ P.defs.toArray ++ #[[(r.1, !r.2)]]⟩

end CountCatcher
