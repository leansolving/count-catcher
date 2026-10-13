import Std.Sat.CNF

/-!
# CountCatcherChecker.CliqueCnf — the clique and Ramsey encoders of GraphIso, executable

`CountCatcherMath.GraphIso.cliqueClauses n s pos` has one clause per `s`-subset of the vertices, with
the variable of an edge `uv` its position in `Complete.edges n` (`edgeVar`). Run by the
interpreter, each `edgeVar` rebuilds the edge list and searches it: the (3,5)-Ramsey encoder on
13 vertices took about 0.53 s per evaluation, and the Ramsey theorem evaluates it 113 times
(2026-10-02). Here the same clauses on naturals, compiled: the edge list once per call,
`sublistsLenN` with the recursion of Mathlib's `List.sublistsLen`. `CountCatcherMath.GraphIso.
cliqueCnfN_eq` and `ramseyCnfN_eq` prove the results equal to `cliqueCnf` and `ramseyCnf`.
-/

open Std.Sat

namespace CountCatcher

/-- The pairs `(i, j)`, `i < j < n`, lexicographic (`Complete.edges n` on naturals). -/
def edgePairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => ((List.range n).filter (i < ·)).map (i, ·)

/-- The `k`-element sublists of `l`, in the order of Mathlib's `List.sublistsLen`. -/
def sublistsLenN : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, a :: l => sublistsLenN (k + 1) l ++ (sublistsLenN k l).map (a :: ·)

/-- The clause of the vertex list `S`: `(x_uv, pos)` for `u < v` in `S`, with `x_uv` the
    position of `(u, v)` in `E`. -/
def cliqueClauseN (E : List (Nat × Nat)) (pos : Bool) (S : List Nat) : CNF.Clause Nat :=
  S.flatMap fun u => (S.filter (u < ·)).map fun v => (E.idxOf (u, v), pos)

/-- One clause per `s`-subset of `0, …, n-1`. -/
def cliqueClausesN (n s : Nat) (pos : Bool) : List (CNF.Clause Nat) :=
  let E := edgePairs n
  (sublistsLenN s (List.range n)).map (cliqueClauseN E pos)

/-- No `s`-clique. -/
def cliqueCnfN (n s : Nat) : CNF Nat := ⟨(cliqueClausesN n s false).toArray⟩

/-- No `s`-clique and no independent set of size `t`. -/
def ramseyCnfN (n s t : Nat) : CNF Nat :=
  ⟨(cliqueClausesN n s false ++ cliqueClausesN n t true).toArray⟩

end CountCatcher
