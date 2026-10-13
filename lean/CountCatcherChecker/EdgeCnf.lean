import Std.Sat.CNF

/-!
# CountCatcherChecker.EdgeCnf — the independent-set encoder of an edge list, executable

`CountCatcherMath.IndepSet.cnf G` tests `G.Adj u v` for all `k²` vertex pairs. For `edgeGraph l` every
test is a membership test of a `Sym2` in `l`, run by the interpreter (CountCatcherMath is not
precompiled): homer (561 vertices, 1,628 edges) took 58 s for the CNF alone (2026-10-02). Here the
edges come as pairs `(smaller, larger)` of naturals (`CountCatcherMath.edgeCnf` converts a `Sym2` list by
`sym2Pair`), are collected once into upper adjacency lists, and the clauses are emitted in the
same order: `¬u ∨ ¬v` for every edge with `u < v`, lexicographically. Cost O(k² + k·|E|): `k²`
pairs `(u, v)`, each a membership test in the adjacency list of `u`. `CountCatcherMath.edgeCnf_eq`
proves the result equal to `IndepSet.cnf (edgeGraph l)`.
-/

open Std.Sat

namespace CountCatcher

/-- Upper adjacency lists: entry `a` holds every `b` with `(a, b) ∈ es` (entries `a ≥ k` are
    dropped). -/
def upperAdj (k : Nat) (es : List (Nat × Nat)) : Array (List Nat) :=
  es.foldl (fun t e => t.modify e.1 (e.2 :: ·)) (Array.replicate k [])

/-- One clause `¬u ∨ ¬v` for every `u < v < k` with `(u, v) ∈ es`, ordered by `(u, v)`. The
    edges must be pairs (smaller, larger); other pairs are ignored (`edgeListClauses 3 [(2, 0)]`
    is empty). -/
def edgeListClauses (k : Nat) (es : List (Nat × Nat)) : List (CNF.Clause Nat) :=
  let adj := upperAdj k es
  (List.range k).flatMap fun u => (List.range k).filterMap fun v =>
    if u < v ∧ (adj[u]!).contains v = true then some [(u, false), (v, false)] else none

/-- The independent-set CNF of the graph on `Fin k` with the edges `es`, given as pairs
    (smaller, larger); other pairs are ignored (`edgeListCnf 3 [(2, 0)]` has no clauses). Only
    `CountCatcherMath.edgeCnf`, through `sym2Pair`, guarantees that form. -/
def edgeListCnf (k : Nat) (es : List (Nat × Nat)) : CNF Nat := ⟨(edgeListClauses k es).toArray⟩

end CountCatcher
