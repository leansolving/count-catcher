import CountCatcherMath.Family
import CountCatcherMath.Families.Domino
import CountCatcherMath.Families.Queens

/-!
# Count 0 for the families whose encoder can be unsatisfiable

cpog-gen refuses unsatisfiable formulas, so a count of 0 comes from an LRAT refutation of the
encoder (CaDiCaL) through lrat-catcher and `card_eq_zero_of_unsat`. Naming convention used by
`count_models … via (L …)`: the count-0 lemma of `…card_of_check` is `…card_of_unsat`.
Independent-set encoders are always satisfiable (the empty set), so they have none.
-/

open SimpleGraph

namespace CountCatcher

theorem Matching.card_of_unsat {V : Type*} [DecidableEq V] {es : List (V × V)}
    {G : SimpleGraph V} {vs : List V} (hL : Matching.Listing G es vs)
    (h : (Matching.cnf es vs).Unsat) : Nat.card {M : G.Subgraph // M.IsPerfectMatching} = 0 :=
  Family.card_of_unsat (Matching.equiv hL) h

theorem Domino.card_of_unsat {R C : ℕ} (h : (Domino.cnf R C).Unsat) :
    Nat.card {M : (pathGraph R □ pathGraph C).Subgraph // M.IsPerfectMatching} = 0 :=
  Matching.card_of_unsat (Domino.listing R C) h

theorem Queens.card_of_unsat {n : ℕ} (h : (Queens.cnf n).Unsat) :
    Nat.card {f : Fin n → Fin n // Queens.Safe f} = 0 :=
  Family.card_of_unsat Queens.equiv h

end CountCatcher
