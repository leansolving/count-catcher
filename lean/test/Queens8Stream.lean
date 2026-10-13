import CountCatcherMath.Families.Queens
import LRATCatcher.StreamOracle

/-! The 8-queens theorem with part B streamed (`lrat_stream_cnf`) instead of embedded: the
    route for certificates too large for `include_str`. -/

open CountCatcher

def q08pog : String := include_str "data/q08.pog"

lrat_stream_cnf queens8_fwd (fwdCnfOf (Queens.cnf 8) q08pog) "test/data/q08.lrat"

theorem queens8_stream :
    Nat.card {f : Fin 8 → Fin 8 // ∀ i j, i ≠ j →
      f i ≠ f j ∧ (i : ℕ) + f j ≠ j + f i ∧ (i : ℕ) + f i ≠ j + f j} = 92 :=
  Queens.card_of_checkAC (pogStr := q08pog) (by native_decide) queens8_fwd

#print axioms queens8_stream
