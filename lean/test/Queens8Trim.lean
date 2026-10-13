import CountCatcherMath.Families.Queens
import LRATCatcher.StreamOracle

/-! The 8-queens theorem streamed from the pipeline's default LRAT form: binary, with
    deletions, trimmed to the backward cone of the empty clause (`cpog2lrat --trim --delete
    --binary`: 5,337 of 7,664 additions kept). Same certificate and POG file as
    `Queens8Stream.lean`. -/

open CountCatcher

def q08pog : String := include_str "data/q08.pog"

lrat_stream_cnf queens8_trim_fwd (fwdCnfOf (Queens.cnf 8) q08pog) "test/data/q08_trim.lrat"

theorem queens8_trim :
    Nat.card {f : Fin 8 → Fin 8 // ∀ i j, i ≠ j →
      f i ≠ f j ∧ (i : ℕ) + f j ≠ j + f i ∧ (i : ℕ) + f i ≠ j + f j} = 92 :=
  Queens.card_of_checkAC (pogStr := q08pog) (by native_decide) queens8_trim_fwd

#print axioms queens8_trim
