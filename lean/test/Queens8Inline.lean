import CountCatcherMath.Families.Queens
import CountCatcherMath.FwdSel
import LRATCatcher.StreamOracle

/-! The 8-queens theorem streamed from an inlined proof: `data/q08_inline.lrat` is the output of
    `cpog2lrat --inline --keep --delete --binary` on the certificate of `Queens8StreamMask.lean`
    (2,467 of the 5,337 kept additions remain, each single-use addition replaced by its hint
    list in its consumer). Inlining changes neither the mask `data/q08.keep` nor the numbering
    of the initial clauses. Run from `lean/` (the LRAT path is relative to it). -/

open CountCatcher

def q08pog : String := include_str "data/q08.pog"
def q08keep : String := include_str "data/q08.keep"

lrat_stream_cnf queens8_inline_sel (fwdCnfOfSel (Queens.cnf 8) q08pog q08keep)
  "test/data/q08_inline.lrat"

theorem queens8_inline :
    Nat.card {f : Fin 8 → Fin 8 // ∀ i j, i ≠ j →
      f i ≠ f j ∧ (i : ℕ) + f j ≠ j + f i ∧ (i : ℕ) + f i ≠ j + f j} = 92 :=
  Queens.card_of_checkAC (pogStr := q08pog) (by native_decide)
    (fwdCnfOf_unsat_of_sel queens8_inline_sel)

#print axioms queens8_inline
