import CountCatcherMath.Families.Queens
import CountCatcherMath.FwdSel
import LRATCatcher.StreamOracle

/-! The streamed 8-queens theorem (`Queens8Stream.lean`) with part B on a selection of its
    initial clauses (`CountCatcherChecker/FwdSel.lean`): `data/q08.keep` keeps the 1,399 of 4,710 clauses of
    `fwdCnfOf (Queens.cnf 8) q08pog` that a step of the trimmed proof cites, and
    `data/q08_mask.lrat` is the output of `cpog2lrat --keep --delete --binary` (binary, trimmed,
    with deletions, numbered for the kept clauses). Run from `lean/` (the LRAT paths are relative
    to it). -/

open CountCatcher

def q08pog : String := include_str "data/q08.pog"
def q08keep : String := include_str "data/q08.keep"

lrat_stream_cnf queens8_fwd_sel (fwdCnfOfSel (Queens.cnf 8) q08pog q08keep) "test/data/q08_mask.lrat"

theorem queens8_stream_mask :
    Nat.card {f : Fin 8 → Fin 8 // ∀ i j, i ≠ j →
      f i ≠ f j ∧ (i : ℕ) + f j ≠ j + f i ∧ (i : ℕ) + f i ≠ j + f j} = 92 :=
  Queens.card_of_checkAC (pogStr := q08pog) (by native_decide)
    (fwdCnfOf_unsat_of_sel queens8_fwd_sel)

#print axioms queens8_stream_mask

/-! The empty mask selects all of `fwdCnfOf`, and the unrenumbered `data/q08.lrat` refutes it. -/

#guard (fwdCnfOfSel (Queens.cnf 8) q08pog "").clauses == (fwdCnfOf (Queens.cnf 8) q08pog).clauses
lrat_stream_cnf queens8_fwd_all (fwdCnfOfSel (Queens.cnf 8) q08pog "") "test/data/q08.lrat"

/-! A mask that also drops clause 0 shifts the numbering of the kept clauses: the renumbered
    proof no longer fits and the check fails. -/

def q08keepBad : String := "0" ++ (q08keep.drop 1).toString

/--
error: Tactic `native_decide` evaluated that the proposition
  LRATCatcher.checkStreamCnf (fwdCnfOfSel (Queens.cnf 8) q08pog q08keepBad) queens8_fwd_bad_feed
      LRATCatcher.streamFuel =
    true
is false
-/
#guard_msgs in
lrat_stream_cnf queens8_fwd_bad (fwdCnfOfSel (Queens.cnf 8) q08pog q08keepBad) "test/data/q08_mask.lrat"

/-! Positions: `fwdCnfSel` keeps exactly the clauses of `fwdCnf` whose mask byte is not `'0'`
    (the reference filters the built `fwdCnf`). Checked on the queens masks, and on the domino
    8x8 POG (sum nodes) with a patterned mask, a mask with other characters, and a short one. -/

def selRef (C : Std.Sat.CNF Nat) (mask : String) : Array (Std.Sat.CNF.Clause Nat) :=
  ((C.clauses.toList.zipIdx.filter fun p => maskKeep mask p.2).map Prod.fst).toArray

#guard (fwdCnfOfSel (Queens.cnf 8) q08pog q08keep).clauses.size = 1399
#guard [q08keep, q08keepBad].all fun k =>
  (fwdCnfOfSel (Queens.cnf 8) q08pog k).clauses == selRef (fwdCnfOf (Queens.cnf 8) q08pog) k

def d08F : Std.Sat.CNF Nat := LRATCatcher.parseDimacs (include_str "data/dom08.dimacs")
def d08pog : String := include_str "data/dom08.pog"
def d08masks : List String :=
  [String.ofList ((List.range 20000).map fun i => if (i * 7919) % 5 < 2 then '0' else '1'),
   String.ofList ((List.range 20000).map fun i => if i % 3 == 0 then '0' else 'x'),
   "0101100"]
#guard d08masks.all fun k => (fwdCnfOfSel d08F d08pog k).clauses == selRef (fwdCnfOf d08F d08pog) k
#guard d08masks.all fun k => (fwdCnfOfSel d08F d08pog k).clauses.size < (fwdCnfOf d08F d08pog).clauses.size
