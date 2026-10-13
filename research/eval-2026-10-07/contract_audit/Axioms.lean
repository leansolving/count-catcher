-- #print axioms for the soundness theorems (port of research/eval-2026-09-30/contract_audit/Axioms.lean
-- to the renamed tree; difftest_rerun.md): the nine theorems of the paper's soundness listing,
-- in its order, plus LRATCatcher.checkLratCnf_sound of the old list.
-- Run from the package root (lean_audit2): lake env lean Axioms.lean
import CountCatcherMath.Check
import CountCatcherMath.Main
import CountCatcherMath.FwdSel
import CountCatcherMath.Family
import LRATCatcher.StreamOracle
open CountCatcher
#print axioms CountCatcher.checkPog_sound
#print axioms CountCatcher.fwd_of_unsat
#print axioms CountCatcher.checkRevKillFast_sound
#print axioms CountCatcher.card_models_eq_countRoot
#print axioms CountCatcher.checkAll_sound
#print axioms CountCatcher.checkAllAC_sound
#print axioms CountCatcher.fwdCnfOf_unsat_of_sel
#print axioms LRATCatcher.checkStreamCnf_sound
#print axioms CountCatcher.Family.card_of_checkAC
-- in the 2026-09-30 list, not in the listing
#print axioms LRATCatcher.checkLratCnf_sound
