-- Axioms of the nine soundness theorems of the paper's soundness listing, in its order
-- (copy of research/eval-2026-10-07/contract_audit/Axioms.lean without its tenth line).
-- Run from lean/: lake env lean ../artifact/Axioms.lean
-- Expected: every theorem depends on propext, Classical.choice and Quot.sound only;
-- fwdCnfOf_unsat_of_sel on propext and Quot.sound.
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
