-- #print axioms for the soundness theorems (contract_audit.md, part 2). Run from lean/: lake env lean ../research/eval-2026-09-30/contract_audit/Axioms.lean
import McCertMath.Check
import McCertMath.Main
open McCert
#print axioms McCert.checkAll_sound
#print axioms McCert.checkAllAC_sound
#print axioms McCert.card_models_eq_countRoot
#print axioms McCert.checkPog_sound
#print axioms McCert.checkRevKillFast_sound
#print axioms McCert.fwd_of_unsat
#print axioms LRATCatcher.checkLratCnf_sound
