import CountCatcher

/-! The 8-queens count (OEIS A000170) in every form of `count_models`, on the certificate
    `data/q08.{pog,lrat}` for the encoder `Queens.cnf 8`. -/

open CountCatcher

/-- Family form, embedded: the object statement from `Queens.card_of_check`. -/
count_models queens8 via (Queens.card_of_check (n := 8)) "data/q08.pog" "data/q08.lrat"

/-- Family form, streamed: part B is the theorem `queens8_stream.fwd` (lrat-catcher's stream
    reader), parts A and C read `def queens8_stream.pog`; `Queens.card_of_checkAC`. -/
count_models +stream queens8_stream via (Queens.card_of_check (n := 8)) "data/q08.pog" "data/q08.lrat"

set_option countCatcher.embedMaxBytes 100000 in
/-- Automatic mode: the LRAT file (516 kB) is above the threshold, so it is streamed. -/
count_models queens8_auto via (Queens.card_of_check (n := 8)) "data/q08.pog" "data/q08.lrat"

/-- Model form: the CNF term itself, universe `Fin 64` (its largest variable plus one). -/
count_models queens8_models (Queens.cnf 8) "data/q08.pog" "data/q08.lrat"

/-- Generic family form: the equivalence `Queens.equiv` and `Family.card_of_check`. -/
count_models queens8_equiv via (Family.card_of_check (Queens.equiv (n := 8))) "data/q08.pog" "data/q08.lrat"

set_option maxHeartbeats 200 in
/-- The command sets no heartbeat limit for its native evaluations (a 444 MB LRAT file hit the
    default limit on the cluster); a tiny limit must not matter. -/
count_models queens8_heartbeats via (Queens.card_of_check (n := 8)) "data/q08.pog" "data/q08.lrat"

example : Nat.card {f : Fin 8 → Fin 8 // Queens.Safe f} = 92 := queens8
example : Nat.card {f : Fin 8 → Fin 8 // Queens.Safe f} = 92 := queens8_stream
example : (fwdCnfOf (Queens.cnf 8) queens8_auto.pog).Unsat := queens8_auto.fwd
example : Fintype.card {a : Fin 64 → Bool // (Queens.cnf 8).eval (ext a) = true} = 92 := queens8_models

#print axioms queens8
#print axioms queens8_stream
#print axioms queens8_auto
#print axioms queens8_models
#print axioms queens8_equiv
