import CountCatcher

/-! `count_models` with a keep file (`CountCatcherChecker/FwdSel.lean`): `data/q08.keep` selects the initial
    clauses of part B's CNF that the translator's LRAT `data/q08_mask.lrat` (binary, numbered
    for the selected clauses) cites, for the certificate `data/q08.pog` of `Queens.cnf 8`. -/

open CountCatcher

/-- Family form; the keep file implies streaming. -/
count_models queens8_keep via (Queens.card_of_check (n := 8)) "data/q08.pog" "data/q08_mask.lrat" (keep := "data/q08.keep")

/-- Model form, `+stream`, with a count hint after the keep file. -/
count_models +stream queens8_keep_models (Queens.cnf 8) "data/q08.pog" "data/q08_mask.lrat" (keep := "data/q08.keep") (count := 92)

example : Nat.card {f : Fin 8 → Fin 8 // Queens.Safe f} = 92 := queens8_keep
example : (fwdCnfOfSel (Queens.cnf 8) queens8_keep.pog queens8_keep.keep).Unsat := queens8_keep.fwd
example : Fintype.card {a : Fin 64 → Bool // (Queens.cnf 8).eval (ext a) = true} = 92 :=
  queens8_keep_models

#print axioms queens8_keep
#print axioms queens8_keep_models

/-! Failures: no theorem is declared. -/

-- A wrong count hint: part B accepts, parts A and C reject the count.
/--
error: count_models: the verified check rejected the certificate for 'queens8_keep_hint91':
  part A (count): the certificate's count is 92, not the hinted (count := 91)
'queens8_keep_hint91' was not declared (the reports come from unverified diagnostics).
-/
#guard_msgs in
count_models queens8_keep_hint91 via (Queens.card_of_check (n := 8)) "data/q08.pog" "data/q08_mask.lrat" (keep := "data/q08.keep") (count := 91)

-- A keep file belongs to the streamed check.
/--
error: count_models: a keep file selects part B's initial clauses for the streamed check; it cannot be used with +embed (use +stream or no flag)
-/
#guard_msgs in
count_models +embed queens8_keep_embed via (Queens.card_of_check (n := 8)) "data/q08.pog" "data/q08_mask.lrat" (keep := "data/q08.keep")

/-- error: count_models: the count-0 form (one LRAT refutation of F) takes no keep file -/
#guard_msgs in
count_models queens3_keep (Queens.cnf 3) "data/q03_unsat.lrat" (keep := "data/q08.keep")

-- The keep file with the LRAT numbered for all clauses (`data/q08.lrat`): its first step
-- cites clauses by their positions in the full CNF, which the selection has renumbered.
/--
error: count_models: the verified check rejected the certificate for 'queens8_keep_mismatch.fwd':
  part B (streamed LRAT refutation of the clauses of F, the defining clauses and ¬root that the keep file selects): step 1 (line 1 of a text LRAT file): clause 4711 (-40 -52 -63 20 37 36 35 45 22 1 3 15 … (3 more) 0) does not follow by RUP from its 22 hints
'queens8_keep_mismatch.fwd' was not declared (the reports come from unverified diagnostics).
-/
#guard_msgs in
count_models queens8_keep_mismatch via (Queens.card_of_check (n := 8)) "data/q08.pog" "data/q08.lrat" (keep := "data/q08.keep")

-- A missing keep file is reported before anything is declared, so the same name can be used
-- again with the right files.
/-- data/nonexistent.keep' as text: no such file or directory -/
#guard_msgs (substring := true) in
count_models queens8_keep_retry via (Queens.card_of_check (n := 8)) "data/q08.pog" "data/q08_mask.lrat" (keep := "data/nonexistent.keep")

count_models queens8_keep_retry via (Queens.card_of_check (n := 8)) "data/q08.pog" "data/q08_mask.lrat" (keep := "data/q08.keep")

example : Nat.card {f : Fin 8 → Fin 8 // Queens.Safe f} = 92 := queens8_keep_retry
