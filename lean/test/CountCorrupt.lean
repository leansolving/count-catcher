import CountCatcher

/-! Failure reports of `count_models` (`CountCatcherMath/Diag.lean`): each corrupted certificate is
    rejected by the verified check, no theorem is declared, and the error names the part that
    failed. `#guard_msgs` fixes the expected reports. -/

open CountCatcher SimpleGraph

-- Part B: one hint of LRAT line 612 changed (`data/k8_bad.lrat`); the step is named.
/-- error: count_models: the verified check rejected the certificate for 'k8_badB':
  part B (LRAT refutation of F, the defining clauses and ¬root): step 612 (line 612 of a text LRAT file): clause 2119 (162 19 20 7 24 11 -14 -26 0) does not follow by RUP from its 8 hints
'k8_badB' was not declared (the reports come from unverified diagnostics). -/
#guard_msgs in
count_models k8_badB via (Matching.card_of_check (Complete.listing 8)) "data/k8.pog" "data/k8_bad.lrat"

-- The same certificate streamed: part B is the separate theorem `k8_badBs.fwd`, rejected alike.
/-- error: count_models: the verified check rejected the certificate for 'k8_badBs.fwd':
  part B (streamed LRAT refutation of F, the defining clauses and ¬root): step 612 (line 612 of a text LRAT file): clause 2119 (162 19 20 7 24 11 -14 -26 0) does not follow by RUP from its 8 hints
'k8_badBs.fwd' was not declared (the reports come from unverified diagnostics). -/
#guard_msgs in
count_models +stream k8_badBs via (Matching.card_of_check (Complete.listing 8)) "data/k8.pog" "data/k8_bad.lrat"

-- Part A: the first product node of `data/k8_badA.pog` gets the argument `-3` next to `3`
-- (condition C3, disjoint supports).
/-- error: count_models: part A (POG validity) rejects the certificate: node 0 (variable 29, POG line 3): product arguments 3 and -3 share the input variable 3 (condition C3: supports must be disjoint, polarity ignored) -/
#guard_msgs in
count_models k8_badA via (Matching.card_of_check (Complete.listing 8)) "data/k8_badA.pog" "data/k8.lrat"

-- Part C: `x1 ∧ x2` with a POG for `x1` alone. Parts A and B accept, part A's count would be 2
-- (the formula has 1 model); part C finds the input clause `x2` not implied, with a witness.
/-- error: count_models: the verified check rejected the certificate for 'partc_bad':
  part C (every input clause implied by the POG): input clause 2 (2 0) is not implied by the POG: the assignment 1 -2 satisfies the POG root 3 and falsifies the clause (the circuit has models that are not models of the formula)
'partc_bad' was not declared (the reports come from unverified diagnostics). -/
#guard_msgs in
count_models partc_bad "data/partc_bad.cnf" "data/partc_bad.pog" "data/partc_bad.lrat"

-- Universe: the certificate is for 28 variables, the theorem asks for `Fin 30`.
/-- error: count_models: the certificate is for 28 variables (the 'V' line of the POG file, from the header of the counted DIMACS file), the theorem's universe is Fin 30 -/
#guard_msgs in
count_models k8_badV (Matching.cnf (Complete.edges 8) (List.finRange 8)) (V := 30) "data/k8.pog" "data/k8.lrat"

-- Count 0: a refutation of another formula (`K_7`) does not refute the `K_8` encoder.
/-- error: count_models: the verified check rejected the certificate for 'k8_badU':
  LRAT refutation of F: step 1 (line 1 of a text LRAT file): clause 113 (-7 -16 -21 0) does not follow by RUP from its 7 hints
'k8_badU' was not declared (the reports come from unverified diagnostics). -/
#guard_msgs in
count_models k8_badU via (Matching.card_of_check (Complete.listing 8)) "data/k7_unsat.lrat"
