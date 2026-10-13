import CountCatcher

/-! The count hint `(count := N)`: the command takes `N` from the hint (in the pipeline, D4's
    count) instead of running part A at elaboration time. The statement is the same and the
    verified check still checks `N`; a wrong hint is rejected with the part-A count report. -/

open CountCatcher SimpleGraph

count_models k8_hint via (Matching.card_of_check (Complete.listing 8)) "data/k8.pog" "data/k8.lrat"
  (count := 105)

count_models +stream k8_hint_stream via (Matching.card_of_check (Complete.listing 8))
  "data/k8.pog" "data/k8.lrat" (count := 105)

count_models dom08_hint "data/dom08.dimacs" "data/dom08.pog" "data/dom08.lrat" (count := 12988816)

example : Nat.card {M : (⊤ : SimpleGraph (Fin 8)).Subgraph // M.IsPerfectMatching} = 105 := k8_hint

/-- error: count_models: the verified check rejected the certificate for 'k8_wrong':
  part A (count): the certificate's count is 105, not the hinted (count := 104)
'k8_wrong' was not declared (the reports come from unverified diagnostics). -/
#guard_msgs in
count_models k8_wrong via (Matching.card_of_check (Complete.listing 8)) "data/k8.pog" "data/k8.lrat"
  (count := 104)

/-- error: count_models: the verified check rejected the certificate for 'k8_wrong_stream':
  part A (count): the certificate's count is 105, not the hinted (count := 106)
'k8_wrong_stream' was not declared (the reports come from unverified diagnostics). -/
#guard_msgs in
count_models +stream k8_wrong_stream via (Matching.card_of_check (Complete.listing 8))
  "data/k8.pog" "data/k8.lrat" (count := 106)

/-- error: count_models: the count-0 form (one LRAT refutation) takes no count hint -/
#guard_msgs in
count_models k7_hint via (Matching.card_of_check (Complete.listing 7)) "data/k7_unsat.lrat" (count := 0)

#print axioms k8_hint
#print axioms k8_hint_stream
#print axioms dom08_hint
