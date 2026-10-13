import CountCatcher

/-! Monotone Boolean functions on 5 variables: the Dedekind number M(5) = 7581 (OEIS A000372),
    from the certificate `data/ded5.{pog,lrat}` for the encoder `Dedekind.cnf 5` (32 variables,
    80 binary clauses; `scripts/showcase/dedekind.py --n 5`, `cpog-gen-norev -F`). -/

open CountCatcher

/-- Embedded: the object statement from `Dedekind.card_of_check`. -/
count_models dedekind5 via (Dedekind.card_of_check (n := 5)) "data/ded5.pog" "data/ded5.lrat"

/-- Streamed: part B is the separate theorem `dedekind5_stream.fwd`
    (`Dedekind.card_of_checkAC`). -/
count_models +stream dedekind5_stream via (Dedekind.card_of_check (n := 5)) "data/ded5.pog" "data/ded5.lrat"

example : Nat.card {f : (Fin 5 → Bool) → Bool // Monotone f} = 7581 := dedekind5

/-- The encoder has one clause per covering pair: `n · 2 ^ (n - 1)`. -/
example : (Dedekind.cnf 5).clauses.size = 80 := by decide

/-! A wrong count hint is rejected by the verified check; the theorem is not declared. -/

/--
error: count_models: the verified check rejected the certificate for 'dedekind5_bad':
  part A (count): the certificate's count is 7581, not the hinted (count := 7580)
'dedekind5_bad' was not declared (the reports come from unverified diagnostics).
-/
#guard_msgs in
count_models dedekind5_bad via (Dedekind.card_of_check (n := 5)) "data/ded5.pog" "data/ded5.lrat" (count := 7580)

#print axioms dedekind5
