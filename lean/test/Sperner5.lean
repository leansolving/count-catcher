import CountCatcher

/-! Uncomplemented Sperner families on a 5-set: A396728(5) = 5001 (OEIS), from the certificate
    `data/sp5.{pog,lrat}` for the encoder `Sperner.cnf 5` (32 variables, 226 binary clauses;
    driver `scripts/showcase/sperner.py --n 5`, `cpog-gen-norev -F`). -/

open CountCatcher

/-- Embedded: the object statement from `Sperner.card_of_check`. -/
count_models sperner5 via (Sperner.card_of_check (n := 5)) "data/sp5.pog" "data/sp5.lrat"

/-- Streamed: part B is the separate theorem `sperner5_stream.fwd` (`Sperner.card_of_checkAC`). -/
count_models +stream sperner5_stream via (Sperner.card_of_check (n := 5)) "data/sp5.pog" "data/sp5.lrat"

example : Nat.card {F : Finset (Finset (Fin 5)) //
    IsAntichain (· ⊆ ·) (F : Set (Finset (Fin 5))) ∧ ∀ A ∈ F, Aᶜ ∉ F} = 5001 := sperner5

example : Nat.card {F : Finset (Finset (Fin 5)) //
    IsAntichain (· ⊆ ·) (F : Set (Finset (Fin 5))) ∧ ∀ A ∈ F, Aᶜ ∉ F} = 5001 := sperner5_stream

/-- The encoder has `3 ^ n - 2 ^ n` comparable and `2 ^ (n - 1) - 1` complementary clauses. -/
example : (Sperner.cnf 5).clauses.size = 226 := by decide +kernel

/-! A wrong count hint is rejected by the verified check; the theorem is not declared. -/

/--
error: count_models: the verified check rejected the certificate for 'sperner5_bad':
  part A (count): the certificate's count is 5001, not the hinted (count := 5000)
'sperner5_bad' was not declared (the reports come from unverified diagnostics).
-/
#guard_msgs in
count_models sperner5_bad via (Sperner.card_of_check (n := 5)) "data/sp5.pog" "data/sp5.lrat" (count := 5000)

#print axioms sperner5
#print axioms sperner5_stream
