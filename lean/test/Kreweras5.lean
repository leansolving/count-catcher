import CountCatcher

/-! Antichains of the Kreweras lattice NC(5) of noncrossing partitions: A358391(5) = 2342196
    (Ignatov 2022), from the certificate `data/krew5.{pog,lrat}` for the encoder `Kreweras.cnf 5`
    (Catalan(5) = 42 variables, 231 binary clauses; `scripts/showcase/kreweras.py --n 5`,
    `cpog-gen-norev -F`). The same certificate proves the statement over `Finpartition` and over
    `Setoid`. -/

open CountCatcher

/-- Embedded, over `Finpartition` (`Kreweras.Fp.card_of_check`). -/
count_models kreweras5 via (Kreweras.Fp.card_of_check (n := 5)) "data/krew5.pog" "data/krew5.lrat"

/-- Streamed, over `Setoid` (`Kreweras.card_of_checkAC`). -/
count_models +stream kreweras5_stream via (Kreweras.card_of_check (n := 5)) "data/krew5.pog" "data/krew5.lrat"

example : Nat.card {A : Set {P : Finpartition (Finset.univ : Finset (Fin 5)) // P.IsNoncrossing} //
    IsAntichain (· ≤ ·) A} = 2342196 := kreweras5

example : Nat.card {A : Set {r : Setoid (Fin 5) // r.IsNoncrossing} // IsAntichain (· ≤ ·) A} =
    2342196 := kreweras5_stream

/-- With the noncrossing condition written out: no definition outside Mathlib. -/
example : Nat.card {A : Set {P : Finpartition (Finset.univ : Finset (Fin 5)) //
    ∀ a b c d : Fin 5, a < b → b < c → c < d → P.part a = P.part c → P.part b = P.part d →
      P.part a = P.part b} // IsAntichain (· ≤ ·) A} = 2342196 := kreweras5

/-- The encoder enumerates Bell(5) = 52 set partitions, of which Catalan(5) = 42 are
    noncrossing. -/
example : (Kreweras.gen 5).length = 52 ∧ (Kreweras.ncList 5).length = 42 := by decide

/-! A wrong count hint is rejected by the verified check; the theorem is not declared. -/

/--
error: count_models: the verified check rejected the certificate for 'kreweras5_bad':
  part A (count): the certificate's count is 2342196, not the hinted (count := 2342195)
'kreweras5_bad' was not declared (the reports come from unverified diagnostics).
-/
#guard_msgs in
count_models kreweras5_bad via (Kreweras.Fp.card_of_check (n := 5)) "data/krew5.pog" "data/krew5.lrat" (count := 2342195)

#print axioms kreweras5
#print axioms kreweras5_stream
