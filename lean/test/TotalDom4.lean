import CountCatcher

/-! Total dominating sets of the n × n torus `cycleGraph n □ cycleGraph n` (OEIS A303210), from
    the certificates `data/a303210_{3,4}.{pog,lrat}` for the encoder
    `TotalDom.cnf (TotalDom.torusNbrs (n - 2))` (n² variables, n² positive clauses;
    `scripts/showcase/a303210.py --n n`, `cpog-gen-norev -F`). -/

open CountCatcher SimpleGraph

/-- Embedded: the object statement from `TotalDom.torus_card_of_check`. -/
count_models A303210_4 via (TotalDom.torus_card_of_check (m := 2)) "data/a303210_4.pog" "data/a303210_4.lrat"

/-- Streamed: part B is the separate theorem `A303210_4_stream.fwd`
    (`TotalDom.torus_card_of_checkAC`). -/
count_models +stream A303210_4_stream via (TotalDom.torus_card_of_check (m := 2)) "data/a303210_4.pog" "data/a303210_4.lrat"

example : Nat.card {S : Finset (Fin 4 × Fin 4) //
    ∀ v, ∃ u ∈ S, (cycleGraph 4 □ cycleGraph 4).Adj v u} = 33489 := A303210_4

/-- The generic family: any graph, numbering and neighbour lists with a proof `hN`. Here n = 3,
    where `cycleGraph 3` is the triangle (K₃ □ K₃). -/
count_models A303210_3 via (TotalDom.card_of_check (cycleGraph 3 □ cycleGraph 3) finProdFinEquiv
  (TotalDom.torusNbrs 1) (TotalDom.torusNbrs_spec 1)) "data/a303210_3.pog" "data/a303210_3.lrat"

example : Nat.card {S : Finset (Fin 3 × Fin 3) //
    ∀ v, ∃ u ∈ S, (cycleGraph 3 □ cycleGraph 3).Adj v u} = 334 := A303210_3

/-- The encoder has one clause per vertex. -/
example : (TotalDom.cnf (TotalDom.torusNbrs 2)).clauses.size = 16 := by decide

/-! A wrong count hint is rejected by the verified check; the theorem is not declared. -/

/--
error: count_models: the verified check rejected the certificate for 'A303210_4_bad':
  part A (count): the certificate's count is 33489, not the hinted (count := 33488)
'A303210_4_bad' was not declared (the reports come from unverified diagnostics).
-/
#guard_msgs in
count_models A303210_4_bad via (TotalDom.torus_card_of_check (m := 2)) "data/a303210_4.pog" "data/a303210_4.lrat" (count := 33488)

#print axioms A303210_4
#print axioms A303210_3
