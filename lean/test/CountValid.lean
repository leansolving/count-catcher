import CountCatcher

/-! Translator and front-end regressions (contract_audit.md, B1 to B3).

    B1: for a valid formula cpog-gen makes the root the empty product and uses its defining
    clause as the root unit, so the final LRAT step cites that clause. The empty formula and the
    formula over no variables are checked as terms and as DIMACS files.

    B2: a hint-less addition is written with single spaces (`nohint`, the audit's case c24;
    Lean core's LRAT checker accepts its hint-less steps).

    B3: lrat-catcher's `validateDimacs` accepts a DIMACS file without clauses since v0.2.0. -/

open CountCatcher

count_models valid_empty (.empty) (V := 3) "data/valid_empty.pog" "data/valid_empty.lrat"
count_models valid_v0 (.empty) (V := 0) "data/valid_v0.pog" "data/valid_v0.lrat"
count_models valid_empty_dimacs "data/valid_empty.cnf" "data/valid_empty.pog"
  "data/valid_empty.lrat"
count_models valid_v0_dimacs "data/valid_v0.cnf" "data/valid_v0.pog" "data/valid_v0.lrat"
count_models valid_taut "data/valid_taut.cnf" "data/valid_taut.pog" "data/valid_taut.lrat"
count_models +stream valid_taut_stream "data/valid_taut.cnf" "data/valid_taut.pog"
  "data/valid_taut.lrat"
count_models nohint "data/nohint.cnf" "data/nohint.pog" "data/nohint.lrat"

#check (valid_empty : _)
#check (valid_v0 : _)
#check (valid_empty_dimacs : _)
#check (valid_v0_dimacs : _)
#check (nohint : _)
#print axioms valid_empty
#print axioms valid_taut_stream
