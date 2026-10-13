import CountCatcherMath.Check

/-! Regression test for tautological input clauses: the domino 8 x 8 CNF with two tautologies
    inserted (`3 -3 0` as clause 101, `9 -9 20 0` as clause 202), so it still has 12,988,816
    models over 112 variables. Lean core's LRAT checker drops tautological clauses from the
    initial formula and addresses clauses by position; `scripts/cpog2lrat.py` (and the native
    `cpog2lrat`) number the clauses the same way. With DIMACS numbering, part B is rejected. -/

open CountCatcher

theorem dom08t_models :
    Fintype.card {a : Fin 112 → Bool //
      (LRATCatcher.parseDimacs (include_str "data/dom08t.dimacs")).eval (ext a) = true} = 12988816 :=
  checkAll_sound (pogStr := include_str "data/dom08t.pog") (lratStr := include_str "data/dom08t.lrat")
    (by native_decide)

#print axioms dom08t_models
