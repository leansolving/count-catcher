import CountCatcherMath.Check

/-! First end-to-end theorem: the domino 8 x 8 CNF (read from DIMACS, see `data/`) has
    12,988,816 models over its 112 edge variables. Certificate: D4 + cpog-gen, translated by
    `scripts/cpog2lrat.py`; checked by parts A, B, C in native mode. -/

open CountCatcher

theorem dom08_models :
    Fintype.card {a : Fin 112 → Bool //
      (LRATCatcher.parseDimacs (include_str "data/dom08.dimacs")).eval (ext a) = true} = 12988816 :=
  checkAll_sound (pogStr := include_str "data/dom08.pog") (lratStr := include_str "data/dom08.lrat")
    (by native_decide)

#print axioms dom08_models
