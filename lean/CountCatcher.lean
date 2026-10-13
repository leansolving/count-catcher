import CountCatcherMath.Command
import CountCatcherMath.Family
import CountCatcherMath.Families.Unsat
import CountCatcherMath.Families.Domino
import CountCatcherMath.Families.Queens
import CountCatcherMath.Families.QueensSym
import CountCatcherMath.Families.Grid
import CountCatcherMath.Families.Graphs
import CountCatcherMath.Families.Complete
import CountCatcherMath.Families.GraphIso
import CountCatcherMath.Families.Dedekind
import CountCatcherMath.Families.DedekindCorner
import CountCatcherMath.Families.LatinAll
import CountCatcherMath.Families.LatinCycle
import CountCatcherMath.Families.Kreweras
import CountCatcherMath.Families.Sperner
import CountCatcherMath.Families.TotalDom
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# CountCatcher — the user front end

`import CountCatcher` gives the commands `count_models` and `#export_cnf`
(`CountCatcherMath/Command.lean`), the generic family lemmas (`CountCatcherMath/Family.lean`), and every
family with its `card_of_check`, `card_of_checkAC` and, where the encoder can be
unsatisfiable, `card_of_unsat` lemma; for graphs up to isomorphism, the Burnside layer
(`CountCatcherMath/Families/GraphIso.lean`, `CountCatcherMath/CycleType.lean`, driver
`scripts/graph_orbits.py`). Driver: `scripts/count_catcher.py`.
-/
