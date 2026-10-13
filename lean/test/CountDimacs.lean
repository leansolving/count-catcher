import CountCatcher

/-! A DIMACS file as the formula: the statement is about `LRATCatcher.parseDimacs` of the file
    contents (validated as by `lrat_reflect`), over `Fin 112`, the header's variable count. -/

open CountCatcher

count_models dom08_models "data/dom08.dimacs" "data/dom08.pog" "data/dom08.lrat"

count_models +stream dom08_models_stream "data/dom08.dimacs" "data/dom08.pog" "data/dom08.lrat"

#print axioms dom08_models
#print axioms dom08_models_stream
