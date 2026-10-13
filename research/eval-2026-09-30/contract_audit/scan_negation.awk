# Scan a CPOG certificate (.cpog, needs V from the DIMACS header: -v V=...) or a translated
# POG file (.pog, V from its "V" line) for the shapes outside the checker's fragment and for
# constants: negated edges into internal nodes, a negated root node, empty and one-argument
# products, a literal root. Prints one line of counts.
# Usage: awk [-v V=<vars>] -f scan_negation.awk FILE.cpog   |   awk -f scan_negation.awk FILE.pog
# (for a .cpog without -v V, V is the first declared extension variable minus 1)
$1 == "V" { V = $2; pogmode = 1; next }
$1 == "r" { root = $2; next }
pogmode && ($1 == "p" || $1 == "s") {
  nodes++; kind = $1; n = 0
  last = (kind == "p") ? NF - 1 : 3
  for (i = 2; i <= last; i++) { a = $i + 0; n++; if (a < 0 && -a > V) neg++ ; if (a < 0 && -a <= V) neginput++ }
  if (kind == "p") { prods++; if (n == 0) empty++; if (n == 1) single++ } else sums++
  next
}
!pogmode && ($2 == "p" || $2 == "s") {
  if (V == "") V = $3 - 1   # cpog-gen declares extension variables from V+1 on (C2)
  nodes++; kind = $2; n = 0
  last = (kind == "p") ? NF - 1 : 5
  for (i = 4; i <= last; i++) { a = $i + 0; n++; if (a < 0 && -a > V) neg++; if (a < 0 && -a <= V) neginput++ }
  if (kind == "p") { prods++; if (n == 0) empty++; if (n == 1) single++ } else sums++
}
END {
  r = root + 0
  printf "file=%s V=%d nodes=%d products=%d sums=%d negated_internal_edges=%d negative_input_args=%d empty_products=%d single_arg_products=%d root=%s root_negated_node=%d root_literal=%d\n", \
    FILENAME, V, nodes, prods, sums, neg + 0, neginput + 0, empty + 0, single + 0, root, (r < 0 && -r > V), ((r < 0 ? -r : r) <= V)
}
