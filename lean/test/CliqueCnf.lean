import CountCatcher

/-! The compiled clique and Ramsey encoders (`CountCatcherChecker/CliqueCnf.lean`, proved equal by
    `GraphIso.cliqueCnfN_eq` and `ramseyCnfN_eq`) compute the same clause lists as the
    interpreted `cliqueCnf` and `ramseyCnf`: small sizes, the showcase sizes (triangle-free on 10
    and 11 vertices, (3,5)-Ramsey on 13), and the fixed-point and neighbourhood formulas built on
    them. The theorems of `GraphOrbits5.lean`, `GraphTree5.lean` and `RamseyC5.lean` use them. -/

open CountCatcher CountCatcher.GraphIso CountCatcher.CycleType

#guard [(4, 3), (5, 3), (5, 4), (6, 3), (7, 4), (8, 3), (10, 3), (11, 3)].all fun (n, s) =>
  (cliqueCnfN n s).clauses == (cliqueCnf n s).clauses
#guard [(5, 3, 3), (6, 3, 4), (8, 3, 4), (9, 3, 4), (13, 3, 5)].all fun (n, s, t) =>
  (ramseyCnfN n s t).clauses == (ramseyCnf n s t).clauses
#guard [[], [2], [3], [2, 2], [3, 2], [5]].all fun l =>
  (symCnf (cliqueCnfN 5 3) (numEdges 5) (edgePerm 5 (rep 5 l))).clauses ==
    (symCnf (cliqueCnf 5 3) (numEdges 5) (edgePerm 5 (rep 5 l))).clauses
#guard [0, 1, 2, 3, 4].all fun k =>
  (nbrCnf (ramseyCnfN 5 3 3) 5 k).clauses == (nbrCnf (ramseyCnf 5 3 3) 5 k).clauses
-- edge variables: the position of `(u, v)` in `edgePairs n` is `edgeVar u v`
#guard (edgePairs 6).length == numEdges 6 && (List.finRange 6).all fun u => (List.finRange 6).all
  fun v => !(u < v) || (edgePairs 6).idxOf (u.val, v.val) == edgeVar u v
