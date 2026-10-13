import CountCatcherMath.Families.QueensSym

/-! DIMACS export of the eight fixed-point formulas `symCnf (cnf n) (n * n) (cellPerm n g)` of
    the n-queens CNF, straight from the Lean terms (clause order as in the theorem, so the
    certificates' clause IDs match). `n` comes from `QSYM_N`, the output directory from
    `QSYM_OUT`; the files are `qsNN_E.cnf` with `E` in `r0 r1 r2 r3 s0 s1 s2 s3` for
    `r 0, …, r 3, sr 0, …, sr 3`. `qsNN_r0.cnf` equals `scripts/gen_queens.py n` clause for
    clause. Usage: `QSYM_N=14 QSYM_OUT=/tmp lake env lean test/QueensSymExport.lean`. -/

open CountCatcher CountCatcher.Queens

#eval show IO Unit from do
  let n := ((← IO.getEnv "QSYM_N").bind String.toNat?).getD 8
  let dir := (← IO.getEnv "QSYM_OUT").getD "."
  let els : List (String × DihedralGroup 4) :=
    [("r0", .r 0), ("r1", .r 1), ("r2", .r 2), ("r3", .r 3),
     ("s0", .sr 0), ("s1", .sr 1), ("s2", .sr 2), ("s3", .sr 3)]
  let nn := if n < 10 then s!"0{n}" else s!"{n}"
  for (e, g) in els do
    let path := s!"{dir}/qs{nn}_{e}.cnf"
    IO.FS.writeFile path (symCnf (cnf n) (n * n) (cellPerm n g)).dimacs
    IO.println s!"wrote {path}"
