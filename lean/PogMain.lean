import CountCatcherChecker.Rev
import LRATCatcher.Basic

/-! `count-catcher-pog FILE.pog [FORMULA.cnf]`: run part A (and part C with the formula) natively.
    `count-catcher-pog --parse-diff FILE…`: parse each file with `parsePogCert` and with the reference
    parser `parsePogCertRef`, print whether the results agree and both times. -/

def parseDiff (paths : List String) : IO UInt32 := do
  let mut nd := 0
  for p in paths do
    let s ← IO.FS.readFile p
    let t0 ← IO.monoMsNow
    let a := CountCatcher.parsePogCert s
    IO.println s!"{p}: parsed={a.isSome}"
    let t1 ← IO.monoMsNow
    let b := CountCatcher.parsePogCertRef s
    IO.println s!"{p}: reference parsed={b.isSome}"
    let t2 ← IO.monoMsNow
    let same := CountCatcher.samePogCert a b
    unless same do nd := nd + 1
    IO.println s!"{p}: {if same then "same" else "DIFFERENT"} parse_ms={t1 - t0} reference_ms={t2 - t1}"
  IO.println s!"compared {paths.length} different {nd}"
  return (if nd == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  if let "--parse-diff" :: paths := args then return (← parseDiff paths)
  let path :: rest := args
    | IO.eprintln "usage: count-catcher-pog FILE.pog [FORMULA.cnf] | count-catcher-pog --parse-diff FILE…"; return 2
  let t0 ← IO.monoMsNow
  let s ← IO.FS.readFile path
  let some c := CountCatcher.parsePogCert s | IO.println "PARSE-ERROR"; return 1
  let t1 ← IO.monoMsNow
  let V := c.pog.V
  let some st := (List.range c.pog.nodes.size).foldlM (CountCatcher.checkNode V c.pog c.hints) {}
    | IO.println s!"REJECT part A nodes={c.pog.nodes.size}"; return 1
  let some n := CountCatcher.checkPog c | IO.println "REJECT part A (root)"; return 1
  let t2 ← IO.monoMsNow
  IO.println s!"part A ACCEPT count={n} nodes={c.pog.nodes.size} read+parse_ms={t1-t0} check_ms={t2-t1}"
  match rest with
  | [cnfPath] =>
    let F := LRATCatcher.parseDimacs (← IO.FS.readFile cnfPath)
    let t3 ← IO.monoMsNow
    let ok := CountCatcher.checkRevKill V c.pog F c.root
    IO.println s!"part C {if ok then "ACCEPT" else "REJECT"} clauses={F.clauses.size} negation_free={CountCatcher.negationFree V c.pog c.root}"
    -- read the clock only after the result has been printed (pure code may be reordered)
    IO.println s!"part C ms={(← IO.monoMsNow) - t3}"
    if rest.length == 1 && (← IO.getEnv "COUNT_CATCHER_OLD_PARTC").isSome then
      -- differential test against the per-clause check (used before the bit-parallel part C)
      let t4 ← IO.monoMsNow
      let ok0 := CountCatcher.checkRev V c.pog st F c.root
      IO.println s!"part C per-clause {if ok0 then "ACCEPT" else "REJECT"}"
      IO.println s!"part C per-clause ms={(← IO.monoMsNow) - t4}"
    return (if ok then 0 else 1)
  | _ => return 0
