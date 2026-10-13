import CountCatcherChecker.RevFast
import CountCatcherChecker.RevTD
import LRATCatcher.Basic

/-! `count-catcher-partc FILE.pog FORMULA.cnf [MODE]` or `count-catcher-partc --list FILE [MODE]`: part C
    verdicts and times. A list file has one `NAME POG CNF` per line. Exit code 1 if any case
    differs.

    Modes `both|old|new`: `checkRevKill` (occurrence table per batch) against
    `checkRevKillFast` (one reused table). Output per case: `partc NAME V= m= nodes= old=… new=…
    old_ms= new_ms= SAME|DIFF`.

    Modes `m1|m2|m3|m4|all`: M1 per-clause `checkRev` (part A runs first, outside
    the clock), M2 top-down `checkRevTD` without, M3 with support signatures, M4
    `checkRevKillFast`; `all` runs part A, M4, M3, M2, M1 and compares the verdicts. Output per
    method: `partc-m NAME METHOD VERDICT ms= visits= maxv=` (visits for M2 and M3 only), then
    `partc NAME V= m= nodes= partA= … SAME|DIFF`. -/

open CountCatcher

def verdict (b : Bool) : String := if b then "ACCEPT" else "REJECT"

/-- Print and flush (a run killed by a timeout keeps what it printed). -/
def say (s : String) : IO Unit := do IO.println s; (← IO.getStdout).flush

def runD20 (name : String) (c : PogCert) (F : Std.Sat.CNF Nat) (mode : String) : IO Bool := do
  let V := c.pog.V
  let mut vOld := ""; let mut vNew := ""; let mut msOld := 0; let mut msNew := 0
  if mode != "old" then
    let t0 ← IO.monoMsNow
    let ok := checkRevKillFast V c.pog F c.root
    IO.println s!"partc-new {name} {verdict ok}"
    msNew := (← IO.monoMsNow) - t0
    vNew := verdict ok
  if mode != "new" then
    let t0 ← IO.monoMsNow
    let ok := checkRevKill V c.pog F c.root
    IO.println s!"partc-old {name} {verdict ok}"
    msOld := (← IO.monoMsNow) - t0
    vOld := verdict ok
  let same := mode != "both" || vOld == vNew
  IO.println s!"partc {name} V={V} m={F.clauses.size} nodes={c.pog.nodes.size} old={vOld} new={vNew} old_ms={msOld} new_ms={msNew} {if same then "SAME" else "DIFF"}"
  return same

/-- One method; the verdict is printed before the clock is read (pure code may be moved). -/
def runMethod (name meth : String) (c : PogCert) (F : Std.Sat.CNF Nat) (st? : Option PState) :
    IO (Option Bool) := do
  let V := c.pog.V
  let t0 ← IO.monoMsNow
  match meth with
  | "m4" =>
    let ok := checkRevKillFast V c.pog F c.root
    say s!"partc-v {name} m4 {verdict ok}"
    say s!"partc-m {name} m4 {verdict ok} ms={(← IO.monoMsNow) - t0}"
    return some ok
  | "m2" | "m3" =>
    let (ok, visits, mx) := checkRevTD V (meth == "m3") c.pog F c.root
    say s!"partc-v {name} {meth} {verdict ok}"
    say s!"partc-m {name} {meth} {verdict ok} ms={(← IO.monoMsNow) - t0} visits={visits} maxv={mx}"
    return some ok
  | _ =>
    match st? with
    | none => say s!"partc-m {name} m1 NA (part A rejected)"; return none
    | some st =>
      let ok := checkRev V c.pog st F c.root
      say s!"partc-v {name} m1 {verdict ok}"
      say s!"partc-m {name} m1 {verdict ok} ms={(← IO.monoMsNow) - t0}"
      return some ok

def runMethods (name : String) (c : PogCert) (F : Std.Sat.CNF Nat) (mode : String) : IO Bool := do
  let V := c.pog.V
  let meths := if mode == "all" then ["m4", "m3", "m2", "m1"] else [mode]
  let st? ← if meths.contains "m1" then do
      let t0 ← IO.monoMsNow
      let st? := (List.range c.pog.nodes.size).foldlM (checkNode V c.pog c.hints) {}
      say s!"partc-a {name} {if st?.isSome then "ACCEPT" else "REJECT"} ms={(← IO.monoMsNow) - t0}"
      pure st?
    else pure none
  let mut vs : List (String × Bool) := []
  for m in meths do
    if let some ok ← runMethod name m c F st? then vs := vs ++ [(m, ok)]
  let same := vs.all fun (_, b) => some b == (vs.head?.map (·.2))
  let partA := if meths.contains "m1" then verdict st?.isSome else "-"
  IO.println s!"partc {name} V={V} m={F.clauses.size} nodes={c.pog.nodes.size} partA={partA} {" ".intercalate (vs.map fun (m, b) => s!"{m}={verdict b}")} {if same then "SAME" else "DIFF"}"
  return same

def runOne (name pogPath cnfPath mode : String) : IO Bool := do
  let t0 ← IO.monoMsNow
  let s ← IO.FS.readFile pogPath
  let some c := parsePogCert s | IO.println s!"partc {name} PARSE-ERROR"; return true
  let F := LRATCatcher.parseDimacs (← IO.FS.readFile cnfPath)
  -- force both parses before the clocks are read (pure code may be floated past them)
  say s!"partc-start {name} V={c.pog.V} m={F.clauses.size} nodes={c.pog.nodes.size}"
  say s!"partc-load {name} ms={(← IO.monoMsNow) - t0}"
  if ["both", "old", "new"].contains mode then runD20 name c F mode
  else runMethods name c F mode

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--list", path] | ["--list", path, _] =>
    let mode := args.getD 2 "both"
    let mut allSame := true
    for line in (← IO.FS.lines path) do
      match (line.splitOn " ").filter (· ≠ "") with
      | [name, pog, cnf] => allSame := (← runOne name pog cnf mode) && allSame
      | _ => pure ()
    IO.println s!"partc-summary {if allSame then "ALL-SAME" else "SOME-DIFF"}"
    return (if allSame then 0 else 1)
  | [pog, cnf] | [pog, cnf, _] =>
    let same ← runOne pog pog cnf (args.getD 2 "both")
    return (if same then 0 else 1)
  | _ =>
    IO.eprintln "usage: count-catcher-partc FILE.pog FORMULA.cnf [both|old|new|m1|m2|m3|m4|all] | --list FILE [mode]"
    return 2
