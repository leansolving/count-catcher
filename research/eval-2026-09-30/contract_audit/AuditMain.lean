import McCert.Check
import LRATCatcher.Basic
import LRATCatcher.StreamOracle

/-!
`mccert-audit BUNDLE [TMPDIR]`: differential test driver for the acceptance-contract audit
(research/eval-2026-09-30/contract_audit.md). One process checks every instance of a bundle.

Bundle format (text, one record per instance):

    @inst NAME EXPECTED
    @cnf
    <DIMACS lines, header "p cnf V m">
    @pog
    <POG file lines as written by cpog2lrat>
    @lrat
    <text LRAT lines>
    @end

`EXPECTED` is the brute-force model count computed outside Lean (Python), or `-1`.
`F := LRATCatcher.parseDimacs cnf`, `V` := header variable count.

Per instance the driver runs the verdict that the theorems are about, `checkAll V F pog lrat N`
with `N` = the count computed by part A (so "accepted" means "accepted with that count"), and
independently the streamed route `checkAllAC V F pog N && checkStreamCnf (fwdCnfOf F pog)
certFeed streamFuel` (the stream reader of lrat-catcher reading the LRAT from TMPDIR/s.lrat).
Diagnostics replay the checker stage by stage to name the first failing stage. Output:

    R NAME ACCEPT|REJECT stage=STAGE count=N exp=E bf=B stream=ACCEPT|REJECT flags=...

flags: OK, or any of WRONG (accepted with count ≠ EXPECTED: a soundness failure),
BFDIFF (Lean `modelCount` ≠ EXPECTED), DIAGDIFF (stage diagnosis disagrees with `checkAll`),
STREAMDIFF (streamed verdict ≠ embedded verdict), CDIFF (per-clause part C ≠ bit-parallel).
-/

open Std.Sat McCert

def headerV (cnf : String) : Option Nat := Id.run do
  for line in cnf.splitOn "\n" do
    match (line.splitOn " ").filter (· ≠ "") with
    | "p" :: "cnf" :: v :: _ => return v.toNat?
    | _ => pure ()
  return none

/-- Why node `i` fails `checkNode` (replays its conditions). -/
def nodeReason (V : Nat) (P : Pog) (hints : Array (List Hint)) (st : PState) (i : Nat) : String :=
  match P.nodes[i]? with
  | none => "missing"
  | some n =>
    if !(Pog.Node.args n).all (·.1 < V + i) then "args-not-earlier"
    else match n with
      | .prod args => if (prodFold V st args 0 0 1).isNone then "prod-overlap" else "prod-?"
      | .sum x y =>
        match (hints[i]?.getD []).mapM (hintClause V P i) with
        | none => "sum-hint-ref"
        | some cls => if !rupStrict [x, y] cls then "sum-rup" else "sum-?"

/-- Part A replay: the state, or the first failing node with its reason. -/
def diagA (c : PogCert) : Except String PState := do
  let V := c.pog.V
  let mut st : PState := {}
  for i in [0:c.pog.nodes.size] do
    match checkNode V c.pog c.hints st i with
    | some st' => st := st'
    | none => throw s!"A-node{i}-{nodeReason V c.pog c.hints st i}"
  return st

structure Inst where
  name : String
  expected : Int
  cnf : String
  pog : String
  lrat : String

def verdict (b : Bool) : String := if b then "ACCEPT" else "REJECT"

def runInst (tmp : String) (I : Inst) : IO (Bool × Bool) := do
  let F := LRATCatcher.parseDimacs I.cnf
  let some V := headerV I.cnf
    | IO.println s!"R {I.name} REJECT stage=no-header count=- exp={I.expected} bf=- stream=- flags=NOHEADER"
      return (true, false)
  let bf : Int := if V ≤ 16 then modelCount V F else -1
  -- stage diagnosis
  let mut stage := "none"
  let mut count : Option Nat := none
  let mut cdiff := false
  if !cnfWFb V F then stage := "cnf-wf"
  else match parsePogCert I.pog with
    | none => stage := "pog-parse"
    | some c =>
      if c.pog.V != V then stage := s!"pog-V{c.pog.V}"
      else match diagA c with
        | .error e => stage := e
        | .ok st =>
          if !decide (c.root.1 < c.pog.V + c.pog.nodes.size) then stage := "A-root-range"
          else
            count := some (litCount V st c.root * 2 ^ (V - litSize V st c.root))
            let fast := checkRevKillFast V c.pog F c.root
            let perClause := checkRev V c.pog st F c.root
            cdiff := fast != perClause
            if !negationFree V c.pog c.root then stage := "C-negation"
            else if !fast then
              let j := (F.clauses.toList.findIdx? fun C => !clauseRefuted V c.pog st C c.root).getD 9999
              stage := s!"C-clause{j}"
            else match Std.Tactic.BVDecide.LRAT.parseLRATProof I.lrat.toUTF8 with
              | .error _ => stage := "B-parse"
              | .ok _ =>
                if !LRATCatcher.checkLratCnf (fwdCnf F c.pog c.root) I.lrat then stage := "B-check"
  let N := count.getD 0
  let ok := checkAll V F I.pog I.lrat N
  -- streamed route: parts A and C, part B through lrat-catcher's stream reader
  let okAC := checkAllAC V F I.pog N
  let path := tmp ++ "/s.lrat"
  IO.FS.writeFile path I.lrat
  LRATCatcher.streamReset (some path)
  let okS := okAC && LRATCatcher.checkStreamCnf (fwdCnfOf F I.pog) LRATCatcher.certFeed
    LRATCatcher.streamFuel
  LRATCatcher.streamReset none
  let mut flags : Array String := #[]
  if ok && (I.expected < 0 || (N : Int) != I.expected) then flags := flags.push "WRONG"
  if okS && (I.expected < 0 || (N : Int) != I.expected) then flags := flags.push "WRONGSTREAM"
  if I.expected ≥ 0 && bf != I.expected then flags := flags.push "BFDIFF"
  if ok != (stage == "none") then flags := flags.push "DIAGDIFF"
  if ok != okS then flags := flags.push "STREAMDIFF"
  if cdiff then flags := flags.push "CDIFF"
  let fl := if flags.isEmpty then "OK" else ",".intercalate flags.toList
  let cs := match count with | some n => toString n | none => "-"
  IO.println s!"R {I.name} {verdict ok} stage={stage} count={cs} exp={I.expected} bf={bf} stream={verdict okS} flags={fl}"
  return (flags.isEmpty, ok)

/-- Parse a bundle into instances. -/
def parseBundle (s : String) : Array Inst := Id.run do
  let mut out : Array Inst := #[]
  let mut name := ""
  let mut expd : Int := -1
  let mut sec := ""
  let mut cnf := ""; let mut pog := ""; let mut lrat := ""
  for line in s.splitOn "\n" do
    if line.startsWith "@inst " then
      match (line.splitOn " ").filter (· ≠ "") with
      | [_, n, e] => name := n; expd := e.toInt?.getD (-1)
      | _ => name := "?"; expd := -1
      cnf := ""; pog := ""; lrat := ""; sec := ""
    else if line == "@cnf" then sec := "cnf"
    else if line == "@pog" then sec := "pog"
    else if line == "@lrat" then sec := "lrat"
    else if line == "@end" then
      out := out.push ⟨name, expd, cnf, pog, lrat⟩
      sec := ""
    else if sec == "cnf" then cnf := cnf ++ line ++ "\n"
    else if sec == "pog" then pog := pog ++ line ++ "\n"
    else if sec == "lrat" then lrat := lrat ++ line ++ "\n"
  return out

def main (args : List String) : IO UInt32 := do
  match args with
  | bundle :: rest =>
    let tmp := rest.headD "."
    let insts := parseBundle (← IO.FS.readFile bundle)
    let mut nOk := 0; let mut nBad := 0; let mut nAcc := 0
    for I in insts do
      let (good, acc) ← runInst tmp I
      if good then nOk := nOk + 1 else nBad := nBad + 1
      if acc then nAcc := nAcc + 1
    IO.println s!"SUMMARY {bundle} instances={insts.size} accepted={nAcc} flagged={nBad}"
    return (if nBad == 0 then 0 else 1)
  | _ => IO.eprintln "usage: mccert-audit BUNDLE [TMPDIR]"; return 2
