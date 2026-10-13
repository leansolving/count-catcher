import CountCatcherChecker.Check
import CountCatcherChecker.FwdSel
import CountCatcherChecker.Rev
import LRATCatcher.Basic
import LRATCatcher.Reflect
import LRATCatcher.StreamOracle

/-!
`count-catcher-audit BUNDLE [TMPDIR]`: differential test driver (research/eval-2026-10-07/
difftest_rerun.md; port of research/eval-2026-09-30/contract_audit/AuditMain.lean to the renamed
tree, extended by the shipped default route). One process checks every record of a bundle.

Bundle format (text, one record per certificate):

    @inst NAME EXPECTED
    @cnf
    <DIMACS lines, header "p cnf V m">
    @pog
    <POG file lines as written by cpog2lrat>
    @lrat                  -- text route: a text LRAT proof
    <text LRAT lines>
    @end

or, for the default route, instead of `@lrat`:

    @bin
    <one line: the binary LRAT file in lowercase hex>
    @keep
    <one line: the keep mask, possibly empty>
    @end

`EXPECTED` is the brute-force model count computed outside Lean (Python), or `-1`.
`F := LRATCatcher.parseDimacs cnf` (the `count_models thm "f.cnf" …` form), `V` := header
variable count. The count `N` is part A's count, so "accepted" means "accepted with that count".

Text route (as on 2026-09-30): the verdict is the embedded check `checkAll V F pog lrat N`
(`count_models +embed`); the streamed route `checkAllAC V F pog N && checkStreamCnf (fwdCnfOf F pog)
certFeed streamFuel` (`count_models +stream` without a keep file) reads the LRAT from
TMPDIR/s.lrat through lrat-catcher's stream reader and is compared with it.

Default route (new): the verdict is `checkAllAC V F pog N && checkStreamCnf (fwdCnfOfSel F pog keep)
certFeed streamFuel` with the binary LRAT in TMPDIR/k.lrat, exactly the two native evaluations of
`count_models thm "f.cnf" "fwd.pog" "fwd.lrat" (keep := "fwd.keep")` (CountCatcherMath/Command.lean,
`countRoute`, streamed branch). For comparison it also runs Lean core's LRAT check on the parsed
binary proof against `fwdCnfSel` (embedded, no `normalizeAction`).

Diagnostics replay the checker stage by stage to name the first failing stage. Output:

    R NAME ACCEPT|REJECT stage=STAGE count=N exp=E bf=B stream=ACCEPT|REJECT|- route=text|default flags=...

where `stream=` is the streamed text route (text records) or the embedded core check of the binary
proof (default records). flags: OK, or any of WRONG (accepted with count ≠ EXPECTED: a soundness
failure), WRONGSTREAM (the streamed text route accepted with count ≠ EXPECTED), BFDIFF (Lean
`modelCount` ≠ EXPECTED), DIAGDIFF (stage diagnosis disagrees with the verdict), STREAMDIFF (text:
streamed verdict ≠ embedded verdict), EMBDIFF (default: embedded core check of the binary proof ≠
streamed part B, informational), CDIFF (per-clause part C ≠ bit-parallel). Positive control: a record
whose name contains `/control` has a deliberately false EXPECTED; it must be flagged WRONG, and is
then reported with the flag CONTROL-OK (CONTROL-FAIL otherwise, which counts as flagged).
-/

open Std.Sat CountCatcher

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

/-- Stages before part B: the first failing stage (`none` if parts A and C pass), part A's count,
    whether per-clause part C differs from the bit-parallel one, and the parsed certificate. -/
def diagAC (V : Nat) (F : CNF Nat) (pog : String) : String × Option Nat × Bool × Option PogCert :=
  Id.run do
  if !cnfWFb V F then return ("cnf-wf", none, false, none)
  match parsePogCert pog with
  | none => return ("pog-parse", none, false, none)
  | some c =>
    if c.pog.V != V then return (s!"pog-V{c.pog.V}", none, false, some c)
    match diagA c with
    | .error e => return (e, none, false, some c)
    | .ok st =>
      if !decide (c.root.1 < c.pog.V + c.pog.nodes.size) then return ("A-root-range", none, false, some c)
      let count := litCount V st c.root * 2 ^ (V - litSize V st c.root)
      let fast := checkRevKillFast V c.pog F c.root
      let perClause := checkRev V c.pog st F c.root
      let cdiff := fast != perClause
      if !negationFree V c.pog c.root then return ("C-negation", some count, cdiff, some c)
      if !fast then
        let j := (F.clauses.toList.findIdx? fun C => !clauseRefuted V c.pog st C c.root).getD 9999
        return (s!"C-clause{j}", some count, cdiff, some c)
      return ("none", some count, cdiff, some c)

/-- Forces the evaluation of `b` before the next IO action (the stream reader is reset after it). -/
@[noinline] def forceBool (b : Bool) : IO Bool := pure b

def hexVal (b : UInt8) : UInt8 :=
  if 48 ≤ b && b ≤ 57 then b - 48 else if 97 ≤ b && b ≤ 102 then b - 87 else 0

def decodeHex (s : String) : ByteArray := Id.run do
  let bs := s.toUTF8
  let mut out := ByteArray.emptyWithCapacity (bs.size / 2)
  let mut i := 0
  while i + 1 < bs.size do
    out := out.push (hexVal bs[i]! * 16 + hexVal bs[i + 1]!)
    i := i + 2
  return out

inductive Proof where
  | text (lrat : String)
  | bin (hex : String) (keep : String)

structure Inst where
  name : String
  expected : Int
  cnf : String
  pog : String
  proof : Proof

def verdict (b : Bool) : String := if b then "ACCEPT" else "REJECT"

def runInst (tmp : String) (I : Inst) : IO (Bool × Bool) := do
  let F := LRATCatcher.parseDimacs I.cnf
  let some V := headerV I.cnf
    | IO.println s!"R {I.name} REJECT stage=no-header count=- exp={I.expected} bf=- stream=- route=- flags=NOHEADER"
      return (false, false)
  let bf : Int := if V ≤ 16 then modelCount V F else -1
  let (stAC, count, cdiff, c?) := diagAC V F I.pog
  let N := count.getD 0
  let mut flags : Array String := #[]
  let mut stage := stAC
  let mut ok := false
  let mut other := "-"
  let mut route := "text"
  match I.proof with
  | .text lrat =>
    if stAC == "none" then
      match c? with
      | some c =>
        match Std.Tactic.BVDecide.LRAT.parseLRATProof lrat.toUTF8 with
        | .error _ => stage := "B-parse"
        | .ok _ =>
          if !LRATCatcher.checkLratCnf (fwdCnf F c.pog c.root) lrat then stage := "B-check"
      | none => stage := "B-?"
    ok := checkAll V F I.pog lrat N
    -- streamed route: parts A and C, part B through lrat-catcher's stream reader (text)
    let okAC := checkAllAC V F I.pog N
    let path := tmp ++ "/s.lrat"
    IO.FS.writeFile path lrat
    LRATCatcher.streamReset (some path)
    let okS ← forceBool (okAC && LRATCatcher.checkStreamCnf (fwdCnfOf F I.pog) LRATCatcher.certFeed
      LRATCatcher.streamFuel)
    LRATCatcher.streamReset none
    other := verdict okS
    if okS && (I.expected < 0 || (N : Int) != I.expected) then flags := flags.push "WRONGSTREAM"
    if ok != okS then flags := flags.push "STREAMDIFF"
  | .bin hex keep =>
    route := "default"
    let bytes := decodeHex hex
    let path := tmp ++ "/k.lrat"
    IO.FS.writeBinFile path bytes
    -- part B as `count_models … (keep := …)` runs it: the streamed check of the selected clauses
    LRATCatcher.streamReset (some path)
    let okB ← forceBool (LRATCatcher.checkStreamCnf (fwdCnfOfSel F I.pog keep) LRATCatcher.certFeed
      LRATCatcher.streamFuel)
    LRATCatcher.streamReset none
    let okAC := checkAllAC V F I.pog N
    ok := okAC && okB
    if stAC == "none" then
      match c? with
      | some c =>
        let emb := match Std.Tactic.BVDecide.LRAT.parseLRATProof bytes with
          | .ok p => Std.Tactic.BVDecide.LRAT.check p (fwdCnfSel F c.pog c.root keep)
          | .error _ => false
        other := verdict emb
        if emb != okB then flags := flags.push "EMBDIFF"
        if !okB then
          stage := match Std.Tactic.BVDecide.LRAT.parseLRATProof bytes with
            | .error _ => "B-parse"
            | .ok _ => "B-check"
      | none => stage := "B-?"
  let isControl := (I.name.splitOn "/control").length > 1
  if ok && (I.expected < 0 || (N : Int) != I.expected) then flags := flags.push "WRONG"
  if I.expected ≥ 0 && bf != I.expected && !isControl then flags := flags.push "BFDIFF"
  if ok != (stage == "none") then flags := flags.push "DIAGDIFF"
  if cdiff then flags := flags.push "CDIFF"
  let mut good := flags.isEmpty || flags == #["EMBDIFF"]
  if isControl then
    if flags.contains "WRONG" then
      flags := #["CONTROL-OK"]
      good := true
    else
      flags := flags.push "CONTROL-FAIL"
      good := false
  let fl := if flags.isEmpty then "OK" else ",".intercalate flags.toList
  let cs := match count with | some n => toString n | none => "-"
  IO.println s!"R {I.name} {verdict ok} stage={stage} count={cs} exp={I.expected} bf={bf} stream={other} route={route} flags={fl}"
  return (good, ok)

/-- Parse a bundle into instances. -/
def parseBundle (s : String) : Array Inst := Id.run do
  let mut out : Array Inst := #[]
  let mut name := ""
  let mut expd : Int := -1
  let mut sec := ""
  let mut cnf := ""; let mut pog := ""; let mut lrat := ""; let mut hex := ""; let mut keep := ""
  let mut isBin := false
  for line in s.splitOn "\n" do
    if line.startsWith "@inst " then
      match (line.splitOn " ").filter (· ≠ "") with
      | [_, n, e] => name := n; expd := e.toInt?.getD (-1)
      | _ => name := "?"; expd := -1
      cnf := ""; pog := ""; lrat := ""; hex := ""; keep := ""; sec := ""; isBin := false
    else if line == "@cnf" then sec := "cnf"
    else if line == "@pog" then sec := "pog"
    else if line == "@lrat" then sec := "lrat"
    else if line == "@bin" then sec := "bin"; isBin := true
    else if line == "@keep" then sec := "keep"
    else if line == "@end" then
      out := out.push ⟨name, expd, cnf, pog, if isBin then .bin hex keep else .text lrat⟩
      sec := ""
    else if sec == "cnf" then cnf := cnf ++ line ++ "\n"
    else if sec == "pog" then pog := pog ++ line ++ "\n"
    else if sec == "lrat" then lrat := lrat ++ line ++ "\n"
    else if sec == "bin" then hex := hex ++ line
    else if sec == "keep" then keep := keep ++ line
  return out

def main (args : List String) : IO UInt32 := do
  match args with
  | bundle :: rest =>
    let tmp := rest.headD "."
    let insts := parseBundle (← IO.FS.readFile bundle)
    let mut nOk := 0; let mut nBad := 0; let mut nAcc := 0; let mut nCtl := 0
    for I in insts do
      let (good, acc) ← runInst tmp I
      if good then nOk := nOk + 1 else nBad := nBad + 1
      if acc then nAcc := nAcc + 1
      if (I.name.splitOn "/control").length > 1 then nCtl := nCtl + 1
    IO.println s!"SUMMARY {bundle} instances={insts.size} accepted={nAcc} controls={nCtl} flagged={nBad}"
    return (if nBad == 0 then 0 else 1)
  | _ => IO.eprintln "usage: count-catcher-audit BUNDLE [TMPDIR]"; return 2
