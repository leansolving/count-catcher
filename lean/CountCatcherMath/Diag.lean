import CountCatcherChecker.Check
import LRATCatcher.Stream

/-!
# CountCatcherMath.Diag — failure reports for `count_models` (unverified)

Reporting only. When the verified check (`checkAll`, `checkAllAC`, lrat-catcher's LRAT check)
rejects a certificate, `count_models` runs these functions to say which part failed and where.
They repeat the checker's steps one node, clause batch or LRAT step at a time, but carry no
proofs: a theorem never depends on them, and a wrong report can only mislead, not prove.

Numbering in the reports: input variables and literals in DIMACS form (variable `x` of `Fin V`
is `x + 1`); POG node `i` defines DIMACS variable `V + 1 + i` and is the `i`-th `p`/`s` line of
the POG file; input clause `k` is the `k`-th clause of the formula (1-based, the clause number
of the exported DIMACS file); LRAT step `k` is line `k` of a text LRAT file.
-/

open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal

namespace CountCatcher.Diag

/-- DIMACS form of a literal. -/
def litStr (l : Literal Nat) : String := if l.2 then toString (l.1 + 1) else s!"-{l.1 + 1}"

def clauseStr (c : CNF.Clause Nat) : String :=
  if c.isEmpty then "the empty clause" else " ".intercalate (c.map litStr) ++ " 0"

/-- At most `k` items, with a count of the rest. -/
def shortList (k : Nat) (xs : List String) : String :=
  " ".intercalate (xs.take k) ++ (if xs.length > k then s!" … ({xs.length - k} more)" else "")

def trunc (s : String) : String :=
  if s.length > 80 then (s.take 80).toString ++ " …" else s

/-! ## POG file -/

private def tokens (line : String) : List String :=
  (line.splitOn " ").filter (· ≠ "")

private def isLit (t : String) : Bool :=
  match t.toInt? with
  | some 0 => false
  | some _ => true
  | none => false

private def isHint (t : String) : Bool :=
  match t.splitOn ":" with
  | [a, b] => a.toNat?.isSome && b.toNat?.isSome
  | _ => false

private def bodyOk (p : String → Bool) (rest : List String) : Bool :=
  rest.getLast? == some "0" && rest.dropLast.all p

/-- Why `parsePogCert` rejects the POG file: the first line it cannot read, or a missing
    header line. -/
def pogParseError (s : String) : String := Id.run do
  let mut ln := 0
  let mut hasV := false
  let mut hasR := false
  for line in s.splitOn "\n" do
    ln := ln + 1
    match tokens line with
    | [] => continue
    | "V" :: [n] =>
      if n.toNat?.isNone then return s!"POG line {ln}: bad universe line '{trunc line}'"
      hasV := true
    | "r" :: [l] =>
      if !isLit l then return s!"POG line {ln}: bad root line '{trunc line}'"
      hasR := true
    | "p" :: rest =>
      if !bodyOk isLit rest then
        return s!"POG line {ln}: malformed product line '{trunc line}' (expected 'p <literals> 0')"
    | "s" :: x :: y :: rest =>
      if !(isLit x && isLit y && bodyOk isHint rest) then
        return s!"POG line {ln}: malformed sum line '{trunc line}' \
          (expected 's <lit> <lit> <node>:<k> … 0')"
    | _ => return s!"POG line {ln}: unrecognized line '{trunc line}'"
  if !hasV then return "the POG file has no universe line 'V <n>'"
  if !hasR then return "the POG file has no root line 'r <literal>'"
  return "the POG file does not parse (no line-level fault found)"

/-- Line numbers (1-based) of the node lines of a POG file, in order. -/
def nodeLines (s : String) : Array Nat := Id.run do
  let mut out := #[]
  let mut ln := 0
  for line in s.splitOn "\n" do
    ln := ln + 1
    match tokens line with
    | "p" :: _ => out := out.push ln
    | "s" :: _ => out := out.push ln
    | _ => pure ()
  return out

/-! ## Part A -/

/-- Lowest set bit below `V`. -/
def lowBit (V x : Nat) : Option Nat := (List.range V).find? x.testBit

def nodeStr (V i : Nat) (lines : Array Nat) : String :=
  s!"node {i} (variable {V + i + 1}" ++
    (match lines[i]? with | some l => s!", POG line {l})" | none => ")")

/-- Why `checkNode` rejects node `i` (the nodes before it were accepted with state `st`). -/
def explainNode (V : Nat) (P : Pog) (hints : Array (List Hint)) (st : PState) (i : Nat)
    (lines : Array Nat) : String :=
  let at_ := nodeStr V i lines
  match P.nodes[i]? with
  | none => s!"{at_}: missing"
  | some n =>
    match (Pog.Node.args n).find? (fun l => !(l.1 < V + i)) with
    | some l => s!"{at_}: argument {litStr l} is not an earlier variable (condition C2)"
    | none =>
      match n with
      | .prod args =>
        let sup := args.toArray.map (litSupp V st)
        let pair := (List.range args.length).findSome? fun j =>
          (List.range j).findSome? fun k =>
            if sup[k]! &&& sup[j]! != 0 then some (k, j) else none
        match pair with
        | some (k, j) =>
          let v := (lowBit V (sup[k]! &&& sup[j]!)).getD 0
          s!"{at_}: product arguments {litStr args[k]!} and {litStr args[j]!} share the \
            input variable {v + 1} (condition C3: supports must be disjoint, polarity ignored)"
        | none => s!"{at_}: product rejected (no overlap found)"
      | .sum x y =>
        match (hints[i]?.getD []).find? (fun h => (hintClause V P i h).isNone) with
        | some h =>
          s!"{at_}: exclusion hint {h.node}:{h.k} does not cite a defining clause of an \
            earlier node (condition C4)"
        | none =>
          s!"{at_}: the exclusion clause {litStr (x.1, !x.2)} {litStr (y.1, !y.2)} 0 of the sum \
            does not follow by strict RUP from the cited defining clauses (condition C4)"

/-- Part A report: the first rejected node, or the root. `none` if part A accepts. -/
def partA (c : PogCert) (lines : Array Nat) : Option String := Id.run do
  let V := c.pog.V
  let mut st : PState := {}
  for i in [0:c.pog.nodes.size] do
    match checkNode V c.pog c.hints st i with
    | some st' => st := st'
    | none => return some (explainNode V c.pog c.hints st i lines)
  unless c.root.1 < V + c.pog.nodes.size do
    return some s!"the root {litStr c.root} is not a declared variable \
      ({V} input variables, {c.pog.nodes.size} nodes)"
  return none

/-! ## Part C -/

/-- A model of the POG that falsifies the clause `C` (a partial assignment as DIMACS literals:
    the literals chosen below the root, then the negated literals of `C`), from the kill masks
    of the one-clause batch `[C]`: a product needs all arguments, a sum one unkilled argument. -/
partial def witness (V : Nat) (P : Pog) (C : CNF.Clause Nat) (r : Literal Nat) : List (Literal Nat) :=
  let occ := Array.ofFn (n := 2 * V) fun x => occMask [C] x.1
  let k := killMasks V P occ
  let alive (l : Literal Nat) : Bool := litKill V occ k l &&& 1 == 0
  let rec go (l : Literal Nat) (seen : Array Bool) (acc : List (Literal Nat)) :
      Array Bool × List (Literal Nat) :=
    if l.1 < V then (seen, l :: acc)
    else if seen[l.1 - V]! then (seen, acc)
    else
      let seen := seen.set! (l.1 - V) true
      match P.nodes[l.1 - V]? with
      | some (.prod args) => args.foldl (fun (s, a) x => go x s a) (seen, acc)
      | some (.sum x y) => if alive x then go x seen acc else go y seen acc
      | none => (seen, acc)
  let (_, lits) := go r (Array.replicate P.nodes.size false) []
  let lits := lits.reverse.eraseDups
  lits ++ (C.map fun l => (l.1, !l.2)).filter fun l => !lits.any (·.1 == l.1)

/-- Part C report: a POG outside the negation-free fragment, or the first input clause that
    the POG does not imply (with a witness). `none` if part C accepts. -/
def partC (V : Nat) (P : Pog) (F : CNF Nat) (r : Literal Nat) (lines : Array Nat) :
    Option String := Id.run do
  unless r.1 < V || r.2 do
    return some s!"the root {litStr r} is a negated node; part C accepts only negation-free \
      POGs (no negated edge into an internal node, positive root), as cpog-gen writes them"
  match (List.range P.nodes.size).find? (fun i =>
      !(((P.nodes[i]?).map Pog.Node.args |>.getD []).all fun l => l.1 < V || l.2)) with
  | some i =>
    return some s!"{nodeStr V i lines} has a negated edge into an internal node; part C \
      accepts only negation-free POGs"
  | none => pure ()
  let css := chunks 63 F.clauses.size F.clauses.toList
  let mut b := 0
  for cs in css do
    let occ := Array.ofFn (n := 2 * V) fun x => occMask cs x.1
    let req := reqMask cs
    let kill := litKill V occ (killMasks V P occ) r
    let miss := req ^^^ (req &&& kill)
    if miss != 0 then
      let j := (lowBit 64 miss).getD 0
      let C := cs[j]!
      let w := (witness V P C r).map litStr
      return some s!"input clause {63 * b + j + 1} ({clauseStr C}) is not implied by the POG: \
        the assignment {shortList 24 w} satisfies the POG root {litStr r} and falsifies \
        the clause (the circuit has models that are not models of the formula)"
    b := b + 1
  return none

/-! ## Part B -/

/-- What it means that step `a` fails. -/
def failStr : IntAction → String
  | .addEmpty _ hints => s!"the empty clause does not follow by RUP from its {hints.size} hints"
  | .addRup id c hints =>
    s!"clause {id} ({shortList 12 (c.toList.map toString)} 0) does not follow by RUP from its \
      {hints.size} hints"
  | .addRat id c _ rup rat =>
    s!"RAT clause {id} ({shortList 12 (c.toList.map toString)} 0) fails \
      ({rup.size} RUP hints, {rat.size} RAT groups)"
  | .del ids => s!"deletion of {ids.size} clauses fails"

/-- Part B report for the LRAT proof `acts` against `cnf`, one step at a time with
    lrat-catcher's `runChunk` (which mirrors the core checker): the first step that fails,
    or the end of the proof without the empty clause. `normalize` applies lrat-catcher's
    stream normalization (empty-hint additions as pivot RAT steps). `none` if it refutes. -/
def partBActions (cnf : CNF Nat) (acts : Array IntAction) (normalize : Bool) : Option String :=
  Id.run do
    let mut f := CNF.convertLRAT cnf
    let mut idx := 0
    for a in acts do
      idx := idx + 1
      let a := if normalize then LRATCatcher.normalizeAction a else a
      match LRATCatcher.runChunk f #[a] 0 with
      | some .refuted => return none
      | some (.more f') => f := f'
      | none => return some s!"step {idx} (line {idx} of a text LRAT file): {failStr a}"
    return some s!"the LRAT proof ends after {acts.size} steps without deriving the empty clause"

def partB (cnf : CNF Nat) (lrat : ByteArray) (normalize : Bool) : Option String :=
  match parseLRATProof lrat with
  | .error e => some s!"LRAT parse error: {e}"
  | .ok acts => partBActions cnf acts normalize

/-! ## Whole checks -/

/-- Universe and well-formedness: the certificate's universe equals `V` and every variable of
    `F` lies in `Fin V`. -/
def universeReport (V : Nat) (F : CNF Nat) (c : PogCert) : List String :=
  (if c.pog.V != V then
    [s!"universe: the certificate is for {c.pog.V} variables (its 'V' line, from the \
      header of the counted DIMACS file), the theorem's universe is Fin {V}"]
  else []) ++
  (match (List.range F.clauses.size).findSome? (fun k =>
      (F.clauses[k]!.find? (fun l => !(l.1 < V))).map (k, ·)) with
   | some (k, l) =>
     [s!"universe: input clause {k + 1} ({clauseStr F.clauses[k]!}) uses variable \
       {l.1 + 1}, outside Fin {V}"]
   | none => [])

/-- Reports for everything `checkAll V F pogStr lratStr N` checks, or for `checkAllAC` when
    `lrat? = none`. An empty list means that no fault was found. -/
def report (V : Nat) (F : CNF Nat) (pogStr : String) (lrat? : Option ByteArray) (N : Nat)
    (hinted : Bool := false) : List String :=
  match parsePogCert pogStr with
  | none => [s!"certificate: {pogParseError pogStr}"]
  | some c =>
    let lines := nodeLines pogStr
    let u := universeReport V F c
    let a := match partA c lines with
      | some m => [s!"part A (POG validity): {m}"]
      | none =>
        match checkPog c with
        | some n =>
          if n == N then []
          else if hinted then
            [s!"part A (count): the certificate's count is {n}, not the hinted (count := {N})"]
          else [s!"part A (count): the certificate's count is {n}, the theorem states {N}"]
        | none => []
    let cc := match partC c.pog.V c.pog F c.root lines with
      | some m => [s!"part C (every input clause implied by the POG): {m}"]
      | none => []
    let b := match lrat? with
      | some l => match partB (fwdCnf F c.pog c.root) l false with
        | some m => [s!"part B (LRAT refutation of F, the defining clauses and ¬root): {m}"]
        | none => []
      | none => []
    u ++ a ++ b ++ cc

end CountCatcher.Diag
