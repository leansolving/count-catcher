import CountCatcherChecker.Spec
import CountCatcherChecker.Popcount

/-!
# CountCatcherChecker.Pog — part A: POG validity and counts, executable

Input: the node table written by `scripts/cpog2lrat.py` (untrusted), parsed into a
`Spec.Pog` plus exclusion hints and the root literal. The format fixes extension variable
`V + i` for node `i` (C2 by construction) and writes each exclusion hint as a pair (earlier
node, index of one of its defining clauses), so a hint can only cite a defining clause
(C4 by construction). This module checks the rest:

* every argument refers to an earlier variable;
* products: pairwise disjoint original-variable supports, polarity ignored (C3);
* sums: the exclusion clause `¬x ∨ ¬y` by strict RUP over the cited defining clauses (C4);
* the root refers to a declared variable;

and computes supports (bitsets over the original variables) and support-local counts.
Soundness: `CountCatcherMath.checkPog_sound` (`checkPog c = some N → c.pog.WF ∧ … ∧ N =
c.pog.countRoot c.root`) and `checkPog_sound_of_fold`.
-/

open Std.Sat

namespace CountCatcher

/-- DIMACS literal to `Std.Sat` literal (0-indexed variable). -/
def ofDimacs (l : Int) : Literal Nat := (l.natAbs - 1, decide (0 < l))

/-- Exclusion hint: defining clause `k` of node `node`. -/
structure Hint where
  node : Nat
  k : Nat
  deriving Repr, DecidableEq

structure PogCert where
  pog : Pog
  hints : Array (List Hint)  -- per node, empty for products
  root : Literal Nat
  deriving Repr

/-! ## Parsing (untrusted: the theorem is about whatever was parsed) -/

/-- A nonzero DIMACS literal (`0` is the terminator, never a literal). -/
private def parseLit? (t : String) : Option Int :=
  match t.toInt? with
  | some 0 => none
  | l => l

/-- The tokens before the terminating `0` of a declaration line. -/
private def body? (rest : List String) : Option (List String) :=
  if rest.getLast? == some "0" then some rest.dropLast else none

private def parseHint? (t : String) : Option Hint :=
  match t.splitOn ":" with
  | [a, b] => do pure ⟨← a.toNat?, ← b.toNat?⟩
  | _ => none

/-- Reference parser (the `parsePogCert` up to 2026-10-01, on `String.splitOn`), kept for the
    differential tests of `parsePogCert` (`test/PogParse.lean`, `count-catcher-pog --parse-diff`). -/
def parsePogCertRef (s : String) : Option PogCert := Id.run do
  let mut nv : Option Nat := none
  let mut root : Option Int := none
  let mut nodes : Array Node := #[]
  let mut hints : Array (List Hint) := #[]
  for line in s.splitOn "\n" do
    let toks := (line.splitOn " ").filter (· ≠ "")
    match toks with
    | [] => continue
    | "V" :: [n] => nv := n.toNat?
    | "r" :: [l] => root := parseLit? l
    | "p" :: rest =>
      match (body? rest).bind (·.mapM parseLit?) with
      | some ls => nodes := nodes.push (.prod (ls.map ofDimacs)); hints := hints.push []
      | none => return none
    | "s" :: x :: y :: rest =>
      match parseLit? x, parseLit? y, (body? rest).bind (·.mapM parseHint?) with
      | some x, some y, some hs =>
        nodes := nodes.push (.sum (ofDimacs x) (ofDimacs y)); hints := hints.push hs
      | _, _, _ => return none
    | _ => return none
  match nv, root with
  | some v, some r => return some ⟨⟨v, nodes⟩, hints, ofDimacs r⟩
  | _, _ => return none

/-! Byte-level parser. It reads the UTF-8 bytes of the string in place (`String.getUTF8Byte`,
constant time) and builds no line or token strings. It is tested to reproduce `parsePogCertRef`
(no theorem proves it):

* lines end at `'\n'` only, tokens are separated by `' '` only (`'\r'` and tabs are token bytes);
  a line of spaces is skipped;
* `V n` and `r l` (exactly one argument) set the universe and the root; the last such line
  counts, and an argument that does not parse sets `none` instead of rejecting;
* `p l* 0` and `s x y h* 0`: the last token is exactly `0`, literals are nonzero
  `String.toInt?` values, hints `a:b` with one colon and two `String.toNat?` values;
* numbers as `String.toNat?`: decimal digits with single `_` separators between digits, leading
  zeros allowed, no `+`, any size; `-0` is `0` (no literal);
* every other line rejects the file, and so does a missing `V` or `r` value at the end. -/

namespace PogParse

/-- Byte `i` of `s` (`'\n'` past the end). -/
@[inline] def byteAt (s : String) (i : Nat) : UInt8 :=
  if h : i < s.utf8ByteSize then s.getUTF8Byte ⟨i⟩ h else 10

/-- The first position from `i` on that holds no space (`n` is the byte length of `s`). -/
def skipSp (s : String) (n i : Nat) : Nat :=
  if i < n then (if byteAt s i == 32 then skipSp s n (i + 1) else i) else i
termination_by n - i

/-- The end of the token at `i`: the first space or newline from `i` on, or `n`. -/
def tokEnd (s : String) (n i : Nat) : Nat :=
  if i < n then
    let b := byteAt s i
    if b == 32 || b == 10 then i else tokEnd s n (i + 1)
  else i
termination_by n - i

/-- `String.toNat?` on the bytes `[i, j)` as a code: `0` for `none`, the value plus one
    otherwise (decimal digits, each `_` after a digit and not at the end, as
    `String.Slice.isNat`). -/
def natCode (s : String) (j i acc : Nat) (lastDigit : Bool) : Nat :=
  if i < j then
    let b := byteAt s i
    if b == 95 then (if lastDigit then natCode s j (i + 1) acc false else 0)
    else if 48 ≤ b && b ≤ 57 then natCode s j (i + 1) (acc * 10 + (b - 48).toNat) true
    else 0
  else if lastDigit then acc + 1 else 0
termination_by j - i

/-- A nonzero `String.toInt?` on `[i, j)`, as the literal `ofDimacs`. -/
@[inline] def litAt (s : String) (i j : Nat) : Option (Literal Nat) :=
  let neg := i < j && byteAt s i == 45
  let c := natCode s j (if neg then i + 1 else i) 0 false
  if c ≤ 1 then none else some (c - 2, !neg)

/-- The first `:` in `[i, j)`, or `j`. -/
def colonAt (s : String) (j i : Nat) : Nat :=
  if i < j then (if byteAt s i == 58 then i else colonAt s j (i + 1)) else j
termination_by j - i

/-- A hint `a:b` on `[i, j)`: one colon between two `String.toNat?` numbers (a second colon
    makes `b` fail). -/
@[inline] def hintAt (s : String) (i j : Nat) : Option Hint :=
  let c := colonAt s j i
  if c < j then
    let a := natCode s c i 0 false
    let b := natCode s j (c + 1) 0 false
    if a == 0 || b == 0 then none else some ⟨a - 1, b - 1⟩
  else none

/-- After the token `0` ending at `j`, the line must end: the start of the next line. -/
@[inline] def lineEnd? (s : String) (n j : Nat) : Option Nat :=
  let k := skipSp s n j
  if k < n then (if byteAt s k == 10 then some (k + 1) else none) else some k

/-- The arguments of a `p` line from `i` on: literals up to the token `0`, which must end the
    line. The start of the next line and the literals in order. `fuel` bounds the tokens. -/
def pBody (s : String) (n : Nat) :
    Nat → Nat → List (Literal Nat) → Option (Nat × List (Literal Nat))
  | 0, _, _ => none
  | fuel + 1, i, acc =>
    let i := skipSp s n i
    if i < n && byteAt s i != 10 then
      let j := tokEnd s n i
      if j == i + 1 && byteAt s i == 48 then (lineEnd? s n j).map (·, acc.reverse)
      else match litAt s i j with
        | some l => pBody s n fuel j (l :: acc)
        | none => none
    else none

/-- The hints of an `s` line from `i` on, up to the token `0`, which must end the line. -/
def sBody (s : String) (n : Nat) : Nat → Nat → List Hint → Option (Nat × List Hint)
  | 0, _, _ => none
  | fuel + 1, i, acc =>
    let i := skipSp s n i
    if i < n && byteAt s i != 10 then
      let j := tokEnd s n i
      if j == i + 1 && byteAt s i == 48 then (lineEnd? s n j).map (·, acc.reverse)
      else match hintAt s i j with
        | some h => sBody s n fuel j (h :: acc)
        | none => none
    else none

/-- The bounds of the next token of the line from `i` on, `none` at the end of the line. -/
@[inline] def nextTok? (s : String) (n i : Nat) : Option (Nat × Nat) :=
  let i := skipSp s n i
  if i < n && byteAt s i != 10 then some (i, tokEnd s n i) else none

/-- The lines from `i` on, with the universe, root, nodes and hints read so far. Every line
    consumes at least one byte, so `fuel = n + 1` suffices. -/
def lines (s : String) (n : Nat) :
    Nat → Nat → Option Nat → Option (Literal Nat) → Array Node → Array (List Hint) →
      Option PogCert
  | 0, _, _, _, _, _ => none
  | fuel + 1, i, nv, root, nodes, hints =>
    let a := skipSp s n i
    if a < n then
      let b := byteAt s a
      if b == 10 then lines s n fuel (a + 1) nv root nodes hints
      else if tokEnd s n a != a + 1 then none
      else if b == 112 then  -- `p`
        match pBody s n (n + 1) (a + 1) [] with
        | some (k, ls) => lines s n fuel k nv root (nodes.push (.prod ls)) (hints.push [])
        | none => none
      else if b == 115 then  -- `s`
        match nextTok? s n (a + 1) with
        | none => none
        | some (x0, x1) =>
          match nextTok? s n x1 with
          | none => none
          | some (y0, y1) =>
            match litAt s x0 x1, litAt s y0 y1, sBody s n (n + 1) y1 [] with
            | some x, some y, some (k, hs) =>
              lines s n fuel k nv root (nodes.push (.sum x y)) (hints.push hs)
            | _, _, _ => none
      else if b == 86 || b == 114 then  -- `V` or `r`: exactly one argument
        match nextTok? s n (a + 1) with
        | none => none
        | some (t0, t1) =>
          if (nextTok? s n t1).isSome then none
          else
            let k := skipSp s n t1
            let k := if k < n then k + 1 else k
            if b == 86 then
              let c := natCode s t1 t0 0 false
              lines s n fuel k (if c == 0 then none else some (c - 1)) root nodes hints
            else lines s n fuel k nv (litAt s t0 t1) nodes hints
      else none
    else
      match nv, root with
      | some v, some r => some ⟨⟨v, nodes⟩, hints, r⟩
      | _, _ => none

end PogParse

/-- Parse the POG file: `V <n>`, `r <lit>`, then `p <lits> 0` or `s <x> <y> <n:k>* 0` lines
    (byte-level; meant to give the same result as `parsePogCertRef`, differential tests in
    `test/PogParse.lean` and `count-catcher-pog --parse-diff`). -/
def parsePogCert (s : String) : Option PogCert :=
  PogParse.lines s s.utf8ByteSize (s.utf8ByteSize + 1) 0 none none #[] #[]

/-- Equality of two parse results (for the differential tests of the parsers). -/
def samePogCert : Option PogCert → Option PogCert → Bool
  | none, none => true
  | some c, some d =>
    c.pog.V == d.pog.V && c.pog.nodes == d.pog.nodes && c.hints == d.hints && c.root == d.root
  | _, _ => false

/-! ## Checking and counting -/

/-- Supports as bitsets over the original variables, their sizes, and support-local counts,
    one entry per checked node. -/
structure PState where
  supps : Array Nat := #[]
  sizes : Array Nat := #[]
  counts : Array Nat := #[]

variable (V : Nat)

/-- Number of original variables in a bitset (as `Spec.card`). Specification of the word-wise
    `popcountFast` (`CountCatcherChecker/Popcount.lean`) that `checkNode` runs. -/
def popcount (s : Nat) : Nat := (List.range V).countP s.testBit

def litSupp (st : PState) (l : Literal Nat) : Nat :=
  if l.1 < V then 1 <<< l.1 else st.supps[l.1 - V]!

def litSize (st : PState) (l : Literal Nat) : Nat :=
  if l.1 < V then 1 else st.sizes[l.1 - V]!

def litCount (st : PState) (l : Literal Nat) : Nat :=
  let c := if l.1 < V then 1 else st.counts[l.1 - V]!
  if l.2 then c else 2 ^ litSize V st l - c

/-- Strict RUP: starting from the assignment `asg` (true literals), every hint clause must
    be unit (then its literal is added) or falsified (success). A contradictory starting
    assignment succeeds (the target clause is a tautology). -/
def rupStrict : List (Literal Nat) → List (CNF.Clause Nat) → Bool
  | asg, [] => asg.any fun l => asg.contains (l.1, !l.2)
  | asg, c :: cs =>
    if asg.any fun l => asg.contains (l.1, !l.2) then true
    else if c.any asg.contains then false  -- satisfied hint: not strict RUP
    else
      match (c.filter fun l => !asg.contains (l.1, !l.2)).eraseDups with
      | [] => true
      | [l] => rupStrict (l :: asg) cs
      | _ => false

/-- Products: check that the argument supports are pairwise disjoint (each against the union
    of the previous ones); accumulate the support, its size and the product of the counts. -/
def prodFold (st : PState) : List (Literal Nat) → Nat → Nat → Nat → Option (Nat × Nat × Nat)
  | [], acc, size, cnt => some (acc, size, cnt)
  | l :: ls, acc, size, cnt =>
    if litSupp V st l &&& acc == 0 then
      prodFold st ls (acc ||| litSupp V st l) (size + litSize V st l) (cnt * litCount V st l)
    else none

/-- The defining clause cited by an exclusion hint of node `i` (an earlier node only). -/
def hintClause (P : Pog) (i : Nat) (h : Hint) : Option (CNF.Clause Nat) :=
  if h.node < i then (P.nodes[h.node]?).bind fun m => (Pog.defClauses (V + h.node) m)[h.k]?
  else none

/-- Check node `i` against the already checked prefix and extend the state. -/
def checkNode (P : Pog) (hints : Array (List Hint)) (st : PState) (i : Nat) : Option PState :=
  match P.nodes[i]? with
  | none => none
  | some n =>
    if (Pog.Node.args n).all (·.1 < V + i) then
      match n with
      | .prod args =>
        match prodFold V st args 0 0 1 with
        | some (acc, size, cnt) =>
          some { supps := st.supps.push acc, sizes := st.sizes.push size,
                 counts := st.counts.push cnt }
        | none => none
      | .sum x y =>
        match (hints[i]?.getD []).mapM (hintClause V P i) with
        | some cls =>
          if rupStrict [x, y] cls then
            let s := litSupp V st x ||| litSupp V st y
            let size := popcountFast V s
            -- compute everything that reads `st` before pushing (keeps the arrays unshared)
            let cnt := litCount V st x * 2 ^ (size - litSize V st x) +
              litCount V st y * 2 ^ (size - litSize V st y)
            some { supps := st.supps.push s, sizes := st.sizes.push size,
                   counts := st.counts.push cnt }
          else none
        | none => none
    else none

/-- Part A: check all nodes and the root; return the count over the universe `Fin V`. -/
def checkPog (c : PogCert) : Option Nat := do
  let V := c.pog.V
  let st ← (List.range c.pog.nodes.size).foldlM (checkNode V c.pog c.hints) {}
  unless c.root.1 < V + c.pog.nodes.size do none
  pure (litCount V st c.root * 2 ^ (V - litSize V st c.root))

end CountCatcher
