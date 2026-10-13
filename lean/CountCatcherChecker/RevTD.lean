import CountCatcherChecker.Rev

/-!
# CountCatcherChecker.RevTD — part C by top-down short-circuit evaluation, unverified

Baseline for the comparison of part C methods in the paper; the checker does not use it.
For every non-tautological input clause `C` the root must be killed by `¬C` (as in
`checkRev` and `checkRevKillFast`): an input literal is killed iff `C` contains it, a product
iff one argument is killed, a sum iff both are. Here the root is evaluated top-down per clause
by a depth-first search with an explicit stack: a product stops at its first killed argument
(input literals first), a sum at its first argument that is not killed. Shared nodes are
evaluated once per clause (memo). The literal table, the memo and the argument positions are
arrays reused across clauses; entries carry the clause's stamp, so nothing is cleared.

With `useSig` every node carries a 63-bit support signature (bit `v % 63` for each variable `v`
of its support). A node whose signature misses the clause's signature has no variable of `C`;
in a negation-free POG it is then satisfiable under `¬C`, hence not killed, and is skipped.
-/

open Std.Sat

namespace CountCatcher

/-- Flat node table. The arguments of node `i` are `code[start[i]]`, …, `code[start[i+1] - 1]`:
    `2 * litIdx l` for an input literal `l`, `2 * j + 1` for node `j` (positive edge). Input
    literals come first. `sig` is empty unless signatures were requested. -/
structure FlatPog where
  start : Array Nat
  code : Array Nat
  isSum : Array Bool
  sig : Array Nat

variable (V : Nat)

/-- Flatten a negation-free POG; `none` if an argument is neither an input literal nor a
    positive edge to an earlier node. -/
def flattenPog (useSig : Bool) (P : Pog) : Option FlatPog := Id.run do
  let mut start : Array Nat := Array.mkEmpty (P.nodes.size + 1)
  let mut code : Array Nat := #[]
  let mut isSum : Array Bool := Array.mkEmpty P.nodes.size
  let mut sig : Array Nat := #[]
  let mut i := 0
  start := start.push 0
  for n in P.nodes do
    let args := Pog.Node.args n
    let mut s := 0
    for l in args do
      if l.1 < V then
        code := code.push (2 * litIdx l)
        if useSig then s := s ||| (1 <<< (l.1 % 63))
    for l in args do
      if l.1 ≥ V then
        let j := l.1 - V
        if j ≥ i || !l.2 then return none
        code := code.push (2 * j + 1)
        if useSig then s := s ||| sig[j]!
    start := start.push code.size
    isSum := isSum.push (match n with | .sum .. => true | .prod .. => false)
    if useSig then sig := sig.push s
    i := i + 1
  return some ⟨start, code, isSum, sig⟩

/-- Arrays threaded through the clauses, the evaluated-node count of the current clause and
    the verdict. -/
structure TDState where
  occ : Array Nat
  memo : Array Nat
  pos : Array Nat
  stack : Array Nat
  visits : Nat
  killed : Bool
  deriving Inhabited

/-- Depth-first evaluation under `¬C` (stamp `s`, signature `csig`). The top of the stack is
    the node in progress, `pos` its current argument. `pend < 2` is the value (1 = killed) of
    that argument, `pend = 2` means it is not evaluated yet. A finished node stores
    `2 * s + value` in `memo`. -/
partial def tdLoop (fp : FlatPog) (useSig : Bool) (csig s : Nat) (occ memo pos stack : Array Nat)
    (visits pend : Nat) : TDState :=
  let i := stack.back!
  let p := pos[i]!
  if pend < 2 then
    -- a product finishes on a killed argument, a sum on an argument that is not killed
    if (pend == 1) != fp.isSum[i]! then
      let memo := memo.set! i (2 * s + pend)
      let stack := stack.pop
      if stack.isEmpty then ⟨occ, memo, pos, stack, visits, pend == 1⟩
      else tdLoop fp useSig csig s occ memo pos stack visits pend
    else tdLoop fp useSig csig s occ memo (pos.set! i (p + 1)) stack visits 2
  else if p == fp.start[i + 1]! then
    -- no short circuit: a product is not killed, a sum is
    let b := if fp.isSum[i]! then 1 else 0
    let memo := memo.set! i (2 * s + b)
    let stack := stack.pop
    if stack.isEmpty then ⟨occ, memo, pos, stack, visits, b == 1⟩
    else tdLoop fp useSig csig s occ memo pos stack visits b
  else
    let c := fp.code[p]!
    if c % 2 == 0 then
      tdLoop fp useSig csig s occ memo pos stack visits (if occ[c / 2]! == s then 1 else 0)
    else
      let j := c / 2
      let mj := memo[j]!
      if mj / 2 == s then tdLoop fp useSig csig s occ memo pos stack visits (mj % 2)
      else if useSig && fp.sig[j]! &&& csig == 0 then
        tdLoop fp useSig csig s occ memo pos stack visits 0
      else
        tdLoop fp useSig csig s occ memo (pos.set! j fp.start[j]!) (stack.push j) (visits + 1) 2

/-- Evaluate the root literal `r` under `¬C` with stamp `s`. -/
def clauseTD (fp : FlatPog) (useSig : Bool) (r : Literal Nat) (C : CNF.Clause Nat) (s : Nat)
    (occ memo pos stack : Array Nat) : TDState :=
  if isTaut C then ⟨occ, memo, pos, stack, 0, true⟩ else
  let occ := C.foldl (fun o l => o.setIfInBounds (litIdx l) s) occ
  if r.1 < V then ⟨occ, memo, pos, stack, 0, occ[litIdx r]! == s⟩ else
  let j := r.1 - V
  if j ≥ fp.isSum.size then ⟨occ, memo, pos, stack, 0, false⟩ else
  let csig := if useSig then C.foldl (fun m l => m ||| (1 <<< (l.1 % 63))) 0 else 0
  if useSig && fp.sig[j]! &&& csig == 0 then ⟨occ, memo, pos, stack, 0, false⟩ else
  tdLoop fp useSig csig s occ memo (pos.set! j fp.start[j]!) (stack.push j) 1 2

/-- Part C, top-down: the POG is negation-free and every non-tautological clause kills the
    root. Also returns the evaluated nodes summed over the clauses and their maximum per
    clause (up to the first clause that fails). -/
def checkRevTD (useSig : Bool) (P : Pog) (F : CNF Nat) (r : Literal Nat) : Bool × Nat × Nat :=
  if !negationFree V P r then (false, 0, 0) else
  match flattenPog V useSig P with
  | none => (false, 0, 0)
  | some fp => Id.run do
    let N := P.nodes.size
    let mut st : TDState :=
      ⟨Array.replicate (2 * V) 0, Array.replicate N 0, Array.replicate N 0, #[], 0, true⟩
    let mut total := 0
    let mut mx := 0
    let mut s := 0
    for C in F.clauses do
      s := s + 1
      st := clauseTD V fp useSig r C s st.occ st.memo st.pos st.stack
      total := total + st.visits
      mx := max mx st.visits
      if !st.killed then return (false, total, mx)
    return (true, total, mx)

end CountCatcher
