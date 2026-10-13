import CountCatcherChecker.Pog

/-!
# CountCatcherChecker.Rev — part C: reverse direction by evaluation, executable

For every input clause `C` of `F`, the POG conditioned on `¬C` must have no model
(`Spec.RevEval`). Fast path, used for negation-free POGs (no negated edge into an internal
node, positive root; all POGs produced by cpog-gen): satisfiability propagates locally —
an input literal is satisfiable unless `¬C` falsifies it, a product iff all arguments are
(supports are disjoint), a sum iff one argument is. Every node of a negation-free POG is
satisfiable, so nodes whose support misses `vars(C)` are skipped. POGs outside the fast path
are rejected (the conditioned-count fallback is not implemented; rejection is sound).
Soundness: `CountCatcherMath.checkRev_sound` (`checkRev P.V P st F r = true → RevEval F P r`).
-/

open Std.Sat

namespace CountCatcher

variable (V : Nat)

/-- No negated edge into an internal node and a positive root. -/
def negationFree (P : Pog) (r : Literal Nat) : Bool :=
  (r.1 < V || r.2) && P.nodes.all fun n => (Pog.Node.args n).all fun l => l.1 < V || l.2

/-- Satisfiability of the POG literal `l` under the partial assignment `¬C`, given the
    satisfiability of the checked nodes in `sat`. `¬C` falsifies an input literal exactly
    when the literal occurs in `C`. -/
@[inline] def litSat (C : CNF.Clause Nat) (sat : Array Bool) (l : Literal Nat) : Bool :=
  if l.1 < V then !(C.contains l) else sat[l.1 - V]!

/-- Satisfiability of node `i` under `¬C` from the values of the earlier nodes. Nodes whose
    support misses `vars(C)` (bitset `mask`) keep the value `true`. -/
def nodeSat (P : Pog) (st : PState) (C : CNF.Clause Nat) (mask : Nat) (sat : Array Bool)
    (i : Nat) : Bool :=
  if st.supps[i]! &&& mask != 0 then
    match P.nodes[i]? with
    | some (.prod args) => args.all (litSat V C sat)
    | some (.sum x y) => litSat V C sat x || litSat V C sat y
    | none => true
  else true

/-- Satisfiability of all nodes under `¬C`, one entry per node. -/
def clauseSat (P : Pog) (st : PState) (C : CNF.Clause Nat) : Array Bool :=
  let mask := C.foldl (fun m l => m ||| (1 <<< l.1)) 0
  (List.range P.nodes.size).foldl (fun sat i => sat.push (nodeSat V P st C mask sat i)) #[]

/-- The root is unsatisfiable under `¬C` (trivially so for a tautological `C`). -/
def clauseRefuted (P : Pog) (st : PState) (C : CNF.Clause Nat) (r : Literal Nat) : Bool :=
  (C.any fun l => C.contains (l.1, !l.2)) || !(litSat V C (clauseSat V P st C) r)

/-- Part C: every input clause is refuted by the conditioned POG. -/
def checkRev (P : Pog) (st : PState) (F : CNF Nat) (r : Literal Nat) : Bool :=
  negationFree V P r && F.clauses.all fun C => clauseRefuted V P st C r

/-! ## Bit-parallel part C with kill masks

Clauses are checked in batches `cs` of at most 63, so every mask is a scalar `Nat`. Bit `j`
of a node's kill mask says that clause `cs[j]` refutes the node: an input literal is killed by
the clauses that contain it, a product by the clauses that kill one of its arguments, a sum
by the clauses that kill both. A batch passes if every non-tautological clause kills the
root. One pass over the nodes per batch instead of one per clause.
Soundness: `CountCatcherMath.checkRevKill_sound`. -/

/-- Index of a literal in the occurrence table. -/
@[inline] def litIdx (l : Literal Nat) : Nat := 2 * l.1 + (if l.2 then 1 else 0)

def isTaut (C : CNF.Clause Nat) : Bool := C.any fun l => C.contains (l.1, !l.2)

/-- Bit `j` is set iff clause `cs[j]` contains the literal with index `x`. -/
def occMask (cs : List (CNF.Clause Nat)) (x : Nat) : Nat :=
  (List.range cs.length).foldl
    (fun m j => if (cs[j]!).any (fun l => litIdx l == x) then m ||| (1 <<< j) else m) 0

/-- Bit `j` is set iff clause `cs[j]` is not a tautology. -/
def reqMask (cs : List (CNF.Clause Nat)) : Nat :=
  (List.range cs.length).foldl (fun m j => if !isTaut (cs[j]!) then m ||| (1 <<< j) else m) 0

/-- Kill mask of a POG literal: the occurrence mask of an input literal, the computed mask of
    a node. -/
@[inline] def litKill (occ k : Array Nat) (l : Literal Nat) : Nat :=
  if l.1 < V then occ[litIdx l]! else k[l.1 - V]!

def nodeKill (P : Pog) (occ k : Array Nat) (i : Nat) : Nat :=
  match P.nodes[i]? with
  | some (.prod args) => args.foldl (fun m l => m ||| litKill V occ k l) 0
  | some (.sum x y) => litKill V occ k x &&& litKill V occ k y
  | none => 0

/-- Kill masks of all nodes, one entry per node. -/
def killMasks (P : Pog) (occ : Array Nat) : Array Nat :=
  (List.range P.nodes.size).foldl (fun k i => k.push (nodeKill V P occ k i)) #[]

/-- Every non-tautological clause of the batch kills the root. -/
def batchRefuted (P : Pog) (cs : List (CNF.Clause Nat)) (r : Literal Nat) : Bool :=
  let occ := Array.ofFn (n := 2 * V) fun x => occMask cs x.1
  let req := reqMask cs
  litKill V occ (killMasks V P occ) r &&& req == req

/-- Consecutive pieces of `w` elements (`fuel` bounds the number of pieces). -/
def chunks {α : Type} (w : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | fuel + 1, l => if l.isEmpty then [] else l.take w :: chunks w fuel (l.drop w)

/-- Part C, bit-parallel: the POG is negation-free and every batch of 63 clauses is refuted. -/
def checkRevKill (P : Pog) (F : CNF Nat) (r : Literal Nat) : Bool :=
  negationFree V P r &&
    (chunks 63 F.clauses.size F.clauses.toList).all fun cs => batchRefuted V P cs r

end CountCatcher
