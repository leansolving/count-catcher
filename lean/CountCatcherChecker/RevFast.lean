import CountCatcherChecker.Rev

/-!
# CountCatcherChecker.RevFast — part C with one reused occurrence table, executable

`checkRevKill` builds the occurrence table of each 63-clause batch as
`Array.ofFn (n := 2 * V) fun x => occMask cs x`, and `occMask` scans the whole batch for each
of the 2V literal indices: O(V · L) per batch with L literal occurrences, O(V · |F|) overall.

Here one table of size 2V is allocated once and threaded through the batches. A batch sets
bit `j` in the entries of the literals of clause `j` (O(L)); after an accepted batch exactly
these entries are reset to 0 (O(L)), so the next batch starts from the zero table again. The
table is updated in place: it is unshared when `addBatchOcc` and `clearBatchOcc` run
(`batchRefutedWith` only reads it, and the reset is in the branch after its result).
Kill masks, the 63-clause batching and the verdict are those of `checkRevKill`;
`CountCatcherMath.checkRevKillFast_eq` proves the two functions equal, and
`CountCatcherMath.checkRevKillFast_sound` gives `RevEval`.
-/

open Std.Sat

namespace CountCatcher

variable (V : Nat)

/-- Set bit `j` in the table entries of the literals of `c` (entries out of range are left
    alone, as in `Array.modify`). -/
def addClauseOcc (j : Nat) (t : Array Nat) (c : CNF.Clause Nat) : Array Nat :=
  c.foldl (fun t l => t.modify (litIdx l) (· ||| (1 <<< j))) t

/-- Add the occurrences of the batch `cs` to `t`: bit `j` for clause `cs[j]`. -/
def addBatchOcc (t : Array Nat) (cs : List (CNF.Clause Nat)) : Array Nat :=
  (List.range cs.length).foldl (fun t j => addClauseOcc j t (cs[j]!)) t

/-- Reset the table entries of the literals of `c` to 0. -/
def clearClauseOcc (t : Array Nat) (c : CNF.Clause Nat) : Array Nat :=
  c.foldl (fun t l => t.set! (litIdx l) 0) t

/-- Reset the table entries of the literals of the batch `cs` to 0. -/
def clearBatchOcc (t : Array Nat) (cs : List (CNF.Clause Nat)) : Array Nat :=
  cs.foldl clearClauseOcc t

/-- `batchRefuted` with the occurrence table given: every non-tautological clause of the batch
    kills the root. -/
def batchRefutedWith (P : Pog) (occ : Array Nat) (cs : List (CNF.Clause Nat))
    (r : Literal Nat) : Bool :=
  let req := reqMask cs
  litKill V occ (killMasks V P occ) r &&& req == req

/-- Every batch is refuted; `t` is the zero table on entry to each batch. -/
def batchesRefuted (P : Pog) (r : Literal Nat) :
    Array Nat → List (List (CNF.Clause Nat)) → Bool
  | _, [] => true
  | t, cs :: css =>
    let occ := addBatchOcc t cs
    if batchRefutedWith V P occ cs r then batchesRefuted P r (clearBatchOcc occ cs) css
    else false

/-- Part C, bit-parallel, one occurrence table for all batches. Equal to `checkRevKill`
    (`CountCatcherMath.checkRevKillFast_eq`). -/
def checkRevKillFast (P : Pog) (F : CNF Nat) (r : Literal Nat) : Bool :=
  negationFree V P r &&
    batchesRefuted V P r (Array.replicate (2 * V) 0) (chunks 63 F.clauses.size F.clauses.toList)

end CountCatcher
