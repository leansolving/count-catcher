import CountCatcherChecker.RevFast
import CountCatcherChecker.Fwd
import LRATCatcher.Reflect

/-!
# CountCatcherChecker.Check — the complete checker, executable

`checkAll V F pogStr lratStr N` runs part A (POG validity and count `N`), part B (the LRAT
refutation of `F ++ defs ++ [¬r]` through lrat-catcher) and part C (bit-parallel evaluation).
Soundness: `CountCatcherMath.checkAll_sound`.
-/

open Std.Sat

namespace CountCatcher

/-- Decidable form of `CnfWF`. -/
def cnfWFb (V : Nat) (F : CNF Nat) : Bool := F.clauses.all fun c => c.all fun l => l.1 < V

/-- Parts A and C on a parsed certificate; part A's fold runs once and its state feeds the
    root check, the count and part C. -/
def checkAC (F : CNF Nat) (c : PogCert) (N : Nat) : Bool :=
  match (List.range c.pog.nodes.size).foldlM (checkNode c.pog.V c.pog c.hints) {} with
  | some st =>
    decide (c.root.1 < c.pog.V + c.pog.nodes.size) &&
    litCount c.pog.V st c.root * 2 ^ (c.pog.V - litSize c.pog.V st c.root) == N &&
    checkRevKillFast c.pog.V c.pog F c.root
  | none => false

/-- The complete check: `F` lives in `Fin V`, the POG file parses with universe `V`, parts A
    and C accept with count `N`, and the LRAT proof refutes `F ++ defs ++ [¬r]`. -/
def checkAll (V : Nat) (F : CNF Nat) (pogStr lratStr : String) (N : Nat) : Bool :=
  cnfWFb V F &&
  match parsePogCert pogStr with
  | some c => c.pog.V == V && checkAC F c N &&
      LRATCatcher.checkLratCnf (fwdCnf F c.pog c.root) lratStr
  | none => false

/-- Part B's CNF `F ++ defs ++ [¬r]` for a POG file (empty if the file does not parse). A
    streamed LRAT refutation (`lrat_stream_cnf`) proves it unsatisfiable. -/
def fwdCnfOf (F : CNF Nat) (pogStr : String) : CNF Nat :=
  match parsePogCert pogStr with
  | some c => fwdCnf F c.pog c.root
  | none => ⟨#[]⟩

/-- `checkAll` without part B, for certificates too large to embed: part B is then the
    separate theorem `(fwdCnfOf F pogStr).Unsat`. Soundness: `CountCatcherMath.checkAllAC_sound`. -/
def checkAllAC (V : Nat) (F : CNF Nat) (pogStr : String) (N : Nat) : Bool :=
  cnfWFb V F &&
  match parsePogCert pogStr with
  | some c => c.pog.V == V && checkAC F c N
  | none => false

end CountCatcher
