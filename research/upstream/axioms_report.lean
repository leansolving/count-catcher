import Main
import ProofChecker.Checker.CheckerCore
import ProofChecker.Count.Pog
import ProofChecker.Count.PropForm

open Lean Elab Command

/-- Dependencies of a constant, following exactly the cases of Lean's `CollectAxioms.collect`. -/
def depsOf (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some (.axiomInfo v)  => v.type.getUsedConstants
  | some (.defnInfo v)   => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.thmInfo v)    => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.quotInfo _)   => #[]
  | some (.ctorInfo v)   => v.type.getUsedConstants
  | some (.recInfo v)    => v.type.getUsedConstants
  | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
  | none                 => #[]

/-- Reachable constants from `root`, with a parent pointer for each (first discovery). -/
def reach (env : Environment) (root : Name) : NameMap Name × Array Name := Id.run do
  let mut parent : NameMap Name := {}
  let mut visited : NameSet := NameSet.empty.insert root
  let mut order : Array Name := #[]
  let mut stack : Array Name := #[root]
  -- bounded loop (fuel) so the definition is not `partial`
  for _ in [0:10000000] do
    if stack.isEmpty then break
    let n := stack.back
    stack := stack.pop
    order := order.push n
    for c in depsOf env n do
      if !visited.contains c then
        visited := visited.insert c
        parent := parent.insert c n
        stack := stack.push c
  return (parent, order)

def pathTo (parent : NameMap Name) (root tgt : Name) : List Name := Id.run do
  let mut p : List Name := [tgt]
  let mut cur := tgt
  for _ in [0:100000] do
    if cur == root then break
    match parent.find? cur with
    | some q => p := q :: p; cur := q
    | none => break
  return p

elab "#sorry_report " id:ident : command => do
  let env ← getEnv
  let root := id.getId
  unless env.contains root do throwError "unknown constant {root}"
  let (parent, order) := reach env root
  let direct := order.filter fun n => n != ``sorryAx && (depsOf env n).contains ``sorryAx
  let mut msg := m!"ROOT {root}: {order.size} reachable constants; sorryAx reachable: {order.contains ``sorryAx}; constants whose own body mentions sorryAx: {direct.size}"
  for n in direct do
    msg := msg ++ m!"\n  SORRY {n}\n    path: {pathTo parent root n}"
  for t in [``Array.getElem?_setF, ``Array.getElem?_setF', ``PPA.varValue?_setVar_of_ne, ``PPA.varValue?_setVar] do
    msg := msg ++ m!"\n  reaches {t}: {order.contains t}"
  logInfo msg

-- positive controls: must show sorryAx / must not
#print axioms Array.getElem?_setF'
#print axioms Array.getElem?_setF
#print axioms Nat.add_comm

-- executable entry points
#print axioms main
#print axioms runCheckCmd
#print axioms checkProof
-- soundness carried in types (Theorem 1 of the JAIR paper is the subtype of checkFinalState)
#print axioms checkFinalState
#print axioms checkProofStep
#print axioms initial
#print axioms PreState.WF.equivalent_lits'
#print axioms PreState.WF.partitioned'
-- counting / ring evaluation theorems named in the JAIR paper, Section 10
#print axioms LeanSAT.Model.PropForm.countModels_eq_card_models
#print axioms LeanSAT.Model.PropForm.ringEval_eq_weightSum
#print axioms Pog.count_eq_countModels
#print axioms Pog.count_eq'
#print axioms Pog.ringEval_eq_ringEval
#print axioms Pog.ringEval_eq'
-- PPA lemmas
#print axioms PPA.varValue?_setVar
#print axioms PPA.varValue?_setVar_of_ne

#sorry_report main
#sorry_report checkProof
#sorry_report checkFinalState
#sorry_report LeanSAT.Model.PropForm.countModels_eq_card_models
#sorry_report LeanSAT.Model.PropForm.ringEval_eq_weightSum
#sorry_report Pog.count_eq_countModels
#sorry_report Pog.ringEval_eq_ringEval
#sorry_report Nat.add_comm
