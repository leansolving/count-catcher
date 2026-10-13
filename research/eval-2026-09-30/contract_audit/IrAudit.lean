-- IR-level trust audit (contract_audit.md, part 2). Run from lean/: lake env lean ../research/eval-2026-09-30/contract_audit/IrAudit.lean
-- Closure over the compiled IR (collectUsedDecls) from the roots; extern declarations are leaves;
-- tags: extern C symbol, unsafe, partial, opaque, implemented_by, export. Output: ir_audit.txt.
import McCert.Check
import LRATCatcher
import Lean
open Lean Elab Command IR

def usedBy (env : Environment) (n : Name) : Array Name :=
  match findEnvDecl env n with
  | some d => (collectUsedDecls env [d]).filter (· != n)
  | none => #[]

def closure (env : Environment) (roots : List Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut work := roots
  let mut order : Array Name := #[]
  let mut fuel := 200000
  while fuel > 0 do
    fuel := fuel - 1
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      order := order.push n
      work := (usedBy env n).toList ++ work
  return order

def tag (env : Environment) (n : Name) : String := Id.run do
  let mut tags : Array String := #[]
  if let some (.extern _ _ _ ext) := findEnvDecl env n then
    tags := tags.push ("extern " ++ ", ".intercalate (ext.entries.map fun (e : ExternEntry) => match e with
          | .adhoc _ => "adhoc" | .inline _ p => s!"inline {p}" | .standard _ f => f | .opaque => "opaque"))
  let base := if n.isStr && n.getString! == "_boxed" then n.getPrefix else n
  if let some ci := env.find? base then
    if ci.isUnsafe then tags := tags.push "unsafe"
    if ci.isPartial then tags := tags.push "partial"
    if ci matches .opaqueInfo _ then tags := tags.push "opaque"
  if let some t := Lean.Compiler.getImplementedBy? env base then tags := tags.push s!"implemented_by {t}"
  if let some e := getExportNameFor? env base then tags := tags.push s!"export {e}"
  return ", ".intercalate tags.toList

elab "#irAudit2 " ids:ident* : command => do
  let env ← getEnv
  let roots := ids.toList.map (·.getId)
  let cl := closure env roots
  let clSet : NameSet := cl.foldl (·.insert ·) {}
  -- callers (inside the closure) of panicCore, and of the unsafe/opaque/extern-less nodes
  let mut panicCallers : Array Name := #[]
  let mut own : Array String := #[]
  let mut flagged : Array String := #[]
  let interesting := [`McCert, `LRATCatcher, `Std.Tactic.BVDecide, `Std.Sat]
  for n in cl do
    let u := usedBy env n
    let pk := u.filter fun m => m == ``panicCore || m.toString.startsWith "panic" || m == ``Array.get!Internal ||
      m == ``Array.get!InternalBorrowed || m == ``Array.set! || m.toString.endsWith "get!" || m.toString.startsWith "outOfBounds"
    if !pk.isEmpty then panicCallers := panicCallers.push (n.appendAfter s!"  <- calls {pk.toList}")
    if interesting.any (·.isPrefixOf n) then own := own.push s!"{n} {tag env n}"
    let t := tag env n
    if !t.isEmpty && !(t.startsWith "extern") then flagged := flagged.push s!"{n} :: {t}"
  let ext := cl.filter fun n => match findEnvDecl env n with | some (.extern ..) => true | _ => false
  logInfo m!"ROOTS {roots}: {cl.size} IR functions, {ext.size} externs\nPANIC-CALLERS {panicCallers.qsort (·.toString < ·.toString)}\nNON-EXTERN-FLAGGED\n{"\n".intercalate (flagged.qsort (· < ·)).toList}\nEXTERNS {(ext.qsort (·.toString < ·.toString))}\nOWN ({own.size})\n{"\n".intercalate (own.qsort (· < ·)).toList}"

#irAudit2 McCert.checkAll
#irAudit2 McCert.checkAllAC McCert.fwdCnfOf
#irAudit2 LRATCatcher.checkStreamCnf LRATCatcher.certFeedImpl LRATCatcher.streamReset
