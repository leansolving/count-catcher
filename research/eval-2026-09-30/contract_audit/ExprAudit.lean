-- Expression-level closure (definition values, implemented_by targets, csimp replacements) from McCert.checkAll.
-- Over-approximates (proof terms inside definitions are traversed); the IR-level closure (IrAudit.lean) is exact.
import McCert.Check
import LRATCatcher
import Lean
open Lean Meta Elab Command

/-- Transitive closure of constants whose *code* can run when the roots are evaluated
    natively: definition values (not types, not theorems), `implemented_by` targets,
    `@[csimp]` replacements. Extern constants are leaves (their C code runs). -/
def reach (env : Environment) (roots : List Name) : Array Name × Std.HashSet Name := Id.run do
  let csimp := (Lean.Compiler.CSimp.ext.getState env).map
  let mut seen : Std.HashSet Name := {}
  let mut work := roots
  let mut order : Array Name := #[]
  let mut fuel := 1000000
  while fuel > 0 do
    fuel := fuel - 1
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      order := order.push n
      if let some t := Lean.Compiler.getImplementedBy? env n then work := t :: work
      if let some t := csimp.find? n then work := t.toDeclName :: work
      if isExtern env n then continue
      match env.find? n with
      | some (.defnInfo d) => work := d.value.getUsedConstants.toList ++ work
      | some (.opaqueInfo d) => work := d.value.getUsedConstants.toList ++ work
      | some (.ctorInfo _) | some (.recInfo _) | some (.inductInfo _) | some (.quotInfo _)
      | some (.axiomInfo _) | some (.thmInfo _) | none => pure ()
  return (order, seen)

elab "#audit " ids:ident* : command => do
  let env ← getEnv
  let roots := ids.toList.map (·.getId)
  let (order, _) := reach env roots
  let csimp := (Lean.Compiler.CSimp.ext.getState env).map
  let mut lines : Array String := #[]
  let mut ndef := 0
  for n in order do
    let some ci := env.find? n | continue
    if ci matches .defnInfo _ then ndef := ndef + 1
    let mut tags : Array String := #[]
    if isExtern env n then
      let sym := match getExternAttrData? env n with
        | some d => ", ".intercalate (d.entries.map fun (e : ExternEntry) => match e with
            | .adhoc _ => "adhoc" | .inline _ p => s!"inline {p}" | .standard _ f => f | .opaque => "opaque")
        | none => "?"
      tags := tags.push s!"extern {sym}"
    if let some t := Lean.Compiler.getImplementedBy? env n then tags := tags.push s!"implemented_by {t}"
    if let some t := csimp.find? n then tags := tags.push s!"csimp→{t.toDeclName}"
    if let some e := getExportNameFor? env n then tags := tags.push s!"export {e}"
    if ci.isUnsafe then tags := tags.push "unsafe"
    if ci.isPartial then tags := tags.push "partial"
    if ci matches .opaqueInfo _ then tags := tags.push "opaque"
    if ci matches .axiomInfo _ then tags := tags.push "AXIOM"
    if n.toString.endsWith "panic" || n == ``panicCore || n == ``panicWithPosWithDecl || n == ``panicWithPos then tags := tags.push "panic"
    if n == ``dbgTrace || n == ``dbgTraceIfShared || n == ``unsafeCast || n == ``ptrAddrUnsafe || n == ``unsafeIO || n == ``unsafeBaseIO || n == ``unsafeEIO then tags := tags.push "FLAG"
    if !tags.isEmpty then lines := lines.push s!"{n} :: {", ".intercalate tags.toList}"
  logInfo m!"roots {roots}: {order.size} constants reached, {ndef} definitions\n{"\n".intercalate (lines.qsort (· < ·)).toList}"

#audit McCert.checkAll
