import CountCatcherMath.Check
import CountCatcherMath.Symmetry
import CountCatcherMath.Family
import CountCatcherMath.Diag
import CountCatcherMath.FwdSel
import LRATCatcher.StreamOracle

/-!
# CountCatcherMath.Command — `count_models` and `#export_cnf`

User commands on top of the verified checker, modelled on lrat-catcher's `lrat_reflect_cnf` and
`lrat_stream_cnf`. The count `N` is never typed by the user: the command runs part A of the
checker at elaboration time (it computes the count), then proves the theorem with the verified
check (`checkAll_sound`, `checkAllAC_sound`, or a family's `card_of_check`) and native
evaluation (`Lean.Meta.nativeEqTrue`, the kernel-facing core of `native_decide`).

Forms (`thm` is the theorem name; paths are relative to the directory of the source file,
as for `include_str`, or absolute):

    count_models thm (F) "fwd.pog" "fwd.lrat"            -- F : CNF Nat, a Lean term
    count_models thm (F) (V := k) "fwd.pog" "fwd.lrat"   -- universe Fin k given explicitly
    count_models thm "f.cnf" "fwd.pog" "fwd.lrat"        -- DIMACS file
    count_models thm via (L args) "fwd.pog" "fwd.lrat"   -- family lemma L = …card_of_check

and the count-0 forms with one LRAT refutation of `F` instead of the two certificate files:

    count_models thm (F) "refutation.lrat"               -- also with (V := k), "f.cnf", via

Statements:
* `(F)`: `Fintype.card {a : Fin V → Bool // F.eval (ext a) = true} = N`, where `V` is `k` if
  given, else `F.numLiterals` (largest variable index plus one, the header that
  `Std.Sat.CNF.dimacs` writes);
* `"f.cnf"`: the same with `F = LRATCatcher.parseDimacs «file contents»` and `V` the header's
  variable count (the file is validated as by `lrat_reflect`);
* `via (L args)`: the conclusion of `L args`, with `V` and `F` read off `L`'s hypothesis
  `checkAll V F pogStr lratStr N = true`. Streamed mode uses `LAC` (name + `AC`), count 0 uses
  the lemma with `check` replaced by `unsat` (`Domino.card_of_unsat`, `Family.card_of_unsat`).

Mode: `count_models +embed …` embeds the LRAT file (one native evaluation of `checkAll`),
`count_models +stream …` streams it (part B by lrat-catcher's stream reader as the separate
theorem `thm.fwd`, parts A and C embedded, POG text in `def thm.pog`). Without a flag the
LRAT file size decides: embedded up to `countCatcher.embedMaxBytes` (default 64 MiB), else streamed;
binary LRAT is always streamed.

Keep file: `count_models thm … "fwd.pog" "fwd.lrat" (keep := "fwd.keep")` (before a count hint)
streams part B on the initial clauses that the mask selects (`CountCatcherChecker/FwdSel.lean`), with the
LRAT numbered for them: `def thm.keep` holds the mask, `thm.fwd : (fwdCnfOfSel F thm.pog
thm.keep).Unsat`, and `fwdCnfOf_unsat_of_sel thm.fwd` enters the main theorem. A keep file
implies streaming; with `+embed`, or in the count-0 form, it is an error.

Failure: the theorem is not declared, and the error names the part that failed (certificate
parse, universe, part A with node and condition, part B with the LRAT step, part C with the
first input clause not implied and a witness). The reports come from `CountCatcherMath.Diag`,
unverified code that runs only after the verified check has returned `false`.

`#export_cnf (F) "out.cnf"` (also with `(V := k)`) and `#export_cnf via (L args) "out.cnf"` write
the DIMACS file that the counter must see: header `p cnf V m` with the theorem's `V`, clauses
in the order of `F` (so certificate clause IDs match `F`).
-/

open Lean Elab Command Term Meta
open Std.Sat

namespace CountCatcher.Command

register_option countCatcher.embedMaxBytes : Nat := {
  defValue := 67108864
  descr := "count_models: an LRAT file of at most this many bytes is embedded (parts A, B, C in \
    one native evaluation); a larger one is streamed (part B by lrat-catcher's stream reader)"
}

register_option countCatcher.diagMaxBytes : Nat := {
  defValue := 1073741824
  descr := "count_models: after a rejected streamed LRAT file larger than this, the \
    step-by-step part B report is skipped (it reads the whole file)"
}

/-! ## Syntax -/

/-- `+embed` or `+stream`. -/
syntax countMode := "+" noWs ident
/-- The universe `Fin k` of a `CNF Nat` term. -/
syntax universeArg := "(" &"V" " := " term ")"
/-- A count hint (from the counter): skips the elaboration-time part-A pass; the verified
    check still verifies it. -/
syntax countHint := "(" &"count" " := " num ")"
/-- A keep file (mask of part B's initial clauses, `CountCatcher.fwdCnfOfSel`); streamed mode only. -/
syntax keepFileArg := atomic("(" &"keep") " := " str ")"

syntax (name := countModelsCnf) (docComment)? "count_models" (countMode)? ident
  " (" term ")" (universeArg)? str (str)? (keepFileArg)? (countHint)? : command
syntax (name := countModelsVia) (docComment)? "count_models" (countMode)? ident
  &"via" " (" term ")" str (str)? (keepFileArg)? (countHint)? : command
syntax (name := countModelsDimacs) (docComment)? "count_models" (countMode)? ident
  str str (str)? (keepFileArg)? (countHint)? : command

syntax (name := exportCnf) "#export_cnf" " (" term ")" (universeArg)? str : command
syntax (name := exportCnfVia) "#export_cnf" &"via" " (" term ")" str : command

/-! ## Helpers -/

def cnfType : Expr := mkApp (Lean.mkConst ``Std.Sat.CNF [Level.zero]) (Lean.mkConst ``Nat)

unsafe def evalCnfUnsafe (e : Expr) : MetaM (CNF Nat) := Meta.evalExpr (CNF Nat) cnfType e
@[implemented_by evalCnfUnsafe] opaque evalCnf (e : Expr) : MetaM (CNF Nat)

unsafe def evalNatUnsafe (e : Expr) : MetaM Nat := Meta.evalExpr Nat (Lean.mkConst ``Nat) e
@[implemented_by evalNatUnsafe] opaque evalNat (e : Expr) : MetaM Nat

/-- DIMACS text with the header `p cnf V m`, clauses in the order of `F`. -/
def dimacs (V : Nat) (F : CNF Nat) : String := Id.run do
  let mut s := s!"p cnf {V} {F.clauses.size}\n"
  for c in F.clauses do
    for l in c do
      s := s ++ Diag.litStr l ++ " "
    s := s ++ "0\n"
  return s

/-- A path relative to the directory of the current source file (as `include_str`). -/
def resolvePath (p : String) : CoreM System.FilePath := do
  let fp := System.FilePath.mk p
  if fp.isAbsolute then return fp
  match (System.FilePath.mk (← getFileName)).parent with
  | some d => return d / fp
  | none => return fp

def readText (p : System.FilePath) : CoreM String := do
  try IO.FS.readFile p
  catch e => throwError "count_models: cannot read '{p}' as text: {e.toMessageData}"

def fileSize (p : System.FilePath) : CoreM Nat := do
  try return (← p.metadata).byteSize.toNat
  catch e => throwError "count_models: cannot read '{p}': {e.toMessageData}"

/-- Binary LRAT starts with `a` or `d` (lrat-catcher's rule); text LRAT with a clause ID. -/
def isBinaryLrat (p : System.FilePath) : CoreM Bool := do
  try
    let h ← IO.FS.Handle.mk p .read
    let b ← h.read 1
    return b.size == 1 && (b[0]! == 'a'.toUInt8 || b[0]! == 'd'.toUInt8)
  catch _ => return false

def mb (n : Nat) : String :=
  let t := n * 10 / 1048576
  s!"{t / 10}.{t % 10} MiB"

/-- The `V` of the `p cnf V M` header of a DIMACS text (exactly one header line). -/
def dimacsHeaderVars (path : String) (s : String) : CoreM Nat := do
  let hdrs := (s.splitOn "\n").filter fun l => l.trimAscii.toString.startsWith "p"
  match hdrs with
  | [h] =>
    match (h.splitOn " ").filter (· ≠ "") with
    | ["p", "cnf", v, _] =>
      match v.trimAscii.toString.toNat? with
      | some v => return v
      | none => throwError "{path}: bad header '{h}'"
    | _ => throwError "{path}: bad header '{h}' (expected 'p cnf V M')"
  | _ => throwError "{path}: expected exactly one 'p cnf V M' header line"

/-- The universe line `V n` among the first lines of a POG text (cheap, no full parse). -/
def pogHeaderV? (s : String) : Option Nat :=
  ((s.take 4096).toString.splitOn "\n").findSome? fun l =>
    match (l.splitOn " ").filter (· ≠ "") with
    | ["V", n] => n.toNat?
    | _ => none

/-- Split `L a b …` into the head identifier and the arguments. -/
def splitApp (stx : Term) : TermElabM (Syntax × Array Syntax) := do
  let (fn, args) :=
    if stx.raw.isOfKind ``Lean.Parser.Term.app then (stx.raw[0], stx.raw[1].getArgs)
    else (stx.raw, #[])
  unless fn.isIdent do
    throwErrorAt stx "via: expected a family lemma name (…card_of_check), possibly applied \
      to arguments; give implicit family parameters as named arguments, e.g. \
      `Domino.card_of_check (R := 8) (C := 8)`"
  return (fn, args)

/-- Which lemma of a family to use. -/
inductive Variant where
  | check | checkAC | unsat

/-- The lemma of the given variant for the family lemma `c` (a name ending in `check`). -/
def variantName (c : Name) : Variant → CoreM Name
  | .check => pure c
  | .checkAC => do
    let c' := c.appendAfter "AC"
    unless (← getEnv).contains c' do
      throwError "count_models: '{c}' has no streamed variant '{c'}'; use +embed"
    pure c'
  | .unsat => do
    let s := c.getString!
    unless s.endsWith "check" do
      throwError "count_models: count 0 needs the family lemma …check, got '{c}'"
    let c' := c.getPrefix.str ((s.dropEnd 5).toString ++ "unsat")
    unless (← getEnv).contains c' do
      throwError "count_models: '{c}' has no count-0 variant '{c'}' (for a family given by an \
        equivalence e, use via (Family.card_of_check e))"
    pure c'

/-- Elaborate the variant `v` of the family lemma application `stx`, keeping metavariables for
    the arguments that the command fills in. -/
def elabVariant (stx : Term) (v : Variant) : TermElabM Expr := do
  let (fn, args) ← splitApp stx
  let c ← realizeGlobalConstNoOverload fn
  let c' ← variantName c v
  let stx' := Syntax.mkApp (mkCIdentFrom fn c') (args.map (⟨·⟩))
  let e ← withoutErrToSorry do
    let e ← elabTerm stx' none
    synthesizeSyntheticMVarsNoPostponing
    pure e
  instantiateMVars e

/-- The first `k` (non-dependent) hypotheses of the type of `e`. -/
def hyps (e : Expr) (k : Nat) : MetaM (Array Expr) := do
  let mut ty ← instantiateMVars (← inferType e)
  let mut out := #[]
  for _ in [0:k] do
    match ← whnfR ty with
    | .forallE _ d b _ =>
      if b.hasLooseBVars then throwError "count_models: unexpected dependent hypothesis in{indentExpr ty}"
      out := out.push d
      ty := b
    | _ => throwError "count_models: expected {k} hypotheses in{indentExpr ty}"
  return out

/-- `f a₁ … aₙ = true` with `f` the constant `c`: the arguments. -/
def boolCall? (d : Expr) (c : Name) (n : Nat) : Option (Array Expr) :=
  match d.eq? with
  | some (_, lhs, rhs) =>
    if rhs.isConstOf ``Bool.true && lhs.isAppOfArity c n then some lhs.getAppArgs else none
  | none => none

def assign (m v : Expr) (what : String) : MetaM Unit := do
  unless ← isDefEq m v do
    throwError "count_models: cannot set the {what} of the family lemma to{indentExpr v}"

/-- Close all metavariables of `e` or fail with a hint. -/
def closed (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if e.hasMVar then
    throwError "count_models: could not determine all arguments of{indentExpr e}\n\
      (give the family parameters as named arguments)"
  return e

/-- Evaluate `e = true` natively (as `native_decide`), naming the auxiliary axiom after
    `declName`; on `false` fail with the reports of `onFail`. -/
def native (declName : Name) (ref : Syntax) (e : Expr) (onFail : TermElabM (List String)) :
    TermElabM (Expr × Nat) := do
  let t0 ← IO.monoMsNow
  let r ← withDeclNameForAuxNaming declName <|
    nativeEqTrue `native_decide e (axiomDeclRange? := ref)
  let t1 ← IO.monoMsNow
  match r with
  | .success prf => return (prf, t1 - t0)
  | .notTrue =>
    let reps ← onFail
    let body := if reps.isEmpty then
        "  (the unverified diagnostics found no fault; please report this certificate)"
      else "\n".intercalate (reps.map ("  " ++ ·))
    throwError "count_models: the verified check rejected the certificate for '{declName}':\n\
      {body}\n'{declName}' was not declared (the reports come from unverified diagnostics)."

/-- No heartbeat limit: the native evaluations run inside the command's elaboration and
    allocate as much as the certificate needs (as lrat-catcher's stream commands, which set
    `maxHeartbeats 0`); under the default limit a 444 MB LRAT file failed with a `whnf`
    timeout after the check. -/
def unlimited (x : TermElabM α) : TermElabM α :=
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) x

/-- Run `x` with lrat-catcher's stream reader pointed at `path`. -/
def withStream (path : System.FilePath) (x : TermElabM α) : TermElabM α := do
  LRATCatcher.streamReset (some path.toString)
  try x finally LRATCatcher.streamReset none

def addThm (name : Name) (value : Expr) : TermElabM Unit := do
  let value ← closed value
  let type ← instantiateMVars (← inferType value)
  addDecl <| .thmDecl { name, levelParams := [], type, value }

/-! ## The subject of a theorem -/

/-- Where `V` and `F` come from. -/
inductive Src where
  /-- A `CNF Nat` term, optionally with its universe. -/
  | cnf (f : Term) (v? : Option Term)
  /-- A DIMACS file: its contents and header variable count. -/
  | dimacs (contents : String) (V : Nat)
  /-- A family lemma application. -/
  | via (l : Term)

structure Subject where
  V : Expr
  F : Expr
  /-- The value of `V`, when known without evaluation. -/
  Vval? : Option Nat := none
  /-- The value of `F`, when known without evaluation. -/
  Fval? : Option (CNF Nat) := none
  /-- The family lemma with metavariables for the certificate arguments. -/
  lemma? : Option Expr := none

def Subject.Vval (s : Subject) : MetaM Nat := do
  match s.Vval? with
  | some v => return v
  | none => evalNat s.V

def Subject.Fval (s : Subject) : MetaM (CNF Nat) := do
  match s.Fval? with
  | some f => return f
  | none => evalCnf s.F

def elabCnf (f : Term) (v? : Option Term) : TermElabM Subject := do
  let F ← withoutErrToSorry do
    let F ← elabTermEnsuringType f cnfType
    synthesizeSyntheticMVarsNoPostponing
    pure F
  let F ← closed F
  match v? with
  | some v =>
    let V ← elabTermEnsuringType v (Lean.mkConst ``Nat)
    synthesizeSyntheticMVarsNoPostponing
    return { V := ← closed V, F }
  | none =>
    let Fv ← evalCnf F
    let k := Fv.numLiterals
    return { V := mkNatLit k, F, Vval? := some k, Fval? := some Fv }

/-- The subject for variant `v`: for a family, `V` and `F` from the lemma's hypothesis. -/
def subject (src : Src) (v : Variant) : TermElabM Subject := do
  match src with
  | .cnf f v? => elabCnf f v?
  | .dimacs s k =>
    return { V := mkNatLit k, F := mkApp (Lean.mkConst ``LRATCatcher.parseDimacs) (mkStrLit s),
             Vval? := some k, Fval? := some (LRATCatcher.parseDimacs s) }
  | .via l =>
    let e ← elabVariant l v
    match v with
    | .check =>
      let hs ← hyps e 1
      let some a := boolCall? hs[0]! ``CountCatcher.checkAll 5
        | throwError "count_models: the hypothesis of the family lemma is not \
            `checkAll V F pogStr lratStr N = true`:{indentExpr hs[0]!}"
      return { V := ← closed a[0]!, F := ← closed a[1]!, lemma? := some e }
    | .checkAC =>
      let hs ← hyps e 2
      let some a := boolCall? hs[0]! ``CountCatcher.checkAllAC 4
        | throwError "count_models: the hypothesis of the streamed family lemma is not \
            `checkAllAC V F pogStr N = true`:{indentExpr hs[0]!}"
      return { V := ← closed a[0]!, F := ← closed a[1]!, lemma? := some e }
    | .unsat =>
      let hs ← hyps e 1
      unless hs[0]!.isAppOfArity ``Std.Sat.CNF.Unsat 2 do
        throwError "count_models: the hypothesis of the count-0 family lemma is not \
          `F.Unsat`:{indentExpr hs[0]!}"
      let F ← closed hs[0]!.appArg!
      return { V := mkNatLit 0, F, lemma? := some e }

/-! ## The routes -/

structure Job where
  declName : Name
  ref : Syntax
  stream : Bool
  lratPath : System.FilePath
  /-- The contents of the keep file (streamed mode only), read before any declaration. -/
  keepStr? : Option String := none

/-- Theorem `N` models, from a POG and an LRAT file. Returns the proof and a summary line. -/
def countRoute (j : Job) (src : Src) (pogStr : String) (hint? : Option Nat) :
    TermElabM (Expr × String) := do
  let s ← subject src (if j.stream then .checkAC else .check)
  -- with a hint, no full parse: only the universe line is read here
  let pogV? ← match hint? with
    | some _ => pure (pogHeaderV? pogStr)
    | none => match parsePogCert pogStr with
      | some c => pure (some c.pog.V)
      | none => throwError "count_models: the POG file does not parse: {Diag.pogParseError pogStr}"
  let Vn ← s.Vval
  if let some pv := pogV? then
    unless pv == Vn do
      let hint := match src with
        | .cnf _ none => s!". For the universe Fin {pv}, write (V := {pv}) after the formula"
        | _ => ""
      throwError "count_models: the certificate is for {pv} variables (the 'V' line of the \
        POG file, from the header of the counted DIMACS file), the theorem's universe is \
        Fin {Vn}{hint}"
  let tA ← IO.monoMsNow
  let N ← match hint? with
    | some n => pure n
    | none =>
      let some c := parsePogCert pogStr | throwError "count_models: the POG file does not parse"
      let some N := checkPog c
        | throwError "count_models: part A (POG validity) rejects the certificate: \
            {(Diag.partA c (Diag.nodeLines pogStr)).getD "no fault found"}"
      pure N
  let NE := mkNatLit N
  let msA := (← IO.monoMsNow) - tA
  let countSrc := if hint?.isSome then "count from the hint" else s!"count by part A {msA} ms"
  if !j.stream then
    let lratStr ← readText j.lratPath
    let pogE := mkStrLit pogStr
    let lratE := mkStrLit lratStr
    let chk := mkAppN (Lean.mkConst ``CountCatcher.checkAll) #[s.V, s.F, pogE, lratE, NE]
    let (prf, ms) ← native j.declName j.ref chk do
      return Diag.report Vn (← s.Fval) pogStr (some lratStr.toUTF8) N hint?.isSome
    let value ← match s.lemma? with
      | none => pure <| mkAppN (Lean.mkConst ``CountCatcher.checkAll_sound) #[s.V, s.F, pogE, lratE, NE, prf]
      | some e => do
        let a := (boolCall? (← hyps e 1)[0]! ``CountCatcher.checkAll 5).get!
        assign a[2]! pogE "POG string"; assign a[3]! lratE "LRAT string"; assign a[4]! NE "count"
        pure (mkApp e prf)
    return (value, s!"{N} models over Fin {Vn}, embedded; {countSrc}, \
      verified check (parts A, B, C) {ms} ms")
  else
    -- POG text as a compiled definition (read by part B's CNF and by parts A and C)
    let pogName := j.declName ++ `pog
    let strTy := Lean.mkConst ``String
    let pogDecl : DefinitionVal :=
      { name := pogName, levelParams := [], type := strTy, value := mkStrLit pogStr,
        hints := .abbrev, safety := .safe }
    addAndCompile (.defnDecl pogDecl)
    let pogC := Lean.mkConst pogName
    -- the keep file's mask as a compiled definition
    let keep? ← j.keepStr?.mapM fun keepStr => do
      let keepName := j.declName ++ `keep
      addAndCompile <| .defnDecl
        { name := keepName, levelParams := [], type := strTy, value := mkStrLit keepStr,
          hints := .abbrev, safety := .safe }
      pure (keepStr, Lean.mkConst keepName)
    -- part B: lrat-catcher's streamed check of F ++ defs ++ [¬r] (or of the selected clauses)
    let fwdName := j.declName ++ `fwd
    let feed := Lean.mkConst (j.declName ++ `fwd_feed)
    let fuel := Lean.mkConst ``LRATCatcher.streamFuel
    let fwdF := match keep? with
      | none => mkApp2 (Lean.mkConst ``CountCatcher.fwdCnfOf) s.F pogC
      | some (_, keepC) => mkApp3 (Lean.mkConst ``CountCatcher.fwdCnfOfSel) s.F pogC keepC
    let chkB := mkApp3 (Lean.mkConst ``LRATCatcher.checkStreamCnf) fwdF feed fuel
    let (prfB, msB) ← withStream j.lratPath <|
        native fwdName j.ref chkB do
          let sz ← fileSize j.lratPath
          if sz > countCatcher.diagMaxBytes.get (← getOptions) then
            return [s!"part B (streamed LRAT refutation): rejected; the file ({mb sz}) is larger \
              than countCatcher.diagMaxBytes, no step-by-step report"]
          let some c := parsePogCert pogStr
            | return [s!"certificate: {Diag.pogParseError pogStr}"]
          let bytes ← IO.FS.readBinFile j.lratPath
          -- the CNF that the LRAT file numbers: with a keep file, the selected clauses
          let F ← s.Fval
          let (cnf, what) := match keep? with
            | none => (fwdCnf F c.pog c.root, "F, the defining clauses and ¬root")
            | some (keepStr, _) => (fwdCnfSel F c.pog c.root keepStr,
                "the clauses of F, the defining clauses and ¬root that the keep file selects")
          match Diag.partB cnf bytes true with
          | some m => return [s!"part B (streamed LRAT refutation of {what}): {m}"]
          | none => return []
    addThm fwdName (mkApp4 (Lean.mkConst ``LRATCatcher.checkStreamCnf_sound) fwdF feed fuel prfB)
    let fwdThm := match keep? with
      | none => Lean.mkConst fwdName
      | some (_, keepC) => mkAppN (Lean.mkConst ``CountCatcher.fwdCnfOf_unsat_of_sel)
          #[s.F, pogC, keepC, Lean.mkConst fwdName]
    -- parts A and C
    let chkAC := mkAppN (Lean.mkConst ``CountCatcher.checkAllAC) #[s.V, s.F, pogC, NE]
    let (prfAC, msAC) ← native j.declName j.ref chkAC do
      return Diag.report Vn (← s.Fval) pogStr none N hint?.isSome
    let value ← match s.lemma? with
      | none => pure <| mkAppN (Lean.mkConst ``CountCatcher.checkAllAC_sound) #[s.V, s.F, pogC, NE, prfAC, fwdThm]
      | some e => do
        let a := (boolCall? (← hyps e 1)[0]! ``CountCatcher.checkAllAC 4).get!
        assign a[2]! pogC "POG string"; assign a[3]! NE "count"
        pure (mkApp2 e prfAC fwdThm)
    let keepNote := if keep?.isSome then " (keep file)" else ""
    return (value, s!"{N} models over Fin {Vn}, streamed; {countSrc}, \
      verified check part B{keepNote} {msB} ms, parts A and C {msAC} ms")

/-- Theorem 0 models, from an LRAT refutation of `F`. -/
def unsatRoute (j : Job) (src : Src) : TermElabM (Expr × String) := do
  let s ← subject src .unsat
  let onFail (normalize : Bool) : TermElabM (List String) := do
    let sz ← fileSize j.lratPath
    if sz > countCatcher.diagMaxBytes.get (← getOptions) then
      return [s!"LRAT refutation of F: rejected; the file ({mb sz}) is larger than \
        countCatcher.diagMaxBytes, no step-by-step report"]
    let bytes ← IO.FS.readBinFile j.lratPath
    match Diag.partB (← s.Fval) bytes normalize with
    | some m => return [s!"LRAT refutation of F: {m}"]
    | none => return []
  let (hU, ms) ← if !j.stream then do
      let lratE := mkStrLit (← readText j.lratPath)
      let chk := mkApp2 (Lean.mkConst ``LRATCatcher.checkLratCnf) s.F lratE
      let (prf, ms) ← native j.declName j.ref chk (onFail false)
      pure (mkApp3 (Lean.mkConst ``LRATCatcher.checkLratCnf_sound) s.F lratE prf, ms)
    else do
      let uName := j.declName ++ `unsat
      let feed := Lean.mkConst (j.declName ++ `unsat_feed)
      let fuel := Lean.mkConst ``LRATCatcher.streamFuel
      let chk := mkApp3 (Lean.mkConst ``LRATCatcher.checkStreamCnf) s.F feed fuel
      let (prf, ms) ← withStream j.lratPath <| native uName j.ref chk (onFail true)
      addThm uName (mkApp4 (Lean.mkConst ``LRATCatcher.checkStreamCnf_sound) s.F feed fuel prf)
      pure (Lean.mkConst uName, ms)
  let value := match s.lemma? with
    | none => mkApp3 (Lean.mkConst ``CountCatcher.card_eq_zero_of_unsat) s.V s.F hU
    | some e => mkApp e hU
  let vs := match src with
    | .via _ => ""
    | _ => match s.Vval? with | some v => s!" over Fin {v}" | none => ""
  return (value, s!"0 models{vs} (LRAT refutation, {if j.stream then "streamed" else "embedded"}, \
    {ms} ms)")

/-! ## Elaborators -/

def modeFlag (m? : Option Syntax) : CommandElabM (Option Bool) := do
  match m? with
  | none => return none
  | some m =>
    match m[1].getId with
    | `embed => return some false
    | `stream => return some true
    | _ => throwErrorAt m "count_models: expected +embed or +stream"

def runCount (stx : Syntax) (doc? : Option (TSyntax ``Lean.Parser.Command.docComment))
    (m? : Option Syntax) (n : Ident) (src : Src) (files : Array StrLit) (keep? : Option Syntax)
    (hint? : Option Syntax) : CommandElabM Unit := do
  let declName := (← getCurrNamespace) ++ n.getId
  if (← getEnv).contains declName then
    throwErrorAt n "'{declName}' has already been declared"
  let unsat := files.size == 1
  let hint? : Option Nat := hint?.map fun h => (TSyntax.getNat ⟨h[3]⟩ : Nat)
  if unsat && hint?.isSome then
    throwErrorAt stx "count_models: the count-0 form (one LRAT refutation) takes no count hint"
  let lratPath ← liftCoreM <| resolvePath files.back!.getString
  let keepPath? ← keep?.mapM fun k => liftCoreM <| resolvePath (TSyntax.getString ⟨k[3]⟩)
  if unsat && keepPath?.isSome then
    throwErrorAt stx "count_models: the count-0 form (one LRAT refutation of F) takes no keep file"
  let flag ← modeFlag m?
  let binary ← liftCoreM <| isBinaryLrat lratPath
  let stream ← match flag with
    | some b => pure b
    | none => pure (binary || keepPath?.isSome ||
        decide ((← liftCoreM (fileSize lratPath)) > countCatcher.embedMaxBytes.get (← getOptions)))
  if keepPath?.isSome && !stream then
    throwErrorAt stx "count_models: a keep file selects part B's initial clauses for the \
      streamed check; it cannot be used with +embed (use +stream or no flag)"
  if binary && !stream then
    throwErrorAt stx "count_models: '{lratPath}' is binary LRAT, which cannot be embedded as a \
      string; use +stream (or no flag)"
  let pogStr ← if unsat then pure "" else liftCoreM <| readText (← liftCoreM <| resolvePath files[0]!.getString)
  -- read now, so that a missing keep file fails before `thm.fwd_feed` and `thm.pog` exist
  let keepStr? ← keepPath?.mapM fun p => liftCoreM (readText p)
  if stream then
    let feed := mkIdent (`_root_ ++ declName ++ (if unsat then `unsat_feed else `fwd_feed))
    elabCommand (← `(command|
      @[implemented_by LRATCatcher.certFeedImpl]
      opaque $feed : Nat → Option (Array Std.Tactic.BVDecide.LRAT.IntAction)))
  let j : Job := { declName, ref := stx, stream, lratPath, keepStr? }
  liftTermElabM <| unlimited <| withDeclNameForAuxNaming declName do
    let (value, summary) ← if unsat then unsatRoute j src else countRoute j src pogStr hint?
    addThm declName value
    addDeclarationRangesFromSyntax declName stx n
    addTermInfo' (isBinder := true) n (Lean.mkConst declName)
    addDocString' declName mkNullNode doc?
    logInfo m!"count_models {declName}: {summary}"

@[command_elab countModelsCnf] def elabCountModelsCnf : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) := stx[0].getOptional?.map (⟨·⟩)
  let v? : Option Term := stx[7].getOptional?.map fun u => ⟨u[3]⟩
  let files := #[stx[8]] ++ stx[9].getOptional?.toArray
  runCount stx doc? stx[2].getOptional? ⟨stx[3]⟩ (.cnf ⟨stx[5]⟩ v?) (files.map (⟨·⟩))
    stx[10].getOptional? stx[11].getOptional?

@[command_elab countModelsVia] def elabCountModelsVia : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) := stx[0].getOptional?.map (⟨·⟩)
  let files := #[stx[8]] ++ stx[9].getOptional?.toArray
  runCount stx doc? stx[2].getOptional? ⟨stx[3]⟩ (.via ⟨stx[6]⟩) (files.map (⟨·⟩))
    stx[10].getOptional? stx[11].getOptional?

@[command_elab countModelsDimacs] def elabCountModelsDimacs : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) := stx[0].getOptional?.map (⟨·⟩)
  let cnfFile : StrLit := ⟨stx[4]⟩
  let path ← liftCoreM <| resolvePath cnfFile.getString
  let contents ← liftCoreM <| readText path
  LRATCatcher.validateDimacs path.toString contents
  let V ← liftCoreM <| dimacsHeaderVars path.toString contents
  let files := #[stx[5]] ++ stx[6].getOptional?.toArray
  runCount stx doc? stx[2].getOptional? ⟨stx[3]⟩ (.dimacs contents V) (files.map (⟨·⟩))
    stx[7].getOptional? stx[8].getOptional?

def runExport (src : Src) (out : StrLit) : CommandElabM Unit := do
  let path ← liftCoreM <| resolvePath out.getString
  liftTermElabM <| unlimited do
    -- for a family, the hypothesis of the embedded lemma fixes V and F
    let s ← subject src .check
    let F ← s.Fval
    let V ← s.Vval
    if let some (k, l) := (List.range F.clauses.size).findSome? (fun k =>
        (F.clauses[k]!.find? (fun l => !(l.1 < V))).map (k, ·)) then
      throwError "#export_cnf: clause {k + 1} uses variable {l.1 + 1}, outside the universe Fin {V}"
    IO.FS.writeFile path (dimacs V F)
    logInfo m!"#export_cnf: wrote {path} (p cnf {V} {F.clauses.size})"

@[command_elab exportCnf] def elabExportCnf : CommandElab := fun stx => do
  let v? : Option Term := stx[4].getOptional?.map fun u => ⟨u[3]⟩
  runExport (.cnf ⟨stx[2]⟩ v?) ⟨stx[5]⟩

@[command_elab exportCnfVia] def elabExportCnfVia : CommandElab := fun stx => do
  runExport (.via ⟨stx[3]⟩) ⟨stx[5]⟩

end CountCatcher.Command
