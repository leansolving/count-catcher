import CountCatcherChecker.Check

/-!
# CountCatcherChecker.FwdSel — part B on a selection of its initial clauses (H3), executable

Part B refutes `fwdCnf F P r`: the clauses of `F`, the defining clauses of `P` in declaration
order, the unit `¬r`. Only 21 to 40 percent of them are ever cited by an LRAT hint
(2026-10-01), but all are built and converted by Lean core's LRAT front end before the first
proof step, where the clause database peaks. An untrusted mask selects the clauses that part B
loads: byte `i` of the mask string is clause `i` (0-based) of `fwdCnf F P r`; `'0'` drops it,
any other byte and every position past the end keep it, so the empty mask selects all of
`fwdCnf F P r`. Every selected clause is a clause of `fwdCnf F P r`, so a refutation of the
selection refutes the whole (`CountCatcherMath.fwdCnfOf_unsat_of_sel`); a wrong mask only makes the
LRAT check fail. The core front end drops tautological clauses and numbers the rest by position,
so the LRAT proof cites a kept clause by its position among the kept non-tautological ones.

`fwdCnfSel` walks the positions in order and builds only the kept clauses (a dropped defining
clause is never allocated); the mask byte is read in constant time (`String.getUTF8Byte`).
-/

open Std.Sat

namespace CountCatcher

/-- The mask keeps position `i`: its byte `i` is not `'0'`, or `i` is past its end. -/
@[inline] def maskKeep (mask : String) (i : Nat) : Bool :=
  if h : i < mask.utf8ByteSize then mask.getUTF8Byte ⟨i⟩ h != 48 else true

/-- One position: the next position and the clauses kept so far, with `c` pushed if the mask
    keeps position `p.1`. -/
@[inline] def keepStep (mask : String) (p : Nat × Array (CNF.Clause Nat)) (c : CNF.Clause Nat) :
    Nat × Array (CNF.Clause Nat) :=
  (p.1 + 1, if maskKeep mask p.1 then p.2.push c else p.2)

/-- `keepStep` for the binary defining clause `[¬u, l]` of a product, built only if kept. -/
@[inline] def keepArg (mask : String) (u : Nat) (p : Nat × Array (CNF.Clause Nat))
    (l : Literal Nat) : Nat × Array (CNF.Clause Nat) :=
  (p.1 + 1, if maskKeep mask p.1 then p.2.push [(u, false), l] else p.2)

/-- The defining clauses of node `n` with variable `u`, in the order of `Pog.defClauses u n`,
    at positions from `p.1`. -/
def keepDefs (mask : String) (u : Nat) (n : Node) (p : Nat × Array (CNF.Clause Nat)) :
    Nat × Array (CNF.Clause Nat) :=
  match n with
  | .prod args =>
    let p := (p.1 + 1,
      if maskKeep mask p.1 then p.2.push ((u, true) :: args.map fun (v, b) => (v, !b)) else p.2)
    args.foldl (keepArg mask u) p
  | .sum x y =>
    let p := (p.1 + 1, if maskKeep mask p.1 then p.2.push [(u, false), x, y] else p.2)
    let p := (p.1 + 1, if maskKeep mask p.1 then p.2.push [(u, true), (x.1, !x.2)] else p.2)
    (p.1 + 1, if maskKeep mask p.1 then p.2.push [(u, true), (y.1, !y.2)] else p.2)

/-- The defining clauses of `k` nodes from node `i` on. -/
def keepNodes (mask : String) (P : Pog) :
    Nat → Nat → Nat × Array (CNF.Clause Nat) → Nat × Array (CNF.Clause Nat)
  | 0, _, p => p
  | k + 1, i, p =>
    match P.nodes[i]? with
    | some n => keepNodes mask P k (i + 1) (keepDefs mask (P.V + i) n p)
    | none => keepNodes mask P k (i + 1) p

/-- The clauses of `fwdCnf F P r` that the mask keeps, in order. -/
def fwdCnfSel (F : CNF Nat) (P : Pog) (r : Literal Nat) (mask : String) : CNF Nat :=
  let p := F.clauses.foldl (keepStep mask) (0, #[])
  let p := keepNodes mask P P.nodes.size 0 p
  ⟨if maskKeep mask p.1 then p.2.push [(r.1, !r.2)] else p.2⟩

/-- `fwdCnfOf` on the clauses that the mask `keepStr` keeps. A streamed refutation of it gives
    `(fwdCnfOf F pogStr).Unsat` (`CountCatcherMath.fwdCnfOf_unsat_of_sel`). -/
def fwdCnfOfSel (F : CNF Nat) (pogStr keepStr : String) : CNF Nat :=
  match parsePogCert pogStr with
  | some c => fwdCnfSel F c.pog c.root keepStr
  | none => ⟨#[]⟩

end CountCatcher
