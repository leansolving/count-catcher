import Std.Sat.CNF

/-!
# CountCatcherChecker.Spec — semantic specification of the counting checker

Mathlib-free. Conventions follow `Std.Sat`: variables are 0-indexed naturals (DIMACS
variable `k` is `k - 1`), a literal `(v, b)` is satisfied by `a` iff `a v == b`.

* The universe is `Fin V`, fixed by the encoder; variables that occur in no clause count.
* A POG over `V` original variables declares extension variables `V, V+1, …` in order,
  node `i` defining variable `V + i`. Arguments are literals over earlier variables.
* Counts are support-local: `count v` counts the satisfying
  assignments of the original-variable support of `v`.

The contract theorems are stated and proved in `CountCatcherMath`.
-/

open Std.Sat

namespace CountCatcher

/-! ## Universe, assignments, model count -/

/-- Assignment of the universe `Fin V`, extended by `false` outside it. -/
def ext {V : Nat} (a : Fin V → Bool) : Nat → Bool :=
  fun i => if h : i < V then a ⟨i, h⟩ else false

/-- The assignment of `Fin V` given by the bits of `k`. -/
def ofBits (V k : Nat) : Fin V → Bool := fun i => k.testBit i

/-- All variables of `F` lie in the universe `Fin V`. -/
def CnfWF (V : Nat) (F : CNF Nat) : Prop := ∀ c ∈ F.clauses, ∀ l ∈ c, l.1 < V

/-- Number of models of `F` over the universe `Fin V` (specification only: `2 ^ V`
    evaluations). The family layer proves `Fintype.card {a // F.eval (ext a)} = modelCount`. -/
def modelCount (V : Nat) (F : CNF Nat) : Nat :=
  (List.range (2 ^ V)).countP fun k => F.eval (ext (ofBits V k))

/-- Satisfaction of a literal. -/
@[inline] def litTrue (b : Nat → Bool) (l : Literal Nat) : Bool := b l.1 == l.2

/-- Number of variables below `V` in a support given as a membership test. -/
def card (V : Nat) (S : Nat → Bool) : Nat := (List.range V).countP S

/-! ## POGs -/

/-- A node defines the extension variable `V + i` where `i` is its index. -/
inductive Node where
  | prod (args : List (Literal Nat))
  | sum (x y : Literal Nat)
  deriving Repr, DecidableEq

structure Pog where
  V : Nat
  nodes : Array Node
  deriving Repr

namespace Pog

variable (P : Pog)

/-- Number of variables (original plus extension). -/
def numVars : Nat := P.V + P.nodes.size

/-- The node defining variable `v`, if `v` is an extension variable. -/
def node? (v : Nat) : Option Node := if v < P.V then none else P.nodes[v - P.V]?

/-- Value of variable `v` under the input assignment `a` (only `a` below `V` matters).
    Arguments that do not refer to earlier variables make the node false; `WF` excludes
    them. -/
def evalVar (a : Nat → Bool) (v : Nat) : Bool :=
  if v < P.V then a v
  else match P.node? v with
    | none => false
    | some (.prod args) =>
        args.all fun l => if _ : l.1 < v then evalVar a l.1 == l.2 else false
    | some (.sum x y) =>
        (if _ : x.1 < v then evalVar a x.1 == x.2 else false) ||
        (if _ : y.1 < v then evalVar a y.1 == y.2 else false)
termination_by v

def evalLit (a : Nat → Bool) (l : Literal Nat) : Bool := P.evalVar a l.1 == l.2

/-- Original-variable support of variable `v`, as a membership test (polarity-blind). -/
def supp (v : Nat) (x : Nat) : Bool :=
  if v < P.V then x == v
  else match P.node? v with
    | none => false
    | some (.prod args) => args.any fun l => if _ : l.1 < v then supp l.1 x else false
    | some (.sum y z) =>
        (if _ : y.1 < v then supp y.1 x else false) || (if _ : z.1 < v then supp z.1 x else false)
termination_by v

/-- Size of the support of `v`. -/
def suppSize (v : Nat) : Nat := card P.V (P.supp v)

/-- Support-local count of variable `v`. -/
def countVar (v : Nat) : Nat :=
  if v < P.V then 1
  else match P.node? v with
    | none => 0
    | some (.prod args) =>
        args.foldl (init := 1) fun acc l =>
          if _ : l.1 < v then
            acc * (if l.2 then countVar l.1 else 2 ^ P.suppSize l.1 - countVar l.1)
          else 0
    | some (.sum x y) =>
        let cx := if _ : x.1 < v then
          (if x.2 then countVar x.1 else 2 ^ P.suppSize x.1 - countVar x.1) else 0
        let cy := if _ : y.1 < v then
          (if y.2 then countVar y.1 else 2 ^ P.suppSize y.1 - countVar y.1) else 0
        cx * 2 ^ (P.suppSize v - P.suppSize x.1) + cy * 2 ^ (P.suppSize v - P.suppSize y.1)
termination_by v

/-- Support-local count of a literal. -/
def countLit (l : Literal Nat) : Nat :=
  if l.2 then P.countVar l.1 else 2 ^ P.suppSize l.1 - P.countVar l.1

/-- Count of literal `r` over the whole universe `Fin V`. -/
def countRoot (r : Literal Nat) : Nat := P.countLit r * 2 ^ (P.V - P.suppSize r.1)

/-- Tseitin defining clauses of node `i` (CPOG Table 2 order). -/
def defClauses (u : Nat) : Node → List (CNF.Clause Nat)
  | .prod args => ((u, true) :: args.map fun (v, b) => (v, !b)) :: args.map fun l => [(u, false), l]
  | .sum x y => [[(u, false), x, y], [(u, true), (x.1, !x.2)], [(u, true), (y.1, !y.2)]]

/-- All defining clauses, in declaration order. -/
def defs : List (CNF.Clause Nat) :=
  (List.range P.nodes.size).flatMap fun i =>
    match P.nodes[i]? with
    | some n => defClauses (P.V + i) n
    | none => []

/-- Arguments of a node. -/
def Node.args : Node → List (Literal Nat)
  | .prod args => args
  | .sum x y => [x, y]

/-- Structural and semantic well-formedness of a POG (acceptance conditions C2 to C4).
    `sum_excl` is semantic; the checker establishes it by RUP over defining clauses only. -/
structure WF : Prop where
  args_lt : ∀ i (h : i < P.nodes.size), ∀ l ∈ Node.args P.nodes[i], l.1 < P.V + i
  prod_disjoint : ∀ i (h : i < P.nodes.size) args, P.nodes[i] = .prod args →
    args.Pairwise fun l₁ l₂ => ∀ x, ¬ (P.supp l₁.1 x = true ∧ P.supp l₂.1 x = true)
  sum_excl : ∀ i (h : i < P.nodes.size) x y, P.nodes[i] = .sum x y →
    ∀ a : Nat → Bool, ¬ (P.evalLit a x = true ∧ P.evalLit a y = true)

/-- Extension of an input assignment by POG evaluation. -/
def extend (a : Nat → Bool) : Nat → Bool := fun v => if v < P.numVars then P.evalVar a v else false

end Pog

/-! ## Contract

The theorems about these definitions are proved in `CountCatcherMath` (which may use
Mathlib). With the reverse direction checked by evaluation, the checker establishes:

* part A: `P.WF` and the root in range;
* part B: `Fwd F P r`, from lrat-catcher's `Unsat` of `F ++ defs P ++ [¬r]`;
* part C: `RevEval F P r`;

and `CountCatcherMath` turns these into `card {a : Fin V → Bool // F.eval (ext a)} = P.countRoot r`. -/

def clausesTrue (b : Nat → Bool) (cs : List (CNF.Clause Nat)) : Prop :=
  ∀ c ∈ cs, CNF.Clause.eval b c = true

/-- Forward direction: `F` and the defining clauses imply the root. -/
def Fwd (F : CNF Nat) (P : Pog) (r : Literal Nat) : Prop :=
  ∀ b : Nat → Bool, F.eval b = true → clausesTrue b P.defs → litTrue b r = true

/-- Reverse direction, evaluation form: every input assignment on which the POG root
    evaluates to true satisfies `F`. -/
def RevEval (F : CNF Nat) (P : Pog) (r : Literal Nat) : Prop :=
  ∀ a : Nat → Bool, P.evalLit a r = true → F.eval a = true

end CountCatcher
