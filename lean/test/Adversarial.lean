import CountCatcher

/-! The adversarial suite (`adversarial/`, expected verdicts in `adversarial/expected.txt`)
    through the verified checker. The CPOG certificates were translated once by
    `tools/bin/cpog2lrat` (2026-10-01; `scripts/cpog2lrat.py` writes the same files) into
    `data/adv_*.pog` and `data/adv_*.lrat`. For each case: the verdicts of the three parts
    (part A's count, part B, part C's `negationFree` fragment test, part C), `checkAll` at the
    true count and at the wrong count a checker without the targeted condition would accept,
    and the `count_models` theorem or failure report.

    a5, a5b (C4) and a9 (C2) do not translate: the translator rejects them ("C4: exclusion hint
    1 of node 2 is not a defining clause", "C2: extension variable 2 is not V+1+0"), since the
    POG format names a hint by an earlier node and one of its defining clauses, and node `i`
    always defines variable `V + i`. Their Lean-format counterparts are written by hand at the
    end, with the negation-free fragment cases c02 and c03 of the contract audit
    (`research/eval-2026-09-30/contract_audit.md`). -/

open CountCatcher

/-- A formula (DIMACS) with a POG file and an LRAT file. -/
structure AdvCase where
  cnf : String
  pog : String
  lrat : String

/-- Part A's count (`none`: rejected), part B, `negationFree`, part C (`checkRevKillFast`). -/
def AdvCase.parts (k : AdvCase) : Option (Option Nat × Bool × Bool × Bool) := do
  let F := LRATCatcher.parseDimacs k.cnf
  let c ← parsePogCert k.pog
  pure (checkPog c, LRATCatcher.checkLratCnf (fwdCnf F c.pog c.root) k.lrat,
    negationFree c.pog.V c.pog c.root, checkRevKillFast c.pog.V c.pog F c.root)

/-- The complete check with universe `Fin V` and count `N`. -/
def AdvCase.accepts (k : AdvCase) (V N : Nat) : Bool :=
  checkAll V (LRATCatcher.parseDimacs k.cnf) k.pog k.lrat N

/-! ## Honest certificates: accepted with the true count -/

-- h1_unused (C1, C8): `F = x1` over `{x1, x2}`, root `x1` wrapped in a product: 2 models.
def h1 : AdvCase := ⟨include_str "adversarial/h1_unused.cnf",
  include_str "data/adv_h1_unused.pog", include_str "data/adv_h1_unused.lrat"⟩
#guard h1.parts == some (some 2, true, true, true)
#guard h1.accepts 2 2 && !h1.accepts 2 1

-- h2_or (C8, sum with unequal supports): `F = x1 ∨ x2`, root `x1 ∨ (¬x1 ∧ x2)`: 3 models.
def h2 : AdvCase := ⟨include_str "adversarial/h2_or.cnf",
  include_str "data/adv_h2_or.pog", include_str "data/adv_h2_or.lrat"⟩
#guard h2.parts == some (some 3, true, true, true)
#guard h2.accepts 2 3 && !h2.accepts 2 4

-- h3_nand (C8, negative input literal, unused variable): `F = ¬x1 ∨ ¬x2` over 3 variables:
-- 6 models.
def h3 : AdvCase := ⟨include_str "adversarial/h3_nand.cnf",
  include_str "data/adv_h3_nand.pog", include_str "data/adv_h3_nand.lrat"⟩
#guard h3.parts == some (some 6, true, true, true)
#guard h3.accepts 3 6 && !h3.accepts 3 3

-- a7_delete_def (C6, policy): the CPOG deletes a defining clause; the Lean checker ignores
-- all deletions and accepts with the true count 1.
def a7 : AdvCase := ⟨include_str "adversarial/a7_delete_def.cnf",
  include_str "data/adv_a7_delete_def.pog", include_str "data/adv_a7_delete_def.lrat"⟩
#guard a7.parts == some (some 1, true, true, true)
#guard a7.accepts 1 1

#guard_msgs (drop info) in
count_models adv_h1 "adversarial/h1_unused.cnf" "data/adv_h1_unused.pog" "data/adv_h1_unused.lrat"
#guard_msgs (drop info) in
count_models adv_h2 "adversarial/h2_or.cnf" "data/adv_h2_or.pog" "data/adv_h2_or.lrat"
#guard_msgs (drop info) in
count_models adv_h3 "adversarial/h3_nand.cnf" "data/adv_h3_nand.pog" "data/adv_h3_nand.lrat"
#guard_msgs (drop info) in
count_models adv_a7 "adversarial/a7_delete_def.cnf" "data/adv_a7_delete_def.pog" "data/adv_a7_delete_def.lrat"

example : Fintype.card {a : Fin 2 → Bool //
    (LRATCatcher.parseDimacs (include_str "adversarial/h1_unused.cnf")).eval (ext a) = true} = 2 :=
  adv_h1
example : Fintype.card {a : Fin 2 → Bool //
    (LRATCatcher.parseDimacs (include_str "adversarial/h2_or.cnf")).eval (ext a) = true} = 3 :=
  adv_h2
example : Fintype.card {a : Fin 3 → Bool //
    (LRATCatcher.parseDimacs (include_str "adversarial/h3_nand.cnf")).eval (ext a) = true} = 6 :=
  adv_h3
example : Fintype.card {a : Fin 1 → Bool //
    (LRATCatcher.parseDimacs (include_str "adversarial/a7_delete_def.cnf")).eval (ext a) = true} = 1 :=
  adv_a7

/-! ## Malicious certificates: rejected, at the true and at the wrong count -/

-- a4_prod_overlap (C3): `F = x1 ∧ ¬x1` (no model), root `x1 ∧ ¬x1` with overlapping supports
-- (wrong count 1). Parts B and C accept; part A rejects.
def a4 : AdvCase := ⟨include_str "adversarial/a4_prod_overlap.cnf",
  include_str "data/adv_a4_prod_overlap.pog", include_str "data/adv_a4_prod_overlap.lrat"⟩
#guard a4.parts == some (none, true, true, true)
#guard !a4.accepts 1 1 && !a4.accepts 1 0

-- a14_prod_self (C3, policy): a product of a node with itself (the wrong count 1 happens to be
-- the true count). Part A rejects.
def a14 : AdvCase := ⟨include_str "adversarial/a14_prod_self.cnf",
  include_str "data/adv_a14_prod_self.pog", include_str "data/adv_a14_prod_self.lrat"⟩
#guard a14.parts == some (none, true, true, true)
#guard !a14.accepts 1 1

-- a6_self_delete (C6 mask), a8_leftover_derived (C7), a10_reused_id (C5): `F = x1`, and each
-- exploit makes the root the constant true (wrong count 2, true count 1). The Lean checker
-- ignores deletions and clause IDs, so all three translate to the same certificate: parts A
-- and B accept with count 2, part C finds the input clause `x1` not implied.
def a6 : AdvCase := ⟨include_str "adversarial/a6_self_delete.cnf",
  include_str "data/adv_a6_self_delete.pog", include_str "data/adv_a6_self_delete.lrat"⟩
def a8 : AdvCase := ⟨include_str "adversarial/a8_leftover_derived.cnf",
  include_str "data/adv_a8_leftover_derived.pog", include_str "data/adv_a8_leftover_derived.lrat"⟩
def a10 : AdvCase := ⟨include_str "adversarial/a10_reused_id.cnf",
  include_str "data/adv_a10_reused_id.pog", include_str "data/adv_a10_reused_id.lrat"⟩
#guard [a6, a8, a10].all fun k =>
  k.parts == some (some 2, true, true, false) && !k.accepts 1 2 && !k.accepts 1 1

/--
error: count_models: part A (POG validity) rejects the certificate: node 0 (variable 2, POG line 3): product arguments 1 and -1 share the input variable 1 (condition C3: supports must be disjoint, polarity ignored)
-/
#guard_msgs in
count_models adv_a4 "adversarial/a4_prod_overlap.cnf" "data/adv_a4_prod_overlap.pog" "data/adv_a4_prod_overlap.lrat"

/--
error: count_models: part A (POG validity) rejects the certificate: node 1 (variable 3, POG line 4): product arguments 2 and 2 share the input variable 1 (condition C3: supports must be disjoint, polarity ignored)
-/
#guard_msgs in
count_models adv_a14 "adversarial/a14_prod_self.cnf" "data/adv_a14_prod_self.pog" "data/adv_a14_prod_self.lrat"

/--
error: count_models: the verified check rejected the certificate for 'adv_a6':
  part C (every input clause implied by the POG): input clause 1 (1 0) is not implied by the POG: the assignment -1 satisfies the POG root 2 and falsifies the clause (the circuit has models that are not models of the formula)
'adv_a6' was not declared (the reports come from unverified diagnostics).
-/
#guard_msgs in
count_models adv_a6 "adversarial/a6_self_delete.cnf" "data/adv_a6_self_delete.pog" "data/adv_a6_self_delete.lrat"

/--
error: count_models: the verified check rejected the certificate for 'adv_a8':
  part C (every input clause implied by the POG): input clause 1 (1 0) is not implied by the POG: the assignment -1 satisfies the POG root 2 and falsifies the clause (the circuit has models that are not models of the formula)
'adv_a8' was not declared (the reports come from unverified diagnostics).
-/
#guard_msgs in
count_models adv_a8 "adversarial/a8_leftover_derived.cnf" "data/adv_a8_leftover_derived.pog" "data/adv_a8_leftover_derived.lrat"

/--
error: count_models: the verified check rejected the certificate for 'adv_a10':
  part C (every input clause implied by the POG): input clause 1 (1 0) is not implied by the POG: the assignment -1 satisfies the POG root 2 and falsifies the clause (the circuit has models that are not models of the formula)
'adv_a10' was not declared (the reports come from unverified diagnostics).
-/
#guard_msgs in
count_models adv_a10 "adversarial/a10_reused_id.cnf" "data/adv_a10_reused_id.pog" "data/adv_a10_reused_id.lrat"

/-! ## Part C outside the negation-free fragment (contract audit c02, c03)

Both CPOGs are correct and translate; parts A and B accept with the true count 3, but part C
evaluates only POGs without a negated edge into an internal node and with a positive root. -/

-- c02: `F = (x1 ∨ x2) ∧ x3`, `n1 = ¬x1 ∧ ¬x2`, root `n2 = ¬n1 ∧ x3`.
def c02 : AdvCase := ⟨include_str "data/adv_c02_neg_internal_edge.cnf",
  include_str "data/adv_c02_neg_internal_edge.pog", include_str "data/adv_c02_neg_internal_edge.lrat"⟩
#guard c02.parts == some (some 3, true, false, false)
#guard !c02.accepts 3 3

-- c03: `F = ¬x1 ∨ ¬x2`, `u = x1 ∧ x2`, root `¬u`.
def c03 : AdvCase := ⟨include_str "data/adv_c03_neg_root.cnf",
  include_str "data/adv_c03_neg_root.pog", include_str "data/adv_c03_neg_root.lrat"⟩
#guard c03.parts == some (some 3, true, false, false)
#guard !c03.accepts 2 3

/--
error: count_models: the verified check rejected the certificate for 'adv_c02':
  part C (every input clause implied by the POG): node 1 (variable 5, POG line 4) has a negated edge into an internal node; part C accepts only negation-free POGs
'adv_c02' was not declared (the reports come from unverified diagnostics).
-/
#guard_msgs in
count_models adv_c02 "data/adv_c02_neg_internal_edge.cnf" "data/adv_c02_neg_internal_edge.pog" "data/adv_c02_neg_internal_edge.lrat"

/--
error: count_models: the verified check rejected the certificate for 'adv_c03':
  part C (every input clause implied by the POG): the root -3 is a negated node; part C accepts only negation-free POGs (no negated edge into an internal node, positive root), as cpog-gen writes them
'adv_c03' was not declared (the reports come from unverified diagnostics).
-/
#guard_msgs in
count_models adv_c03 "data/adv_c03_neg_root.cnf" "data/adv_c03_neg_root.pog" "data/adv_c03_neg_root.lrat"

/-! ## C4 and C2 in the Lean format (a5, a5b, a9 by hand)

C4: the sum `s = x1 ∨ x1` is not exclusive. With `F = x1` and root `s`, part A's count formula
would give 2 (true count 1), and parts B and C accept. A hint can only cite a defining clause of
an earlier node: without hints, with a hint that cites the node itself, and with a hint that
cites an earlier node's defining clause `¬n ∨ x1` (satisfied by `x1`, so not strict RUP), part A
rejects. C2: node `i` always defines `V + i`, so a collision with an input variable cannot be
written; an argument that refers to the node itself or to a later node is rejected. -/

/-- Part A's report on a POG file (`none`: accepted). -/
def reportA (pog : String) : Option String :=
  (parsePogCert pog).bind fun c => Diag.partA c (Diag.nodeLines pog)

def c4NoHint : AdvCase := ⟨"p cnf 1 1\n1 0\n", "V 1\nr 2\ns 1 1 0\n", "6 0 1 3 5 0\n"⟩
def c4SelfHint : AdvCase := ⟨"p cnf 1 1\n1 0\n", "V 1\nr 2\ns 1 1 0:0 0\n", "6 0 1 3 5 0\n"⟩
def c4DefHint : AdvCase := ⟨"p cnf 1 1\n1 0\n", "V 1\nr 3\np 1 0\ns 1 1 0:1 0\n", "8 0 1 5 7 0\n"⟩
#guard [c4NoHint, c4SelfHint, c4DefHint].all fun k =>
  k.parts == some (none, true, true, true) && !k.accepts 1 2 && !k.accepts 1 1

/--
info: some
  "node 0 (variable 2, POG line 3): the exclusion clause -1 -1 0 of the sum does not follow by strict RUP from the cited defining clauses (condition C4)"
-/
#guard_msgs in
#eval reportA c4NoHint.pog

/--
info: some
  "node 0 (variable 2, POG line 3): exclusion hint 0:0 does not cite a defining clause of an earlier node (condition C4)"
-/
#guard_msgs in
#eval reportA c4SelfHint.pog

/--
info: some
  "node 1 (variable 3, POG line 4): the exclusion clause -1 -1 0 of the sum does not follow by strict RUP from the cited defining clauses (condition C4)"
-/
#guard_msgs in
#eval reportA c4DefHint.pog

-- C2 (formula of a9, `F = x1` over 2 variables): node 0 (variable 3) refers to itself, or to
-- the later node 1 (variable 4).
#guard (parsePogCert "V 2\nr 3\np 3 0\n").map checkPog == some none
#guard (parsePogCert "V 2\nr 3\np 4 1 0\np 2 0\n").map checkPog == some none
#guard !checkAll 2 (LRATCatcher.parseDimacs "p cnf 2 1\n1 0\n") "V 2\nr 3\np 3 0\n" "" 1

/-- info: some "node 0 (variable 3, POG line 3): argument 3 is not an earlier variable (condition C2)" -/
#guard_msgs in
#eval reportA "V 2\nr 3\np 3 0\n"

/-- info: some "node 0 (variable 3, POG line 3): argument 4 is not an earlier variable (condition C2)" -/
#guard_msgs in
#eval reportA "V 2\nr 3\np 4 1 0\np 2 0\n"
