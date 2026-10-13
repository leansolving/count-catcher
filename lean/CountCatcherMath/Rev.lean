import CountCatcherMath.Main
import CountCatcherChecker.Rev

/-!
# Part C soundness: `checkRev` gives `RevEval`

Only one direction is needed: if an assignment falsifying `C` makes node `j` true, the
propagated value of `j` is true. Skipping nodes outside the cone keeps the value `true`,
an over-approximation, so it needs no argument. Negated edges into internal nodes would
break the induction, hence `negationFree`.
-/

open Std.Sat

namespace CountCatcher

variable {P : Pog} {st : PState} {C : CNF.Clause Nat} {a : Nat → Bool}

/-- Propagated values are over-approximations of the values under `a`. -/
def SatInv (P : Pog) (a : Nat → Bool) (sat : Array Bool) : Prop :=
  ∀ j (hj : j < sat.size), P.evalVar a (P.V + j) = true → sat[j] = true

theorem litSat_of_true (hC : CNF.Clause.eval a C = false) {sat : Array Bool} (hinv : SatInv P a sat)
    {l : Literal Nat} (hneg : l.1 < P.V ∨ l.2 = true) (hl : l.1 < P.V + sat.size)
    (ht : P.evalLit a l = true) : litSat P.V C sat l = true := by
  unfold litSat
  split_ifs with hv
  · -- input literal: it cannot occur in C, since C is false under a
    simp only [Bool.not_eq_true']
    by_contra hmem
    simp only [Bool.not_eq_false, List.contains_iff_mem] at hmem
    have : CNF.Clause.eval a C = true := by
      simp only [CNF.Clause.eval, List.any_eq_true]
      refine ⟨l, hmem, ?_⟩
      simpa [Pog.evalLit, Pog.evalVar, hv] using ht
    rw [this] at hC; exact absurd hC (by simp)
  · -- node literal: positive, so the node is true under a
    have hpos : l.2 = true := hneg.resolve_left hv
    have hj : l.1 - P.V < sat.size := by omega
    have hval : P.evalVar a (P.V + (l.1 - P.V)) = true := by
      rw [show P.V + (l.1 - P.V) = l.1 by omega]
      simpa [Pog.evalLit, hpos] using ht
    rw [getElem!_pos sat (l.1 - P.V) hj]
    exact hinv _ hj hval

theorem nodeSat_of_true (hP : P.WF) (hC : CNF.Clause.eval a C = false) {sat : Array Bool}
    (hinv : SatInv P a sat) {i : Nat} (hsize : sat.size = i) (hi : i < P.nodes.size)
    (hnf : ∀ l ∈ Pog.Node.args P.nodes[i], l.1 < P.V ∨ l.2 = true) (mask : Nat)
    (ht : P.evalVar a (P.V + i) = true) : nodeSat P.V P st C mask sat i = true := by
  unfold nodeSat
  split_ifs with hcone
  · have hargs := hP.args_lt i hi
    rw [Array.getElem?_eq_getElem hi]
    generalize hn : P.nodes[i] = n at hargs hnf
    cases n with
    | prod args =>
      simp only [Pog.Node.args] at hargs hnf
      rw [P.evalVar_prod a hi hn, List.all_eq_true] at ht
      simp only [List.all_eq_true]
      intro l hl
      have := ht l hl
      rw [dif_pos (hargs l hl)] at this
      exact litSat_of_true hC hinv (hnf l hl) (by rw [hsize]; exact hargs l hl) this
    | sum x y =>
      simp only [Pog.Node.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hargs hnf
      rw [P.evalVar_sum a hi hn, dif_pos hargs.1, dif_pos hargs.2, Bool.or_eq_true] at ht
      simp only [Bool.or_eq_true]
      rcases ht with ht | ht
      · exact Or.inl (litSat_of_true hC hinv hnf.1 (by rw [hsize]; exact hargs.1) ht)
      · exact Or.inr (litSat_of_true hC hinv hnf.2 (by rw [hsize]; exact hargs.2) ht)
  · rfl

theorem clauseSat_inv (hP : P.WF) (hC : CNF.Clause.eval a C = false)
    (hnf : ∀ i (hi : i < P.nodes.size), ∀ l ∈ Pog.Node.args P.nodes[i], l.1 < P.V ∨ l.2 = true) :
    (clauseSat P.V P st C).size = P.nodes.size ∧ SatInv P a (clauseSat P.V P st C) := by
  unfold clauseSat
  generalize C.foldl (fun m l => m ||| (1 <<< l.1)) 0 = mask
  suffices h : ∀ k ≤ P.nodes.size,
      ((List.range k).foldl (fun sat i => sat.push (nodeSat P.V P st C mask sat i)) #[]).size = k ∧
      SatInv P a ((List.range k).foldl (fun sat i => sat.push (nodeSat P.V P st C mask sat i)) #[]) from
    h _ le_rfl
  intro k
  induction k with
  | zero => intro _; exact ⟨rfl, fun j hj => by simp at hj⟩
  | succ k ih =>
    intro hk
    obtain ⟨hs, hinv⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by simp [hs], ?_⟩
    intro j hj ht
    rw [Array.size_push] at hj
    by_cases hjk : j < k
    · rw [Array.getElem_push_lt (by omega)]; exact hinv j (by omega) ht
    · have hjk' : j = k := by omega
      subst hjk'
      rw [Array.getElem_push, dif_neg (by omega)]
      exact nodeSat_of_true hP hC hinv hs (by omega) (hnf _ (by omega)) mask ht

theorem clauseRefuted_sound (hP : P.WF)
    (hnf : ∀ i (hi : i < P.nodes.size), ∀ l ∈ Pog.Node.args P.nodes[i], l.1 < P.V ∨ l.2 = true)
    {r : Literal Nat} (hr : r.1 < P.numVars) (hrneg : r.1 < P.V ∨ r.2 = true)
    (h : clauseRefuted P.V P st C r = true) (ht : P.evalLit a r = true) :
    CNF.Clause.eval a C = true := by
  by_contra hC
  rw [Bool.not_eq_true] at hC
  unfold clauseRefuted at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · -- a tautological clause is true under every assignment
    obtain ⟨⟨v, b⟩, hl, hl'⟩ := List.any_eq_true.1 h
    rw [List.contains_iff_mem] at hl'
    have : CNF.Clause.eval a C = true := by
      simp only [CNF.Clause.eval, List.any_eq_true]
      by_cases hab : a v = b
      · exact ⟨(v, b), hl, by simp [hab]⟩
      · exact ⟨(v, !b), hl', by cases hv : a v <;> cases b <;> simp_all⟩
    rw [this] at hC; exact absurd hC (by simp)
  · obtain ⟨hsize, hinv⟩ := clauseSat_inv (st := st) hP hC hnf
    have := litSat_of_true hC hinv hrneg (by rw [hsize]; exact hr) ht
    rw [this] at h; exact absurd h (by simp)

/-- Part C soundness. -/
theorem checkRev_sound (hP : P.WF) {F : CNF Nat} {r : Literal Nat} (hr : r.1 < P.numVars)
    (h : checkRev P.V P st F r = true) : RevEval F P r := by
  unfold checkRev at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hnf, hall⟩ := h
  unfold negationFree at hnf
  rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff] at hnf
  obtain ⟨hrneg, hnodes⟩ := hnf
  have hnf' : ∀ i (hi : i < P.nodes.size), ∀ l ∈ Pog.Node.args P.nodes[i],
      l.1 < P.V ∨ l.2 = true := by
    intro i hi l hl
    rw [Array.all_eq_true_iff_forall_mem] at hnodes
    have := hnodes _ (Array.getElem_mem hi)
    rw [List.all_eq_true] at this
    have := this l hl
    simpa [Bool.or_eq_true, decide_eq_true_iff] using this
  intro a ha
  unfold CNF.eval
  rw [Array.all_eq_true_iff_forall_mem]
  intro C hC
  rw [Array.all_eq_true_iff_forall_mem] at hall
  exact clauseRefuted_sound hP hnf' hr hrneg (hall C hC) ha

/-! ## Bit-parallel part C

The invariant of `SatInv`, one bit at a time: if an assignment falsifying clause `cs[j]`
makes node `i` true, bit `j` of the kill mask of `i` is clear. -/

/-- The bit-setting folds of `occMask` and `reqMask`. -/
theorem testBit_foldl_bits (p : Nat → Bool) (n m j : Nat) :
    ((List.range n).foldl (fun m i => if p i then m ||| (1 <<< i) else m) m).testBit j =
      (m.testBit j || (decide (j < n) && p j)) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have step : ∀ m', (if p n then m' ||| (1 <<< n) else m').testBit j =
        (m'.testBit j || (decide (j = n) && p n)) := by
      intro m'
      by_cases hp : p n
      · simp [hp, Nat.one_shiftLeft, Nat.testBit_two_pow, eq_comm]
      · simp [hp]
    rw [step, ih]
    by_cases hjn : j = n
    · subst hjn; simp
    · have h' : (j ≤ n) = (j < n) := propext (by omega)
      simp [hjn, h']

theorem testBit_occMask (cs : List (CNF.Clause Nat)) (x j : Nat) :
    (occMask cs x).testBit j = (decide (j < cs.length) && (cs[j]!).any fun l => litIdx l == x) := by
  unfold occMask
  rw [testBit_foldl_bits (fun j => (cs[j]!).any fun l => litIdx l == x)]
  simp

theorem testBit_reqMask (cs : List (CNF.Clause Nat)) (j : Nat) :
    (reqMask cs).testBit j = (decide (j < cs.length) && !isTaut (cs[j]!)) := by
  unfold reqMask
  rw [testBit_foldl_bits (fun j => !isTaut (cs[j]!))]
  simp

theorem litIdx_inj {l l' : Literal Nat} (h : litIdx l = litIdx l') : l = l' := by
  obtain ⟨v, b⟩ := l
  obtain ⟨v', b'⟩ := l'
  cases b <;> cases b' <;> simp [litIdx] at h <;> simp <;> omega

theorem eval_of_isTaut (h : isTaut C = true) : CNF.Clause.eval a C = true := by
  obtain ⟨⟨v, b⟩, hl, hl'⟩ := List.any_eq_true.1 h
  rw [List.contains_iff_mem] at hl'
  simp only [CNF.Clause.eval, List.any_eq_true]
  by_cases hab : a v = b
  · exact ⟨(v, b), hl, by simp [hab]⟩
  · exact ⟨(v, !b), hl', by cases hv : a v <;> cases b <;> simp_all⟩

/-- Kill masks are sound for bit `j`: nodes true under `a` have bit `j` clear. -/
def KillInv (P : Pog) (a : Nat → Bool) (j : Nat) (k : Array Nat) : Prop :=
  ∀ i (hi : i < k.size), P.evalVar a (P.V + i) = true → (k[i]).testBit j = false

variable {cs : List (CNF.Clause Nat)} {j : Nat}

theorem testBit_foldl_or (f : Literal Nat → Nat) (args : List (Literal Nat)) (m : Nat) :
    (args.foldl (fun m l => m ||| f l) m).testBit j =
      (m.testBit j || args.any fun l => (f l).testBit j) := by
  induction args generalizing m with
  | nil => simp
  | cons l ls ih => rw [List.foldl_cons, ih]; simp [Bool.or_assoc]

theorem litKill_of_true (hC : CNF.Clause.eval a (cs[j]!) = false) {k : Array Nat}
    (hinv : KillInv P a j k) {l : Literal Nat} (hneg : l.1 < P.V ∨ l.2 = true)
    (hl : l.1 < P.V + k.size) (ht : P.evalLit a l = true) :
    (litKill P.V (Array.ofFn (n := 2 * P.V) fun x => occMask cs x.1) k l).testBit j = false := by
  unfold litKill
  split_ifs with hv
  · have hx : litIdx l < 2 * P.V := by unfold litIdx; split <;> omega
    rw [getElem!_pos _ _ (by simpa using hx), Array.getElem_ofFn, testBit_occMask]
    by_contra hbit
    simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
      beq_iff_eq] at hbit
    obtain ⟨-, l', hl', hidx⟩ := hbit
    have hll := litIdx_inj hidx
    subst hll
    have : CNF.Clause.eval a (cs[j]!) = true := by
      simp only [CNF.Clause.eval, List.any_eq_true]
      refine ⟨l', hl', ?_⟩
      simpa [Pog.evalLit, Pog.evalVar, hv] using ht
    rw [this] at hC; exact absurd hC (by simp)
  · have hpos : l.2 = true := hneg.resolve_left hv
    have hj : l.1 - P.V < k.size := by omega
    have hval : P.evalVar a (P.V + (l.1 - P.V)) = true := by
      rw [show P.V + (l.1 - P.V) = l.1 by omega]
      simpa [Pog.evalLit, hpos] using ht
    rw [getElem!_pos k (l.1 - P.V) hj]
    exact hinv _ hj hval

theorem nodeKill_of_true (hP : P.WF) (hC : CNF.Clause.eval a (cs[j]!) = false) {k : Array Nat}
    (hinv : KillInv P a j k) {i : Nat} (hsize : k.size = i) (hi : i < P.nodes.size)
    (hnf : ∀ l ∈ Pog.Node.args P.nodes[i], l.1 < P.V ∨ l.2 = true)
    (ht : P.evalVar a (P.V + i) = true) :
    (nodeKill P.V P (Array.ofFn (n := 2 * P.V) fun x => occMask cs x.1) k i).testBit j = false := by
  unfold nodeKill
  have hargs := hP.args_lt i hi
  rw [Array.getElem?_eq_getElem hi]
  generalize hn : P.nodes[i] = n at hargs hnf
  cases n with
  | prod args =>
    simp only [Pog.Node.args] at hargs hnf
    rw [P.evalVar_prod a hi hn, List.all_eq_true] at ht
    rw [testBit_foldl_or, Nat.zero_testBit, Bool.false_or, List.any_eq_false]
    intro l hl
    have := ht l hl
    rw [dif_pos (hargs l hl)] at this
    rw [litKill_of_true hC hinv (hnf l hl) (by rw [hsize]; exact hargs l hl) this]
    simp
  | sum x y =>
    simp only [Pog.Node.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hargs hnf
    rw [P.evalVar_sum a hi hn, dif_pos hargs.1, dif_pos hargs.2, Bool.or_eq_true] at ht
    rw [Nat.testBit_and]
    rcases ht with ht | ht
    · rw [litKill_of_true hC hinv hnf.1 (by rw [hsize]; exact hargs.1) ht]; simp
    · rw [litKill_of_true hC hinv hnf.2 (by rw [hsize]; exact hargs.2) ht]; simp

theorem killMasks_inv (hP : P.WF) (hC : CNF.Clause.eval a (cs[j]!) = false)
    (hnf : ∀ i (hi : i < P.nodes.size), ∀ l ∈ Pog.Node.args P.nodes[i], l.1 < P.V ∨ l.2 = true) :
    let k := killMasks P.V P (Array.ofFn (n := 2 * P.V) fun x => occMask cs x.1)
    k.size = P.nodes.size ∧ KillInv P a j k := by
  intro k
  unfold k killMasks
  suffices h : ∀ n ≤ P.nodes.size,
      let k := (List.range n).foldl (fun k i =>
        k.push (nodeKill P.V P (Array.ofFn (n := 2 * P.V) fun x => occMask cs x.1) k i)) #[]
      k.size = n ∧ KillInv P a j k from h _ le_rfl
  intro n
  induction n with
  | zero => intro _; exact ⟨rfl, fun i hi => by simp at hi⟩
  | succ n ih =>
    intro hn
    obtain ⟨hs, hinv⟩ := ih (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by simp [hs], ?_⟩
    intro i hi ht
    rw [Array.size_push] at hi
    by_cases hin : i < n
    · rw [Array.getElem_push_lt (by omega)]; exact hinv i (by omega) ht
    · have hin' : i = n := by omega
      subst hin'
      rw [Array.getElem_push, dif_neg (by omega)]
      exact nodeKill_of_true hP hC hinv hs (by omega) (hnf _ (by omega)) ht

/-- A refuted batch: every clause of the batch holds under every assignment making the root
    true. -/
theorem batchRefuted_sound (hP : P.WF)
    (hnf : ∀ i (hi : i < P.nodes.size), ∀ l ∈ Pog.Node.args P.nodes[i], l.1 < P.V ∨ l.2 = true)
    {r : Literal Nat} (hr : r.1 < P.numVars) (hrneg : r.1 < P.V ∨ r.2 = true)
    (h : batchRefuted P.V P cs r = true) (hj : j < cs.length) (ht : P.evalLit a r = true) :
    CNF.Clause.eval a (cs[j]!) = true := by
  by_contra hC
  rw [Bool.not_eq_true] at hC
  by_cases htaut : isTaut (cs[j]!) = true
  · rw [eval_of_isTaut htaut] at hC; exact absurd hC (by simp)
  · obtain ⟨hsize, hinv⟩ := killMasks_inv (a := a) hP hC hnf
    unfold batchRefuted at h
    simp only [beq_iff_eq] at h
    have hreq : (reqMask cs).testBit j = true := by
      have ht' : isTaut (cs[j]!) = false := by simpa using htaut
      rw [testBit_reqMask, ht']; simp [hj]
    have hbit := congrArg (fun x => Nat.testBit x j) h
    simp only [Nat.testBit_and, hreq, Bool.and_true] at hbit
    rw [litKill_of_true hC hinv hrneg (by rw [hsize]; exact hr) ht] at hbit
    exact absurd hbit (by simp)

theorem mem_chunks {α : Type} {w : Nat} (hw : 0 < w) :
    ∀ (fuel : Nat) (l : List α), l.length ≤ fuel → ∀ x ∈ l, ∃ c ∈ chunks w fuel l, x ∈ c := by
  intro fuel
  induction fuel with
  | zero => intro l hl x hx; cases l with
    | nil => simp at hx
    | cons _ _ => simp at hl
  | succ fuel ih =>
    intro l hl x hx
    have hne : l.isEmpty = false := by cases l <;> simp_all
    simp only [chunks, hne, Bool.false_eq_true, ite_false, List.mem_cons]
    rw [← List.take_append_drop w l, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ⟨_, Or.inl rfl, hx⟩
    · obtain ⟨c, hc, hxc⟩ := ih (l.drop w) (by
        have : l.length ≠ 0 := by cases l <;> simp_all
        simp only [List.length_drop]; omega) x hx
      exact ⟨c, Or.inr hc, hxc⟩

/-- Part C soundness for the bit-parallel check. -/
theorem checkRevKill_sound (hP : P.WF) {F : CNF Nat} {r : Literal Nat} (hr : r.1 < P.numVars)
    (h : checkRevKill P.V P F r = true) : RevEval F P r := by
  unfold checkRevKill at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hnf, hall⟩ := h
  unfold negationFree at hnf
  rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff] at hnf
  obtain ⟨hrneg, hnodes⟩ := hnf
  have hnf' : ∀ i (hi : i < P.nodes.size), ∀ l ∈ Pog.Node.args P.nodes[i],
      l.1 < P.V ∨ l.2 = true := by
    intro i hi l hl
    rw [Array.all_eq_true_iff_forall_mem] at hnodes
    have := hnodes _ (Array.getElem_mem hi)
    rw [List.all_eq_true] at this
    have := this l hl
    simpa [Bool.or_eq_true, decide_eq_true_iff] using this
  intro a ha
  unfold CNF.eval
  rw [Array.all_eq_true_iff_forall_mem]
  intro C hC
  obtain ⟨cs, hcs, hCcs⟩ := mem_chunks (w := 63) (by omega) F.clauses.size F.clauses.toList
    (by simp) C (by simpa using hC)
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hCcs
  have hb := List.all_eq_true.1 hall cs hcs
  have := batchRefuted_sound hP hnf' hr hrneg hb hj ha
  rwa [getElem!_pos cs j hj] at this

end CountCatcher
