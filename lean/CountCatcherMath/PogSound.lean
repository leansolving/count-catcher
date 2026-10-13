import CountCatcherMath.Main
import CountCatcherMath.Popcount
import CountCatcherChecker.Pog

/-!
# Part A soundness: `checkPog` accepts ⇒ `P.WF` and the count is `countRoot`
-/

open Std.Sat

namespace CountCatcher

/-- Strict RUP is sound: no assignment makes the starting literals and all hint clauses true. -/
theorem rupStrict_sound (b : Nat → Bool) :
    ∀ (asg : List (Literal Nat)) (cls : List (CNF.Clause Nat)), rupStrict asg cls = true →
      (∀ l ∈ asg, b l.1 = l.2) → (∀ c ∈ cls, CNF.Clause.eval b c = true) → False := by
  have contra : ∀ asg : List (Literal Nat), (∀ l ∈ asg, b l.1 = l.2) →
      (asg.any fun l => asg.contains (l.1, !l.2)) = true → False := by
    intro asg hasg h
    obtain ⟨l, hl, hl'⟩ := List.any_eq_true.1 h
    rw [List.contains_iff_mem] at hl'
    have h1 := hasg l hl
    have h2 := hasg _ hl'
    simp only at h2
    rw [h1] at h2; cases l.2 <;> simp at h2
  intro asg cls
  induction cls generalizing asg with
  | nil => intro h hasg _; exact contra asg hasg h
  | cons c cs ih =>
    intro h hasg hcls
    unfold rupStrict at h
    split_ifs at h with hc hsat
    · exact contra asg hasg hc
    · -- some literal of `c` is true under `b`
      obtain ⟨l', hl', ht'⟩ := List.any_eq_true.1 (hcls c List.mem_cons_self)
      have ht' : b l'.1 = l'.2 := by simpa using ht'
      -- it is not falsified by `asg`
      have hnf : ¬ (l'.1, !l'.2) ∈ asg := fun hm => by
        have := hasg _ hm; simp only at this; rw [ht'] at this; cases l'.2 <;> simp at this
      have hmem : l' ∈ (c.filter fun l => !asg.contains (l.1, !l.2)).eraseDups := by
        rw [List.mem_eraseDups, List.mem_filter]
        exact ⟨hl', by simp [hnf]⟩
      split at h
      · rename_i heq; rw [heq] at hmem; simp at hmem
      · rename_i l heq
        rw [heq, List.mem_singleton] at hmem
        subst hmem
        exact ih (l' :: asg) h (by
          intro l hl; rcases List.mem_cons.1 hl with rfl | hl
          · exact ht'
          · exact hasg l hl) (fun c hc => hcls c (List.mem_cons_of_mem _ hc))
      · simp at h

namespace Pog

variable (P : Pog)

theorem supp_input_iff {v : Nat} (hv : v < P.V) (x : Nat) : P.supp v x = (x == v) := by
  rw [supp]; simp [hv]

theorem countVar_input {v : Nat} (hv : v < P.V) : P.countVar v = 1 := by
  rw [countVar]; simp [hv]

theorem suppSize_input {v : Nat} (hv : v < P.V) : P.suppSize v = 1 := by
  rw [suppSize_eq]
  have : P.suppF v = {⟨v, hv⟩} := by
    ext j; simp only [suppF, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Fin.ext_iff]
    rw [supp_input_iff P hv]; simp
  rw [this, Finset.card_singleton]

end Pog

/-- Part A's state represents supports, sizes and counts of the first `k` nodes. -/
structure Rep (P : Pog) (st : PState) (k : Nat) : Prop where
  supps_size : st.supps.size = k
  sizes_size : st.sizes.size = k
  counts_size : st.counts.size = k
  supp : ∀ j < k, ∀ x, (st.supps[j]!).testBit x = P.supp (P.V + j) x
  size : ∀ j < k, st.sizes[j]! = P.suppSize (P.V + j)
  count : ∀ j < k, st.counts[j]! = P.countVar (P.V + j)

variable {P : Pog} {st : PState} {k : Nat}

theorem Rep.litSupp (h : Rep P st k) {l : Literal Nat} (hl : l.1 < P.V + k) (x : Nat) :
    (litSupp P.V st l).testBit x = P.supp l.1 x := by
  unfold CountCatcher.litSupp
  split_ifs with hv
  · rw [Nat.one_shiftLeft, Nat.testBit_two_pow, P.supp_input_iff hv]
    by_cases hx : x = l.1
    · subst hx; simp
    · have hx' : l.1 ≠ x := Ne.symm hx
      simp [hx, hx']
  · have := h.supp (l.1 - P.V) (by omega) x
    rwa [show P.V + (l.1 - P.V) = l.1 by omega] at this

theorem Rep.litSize (h : Rep P st k) {l : Literal Nat} (hl : l.1 < P.V + k) :
    litSize P.V st l = P.suppSize l.1 := by
  unfold CountCatcher.litSize
  split_ifs with hv
  · rw [P.suppSize_input hv]
  · have := h.size (l.1 - P.V) (by omega)
    rwa [show P.V + (l.1 - P.V) = l.1 by omega] at this

theorem Rep.litCount (h : Rep P st k) {l : Literal Nat} (hl : l.1 < P.V + k) :
    litCount P.V st l = P.countLit l := by
  have hc : (if l.1 < P.V then 1 else st.counts[l.1 - P.V]!) = P.countVar l.1 := by
    split_ifs with hv
    · rw [P.countVar_input hv]
    · have := h.count (l.1 - P.V) (by omega)
      rwa [show P.V + (l.1 - P.V) = l.1 by omega] at this
  unfold CountCatcher.litCount Pog.countLit
  simp only [hc, h.litSize hl]

theorem testBit_land_eq_zero {a b : Nat} (h : (a &&& b == 0) = true) (x : Nat) :
    ¬ (a.testBit x = true ∧ b.testBit x = true) := by
  rw [beq_iff_eq] at h
  intro ⟨ha, hb⟩
  have := Nat.testBit_and a b x
  rw [h, Nat.zero_testBit, ha, hb] at this
  simp at this

theorem prodFold_spec (h : Rep P st k) :
    ∀ (args : List (Literal Nat)) (acc size cnt acc' size' cnt' : Nat),
    (∀ l ∈ args, l.1 < P.V + k) →
    prodFold P.V st args acc size cnt = some (acc', size', cnt') →
    (∀ x, acc'.testBit x = (acc.testBit x || args.any fun l => P.supp l.1 x)) ∧
    size' = size + (args.map fun l => P.suppSize l.1).sum ∧
    cnt' = cnt * (args.map P.countLit).prod ∧
    (∀ l ∈ args, ∀ x, ¬ (acc.testBit x = true ∧ P.supp l.1 x = true)) ∧
    args.Pairwise (fun l₁ l₂ => ∀ x, ¬ (P.supp l₁.1 x = true ∧ P.supp l₂.1 x = true)) := by
  intro args
  induction args with
  | nil =>
    intro acc size cnt acc' size' cnt' _ hf
    simp only [prodFold, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl, rfl⟩ := hf
    simp
  | cons l ls ih =>
    intro acc size cnt acc' size' cnt' hlt hf
    simp only [prodFold] at hf
    split_ifs at hf with hd
    have hl := hlt l List.mem_cons_self
    obtain ⟨hbits, hsize, hcnt, hdisj, hpw⟩ :=
      ih _ _ _ _ _ _ (fun l' hl' => hlt l' (List.mem_cons_of_mem _ hl')) hf
    have hs : ∀ x, (litSupp P.V st l).testBit x = P.supp l.1 x := h.litSupp hl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x
      rw [hbits x, Nat.testBit_or, hs x, List.any_cons]
      cases acc.testBit x <;> cases P.supp l.1 x <;> simp
    · rw [hsize, h.litSize hl]; simp [Nat.add_assoc]
    · rw [hcnt, h.litCount hl]; simp [Nat.mul_assoc]
    · intro l' hl' x ⟨ha, hb⟩
      rcases List.mem_cons.1 hl' with rfl | hl'
      · exact testBit_land_eq_zero hd x ⟨by rw [hs x]; exact hb, ha⟩
      · exact hdisj l' hl' x ⟨by rw [Nat.testBit_or, ha]; simp, hb⟩
    · rw [List.pairwise_cons]
      refine ⟨fun l' hl' x ⟨ha, hb⟩ => hdisj l' hl' x ⟨?_, hb⟩, hpw⟩
      rw [Nat.testBit_or, hs x, ha]; simp

theorem push_getElem!_lt {α : Type} [Inhabited α] (a : Array α) (v : α) {j : Nat}
    (hj : j < a.size) : (a.push v)[j]! = a[j]! := by
  rw [getElem!_pos (a.push v) j (by simp; omega), getElem!_pos a j hj, Array.getElem_push_lt hj]

theorem push_getElem!_eq {α : Type} [Inhabited α] (a : Array α) (v : α) {j : Nat}
    (hj : j = a.size) : (a.push v)[j]! = v := by
  subst hj
  rw [getElem!_pos (a.push v) a.size (by simp), Array.getElem_push_eq]

theorem mapM_some_mem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' → ∀ b ∈ l', ∃ a ∈ l, f a = some b := by
  intro l
  induction l with
  | nil => intro l' h; simp at h; subst h; simp
  | cons a l ih =>
    intro l' h b hb
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨b', hb', l'', hl'', rfl⟩ := h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hb'⟩
    · obtain ⟨a', ha', hfa⟩ := ih l'' hl'' b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', hfa⟩

theorem hintClause_mem {i : Nat} (hi : i < P.nodes.size) {h : Hint} {c : CNF.Clause Nat}
    (hc : hintClause P.V P i h = some c) : c ∈ P.defs := by
  unfold hintClause at hc
  split_ifs at hc with hlt
  have hn : h.node < P.nodes.size := by omega
  rw [Array.getElem?_eq_getElem hn, Option.bind_some] at hc
  simp only [Pog.defs, List.mem_flatMap, List.mem_range]
  refine ⟨h.node, hn, ?_⟩
  rw [Array.getElem?_eq_getElem hn]
  exact List.mem_of_getElem? hc

namespace Pog

theorem card_suppU (P : Pog) : ∀ (ls : List (Literal Nat)),
    ls.Pairwise (fun l₁ l₂ => ∀ x, ¬ (P.supp l₁.1 x = true ∧ P.supp l₂.1 x = true)) →
    (P.suppU ls).card = (ls.map fun l => P.suppSize l.1).sum := by
  intro ls
  induction ls with
  | nil => simp [suppU]
  | cons l ls ih =>
    intro hpw
    rw [List.pairwise_cons] at hpw
    have hST : Disjoint (P.suppF l.1) (P.suppU ls) := by
      rw [Finset.disjoint_left]
      intro j hj hj'
      obtain ⟨l', hl', hj'⟩ := P.mem_suppU.1 hj'
      exact hpw.1 l' hl' j ⟨P.mem_suppF.1 hj, P.mem_suppF.1 hj'⟩
    simp only [suppU, List.map_cons, List.sum_cons]
    rw [Finset.card_union_of_disjoint hST, ih hpw.2, suppSize_eq]

end Pog

/-- What part A establishes about node `i` besides the representation. -/
structure NodeOK (P : Pog) (i : Nat) (hi : i < P.nodes.size) : Prop where
  args_lt : ∀ l ∈ Pog.Node.args P.nodes[i], l.1 < P.V + i
  prod_disjoint : ∀ args, P.nodes[i] = .prod args →
    args.Pairwise fun l₁ l₂ => ∀ x, ¬ (P.supp l₁.1 x = true ∧ P.supp l₂.1 x = true)
  sum_rup : ∀ x y, P.nodes[i] = .sum x y →
    ∃ cls : List (CNF.Clause Nat), (∀ c ∈ cls, c ∈ P.defs) ∧ rupStrict [x, y] cls = true

theorem checkNode_spec {hints : Array (List Hint)} {st' : PState} {i : Nat} (h : Rep P st i)
    (hc : checkNode P.V P hints st i = some st') :
    ∃ hi : i < P.nodes.size, NodeOK P i hi ∧ Rep P st' (i + 1) := by
  unfold checkNode at hc
  split at hc
  · simp at hc
  rename_i n hn
  have hi : i < P.nodes.size := by
    by_contra hge; rw [Array.getElem?_eq_none (by omega)] at hn; simp at hn
  have hni : P.nodes[i] = n := by
    rw [Array.getElem?_eq_getElem hi] at hn; exact Option.some.inj hn
  refine ⟨hi, ?_⟩
  split_ifs at hc with hall
  have hargs : ∀ l ∈ Pog.Node.args n, l.1 < P.V + i := by
    intro l hl; have := List.all_eq_true.1 hall l hl; simpa using this
  -- entries below `i` are unchanged by a push
  have old : ∀ {α : Type} [Inhabited α] (a : Array α) (v : α), a.size = i →
      ∀ j < i, (a.push v)[j]! = a[j]! := fun a v ha j hj => push_getElem!_lt a v (by omega)
  have new : ∀ {α : Type} [Inhabited α] (a : Array α) (v : α), a.size = i → (a.push v)[i]! = v :=
    fun a v ha => push_getElem!_eq a v ha.symm
  cases n with
  | prod args =>
    dsimp only [Pog.Node.args] at hargs hc
    split at hc
    · rename_i acc size cnt hpf
      simp only [Option.some.injEq] at hc
      subst hc
      obtain ⟨hbits, hsize, hcnt, -, hpw⟩ := prodFold_spec h args 0 0 1 acc size cnt hargs hpf
      have hsuppF : P.suppF (P.V + i) = P.suppU args := by
        ext j; rw [Pog.mem_suppF, P.supp_prod_iff hi hni hargs, Pog.mem_suppU]
        simp [Pog.mem_suppF]
      refine ⟨⟨by rw [hni]; exact hargs, fun args' h' => ?_, fun x y h' => ?_⟩, ?_⟩
      · rw [hni] at h'; cases h'; exact hpw
      · rw [hni] at h'; cases h'
      refine ⟨by simp [h.supps_size], by simp [h.sizes_size], by simp [h.counts_size], ?_, ?_, ?_⟩
      · intro j hj x
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [old _ _ h.supps_size j hj]; exact h.supp j hj x
        · rw [new _ _ h.supps_size, hbits x, Nat.zero_testBit, Bool.false_or]
          rw [Bool.eq_iff_iff, List.any_eq_true, P.supp_prod_iff hi hni hargs]
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [old _ _ h.sizes_size j hj]; exact h.size j hj
        · rw [new _ _ h.sizes_size, hsize, Nat.zero_add, Pog.suppSize_eq, hsuppF,
            P.card_suppU args hpw]
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [old _ _ h.counts_size j hj]; exact h.count j hj
        · rw [new _ _ h.counts_size, hcnt, Nat.one_mul, P.countVar_prod hi hni hargs]
    · simp at hc
  | sum x y =>
    dsimp only at hc
    simp only [Pog.Node.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hargs
    split at hc
    · rename_i cls hcls
      split_ifs at hc with hrup
      simp only [Option.some.injEq] at hc
      subst hc
      have hbits : ∀ z, (litSupp P.V st x ||| litSupp P.V st y).testBit z = P.supp (P.V + i) z := by
        intro z
        rw [Nat.testBit_or, h.litSupp hargs.1, h.litSupp hargs.2, Bool.eq_iff_iff, Bool.or_eq_true,
          P.supp_sum_iff hi hni hargs.1 hargs.2]
      have hpop : popcountFast P.V (litSupp P.V st x ||| litSupp P.V st y) =
          P.suppSize (P.V + i) := by
        rw [popcountFast_eq]
        unfold popcount Pog.suppSize card
        congr 1; funext z; exact hbits z
      have hargs' : ∀ l ∈ Pog.Node.args P.nodes[i], l.1 < P.V + i := by
        rw [hni]; intro l hl
        simp only [Pog.Node.args, List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        exacts [hargs.1, hargs.2]
      refine ⟨⟨hargs', fun args' h' => ?_, fun x' y' h' => ?_⟩, ?_⟩
      · rw [hni] at h'; cases h'
      · rw [hni] at h'; cases h'
        refine ⟨cls, fun c hc => ?_, hrup⟩
        obtain ⟨hh, -, hhc⟩ := mapM_some_mem _ _ _ hcls c hc
        exact hintClause_mem hi hhc
      refine ⟨by simp [h.supps_size], by simp [h.sizes_size], by simp [h.counts_size], ?_, ?_, ?_⟩
      · intro j hj z
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [old _ _ h.supps_size j hj]; exact h.supp j hj z
        · rw [new _ _ h.supps_size]; exact hbits z
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [old _ _ h.sizes_size j hj]; exact h.size j hj
        · rw [new _ _ h.sizes_size]; exact hpop
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [old _ _ h.counts_size j hj]; exact h.count j hj
        · rw [new _ _ h.counts_size, hpop, h.litCount hargs.1, h.litCount hargs.2,
            h.litSize hargs.1, h.litSize hargs.2, P.countVar_sum hi hni hargs.1 hargs.2]
    · simp at hc

theorem fold_spec {hints : Array (List Hint)} :
    ∀ k ≤ P.nodes.size, ∀ st' : PState,
    (List.range k).foldlM (checkNode P.V P hints) {} = some st' →
    Rep P st' k ∧ ∀ i (_ : i < k) (hi : i < P.nodes.size), NodeOK P i hi := by
  intro k
  induction k with
  | zero =>
    intro _ st' h
    simp only [List.range_zero, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨⟨rfl, rfl, rfl, fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega)⟩, fun i hi => absurd hi (by omega)⟩
  | succ k ih =>
    intro hk st' h
    rw [List.range_succ, List.foldlM_append] at h
    simp only [List.foldlM_cons, List.foldlM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at h
    obtain ⟨st, hst, st'', hnode, heq⟩ := h
    cases Option.some.inj heq
    obtain ⟨hrep, hok⟩ := ih (by omega) st hst
    obtain ⟨hi, hok', hrep'⟩ := checkNode_spec hrep hnode
    refine ⟨hrep', fun i hik hi' => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hik | rfl
    · exact hok i hik hi'
    · exact hok'

/-- Part A soundness from the fold's final state: well formed, root in range, and the count
    computed from the state is `countRoot`. -/
theorem checkPog_sound_of_fold {c : PogCert} {st : PState}
    (hst : (List.range c.pog.nodes.size).foldlM (checkNode c.pog.V c.pog c.hints) {} = some st)
    (hroot : c.root.1 < c.pog.V + c.pog.nodes.size) :
    c.pog.WF ∧ c.root.1 < c.pog.numVars ∧
      litCount c.pog.V st c.root * 2 ^ (c.pog.V - litSize c.pog.V st c.root) =
        c.pog.countRoot c.root := by
  set P := c.pog
  obtain ⟨hrep, hok⟩ := fold_spec (P := P) P.nodes.size le_rfl st hst
  have hargs : ∀ i (hi : i < P.nodes.size), ∀ l ∈ Pog.Node.args P.nodes[i], l.1 < P.V + i :=
    fun i hi => (hok i hi hi).args_lt
  have hwf : P.WF := by
    refine ⟨hargs, fun i hi args hn => (hok i hi hi).prod_disjoint args hn, ?_⟩
    intro i hi x y hn a ⟨hx, hy⟩
    obtain ⟨cls, hmem, hrup⟩ := (hok i hi hi).sum_rup x y hn
    have hxy := hargs i hi
    rw [hn] at hxy
    simp only [Pog.Node.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hxy
    have hnum : ∀ v, v < P.V + i → v < P.numVars := fun v hv => by simp [Pog.numVars]; omega
    apply rupStrict_sound (P.extend a) [x, y] cls hrup
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · rw [P.extend_eq (hnum _ hxy.1)]; simpa [Pog.evalLit] using hx
      · rw [P.extend_eq (hnum _ hxy.2)]; simpa [Pog.evalLit] using hy
    · exact fun c hc => P.defs_extend' hargs a c (hmem c hc)
  refine ⟨hwf, by simpa [Pog.numVars] using hroot, ?_⟩
  rw [Pog.countRoot, hrep.litCount hroot, hrep.litSize hroot]

/-- Part A soundness: an accepted POG is well formed and its computed count is `countRoot`. -/
theorem checkPog_sound {c : PogCert} {N : Nat} (h : checkPog c = some N) :
    c.pog.WF ∧ c.root.1 < c.pog.numVars ∧ N = c.pog.countRoot c.root := by
  unfold checkPog at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨st, hst, h⟩ := h
  split_ifs at h with hroot
  case neg => simp at h
  simp only [Option.pure_def, Option.bind_some, Option.some.injEq] at h
  obtain ⟨hwf, hr, hN⟩ := checkPog_sound_of_fold hst hroot
  exact ⟨hwf, hr, h ▸ hN⟩

end CountCatcher
