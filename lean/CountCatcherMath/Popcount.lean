import CountCatcherChecker.Pog
import CountCatcherChecker.Popcount

/-!
# Word-wise popcount: `popcountFast = popcount`

Two facts about the specification `popcount n s = (List.range n).countP s.testBit` carry the
proof: the bits `0, …, a+b-1` split into the low `a` bits and the low `b` bits of `s >>> a`
(`popcount_add`), and reducing `s` modulo `2^m` keeps the low `n ≤ m` bits (`popcount_mod`).
The byte table, the bit loop, the word walk and the halving are instances of these.
-/

namespace CountCatcher

theorem popcount_add (a b s : Nat) : popcount (a + b) s = popcount a s + popcount b (s >>> a) := by
  unfold popcount
  rw [List.range_add, List.countP_append, List.countP_map]
  congr 1
  apply List.countP_congr
  intro x _
  simp [Nat.testBit_shiftRight]

theorem popcount_mod {n m : Nat} (s : Nat) (h : n ≤ m) : popcount n (s % 2 ^ m) = popcount n s := by
  unfold popcount
  apply List.countP_congr
  intro x hx
  rw [List.mem_range] at hx
  rw [Nat.testBit_mod_two_pow]
  simp [show x < m by omega]

theorem popcount_zero_right (n : Nat) : popcount n 0 = 0 := by
  simp [popcount, Nat.zero_testBit]

theorem popcount_one (s : Nat) : popcount 1 s = s % 2 := by
  unfold popcount
  rw [List.range_one, List.countP_singleton, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one s with h | h <;> simp [h]

theorem popTable_getElem! {i : Nat} (hi : i < 256) : popTable[i]! = popcount 8 i := by
  rw [getElem!_pos popTable i (by simp [popTable]; omega)]
  simp [popTable, Array.getElem_ofFn, popcount]

theorem popBytes_eq : ∀ (k : Nat) (w : UInt64) (acc : Nat),
    popBytes k w acc = acc + popcount (8 * k) w.toNat := by
  intro k
  induction k with
  | zero => intro w acc; simp [popBytes, popcount]
  | succ k ih =>
    intro w acc
    have hb : (w &&& 255).toNat = w.toNat % 2 ^ 8 := by
      rw [UInt64.toNat_and, show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
    have hlt : w.toNat % 2 ^ 8 < 256 := Nat.mod_lt _ (by decide)
    rw [popBytes, ih, hb, popTable_getElem! hlt, popcount_mod _ (Nat.le_refl 8),
      UInt64.toNat_shiftRight, show (8 : UInt64).toNat % 64 = 8 from rfl,
      show 8 * (k + 1) = 8 + 8 * k by omega, popcount_add, Nat.add_assoc]

theorem popBits_eq : ∀ (n : Nat) (w : UInt64) (acc : Nat),
    popBits n w acc = acc + popcount n w.toNat := by
  intro n
  induction n with
  | zero => intro w acc; simp [popBits, popcount]
  | succ n ih =>
    intro w acc
    rw [popBits, ih, UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod,
      UInt64.toNat_shiftRight, show (1 : UInt64).toNat % 64 = 1 from rfl,
      show n + 1 = 1 + n by omega, popcount_add, popcount_one, Nat.add_assoc]

theorem popcountRun_eq (n s : Nat) : popcountRun n s = popcount n s := by
  induction n using Nat.strongRecOn generalizing s with
  | _ n ih =>
    rw [popcountRun]
    by_cases hs : s = 0
    · rw [if_pos hs, hs, popcount_zero_right]
    rw [if_neg hs]
    by_cases hn : n < 64
    · rw [if_pos hn, popBits_eq, Nat.zero_add, UInt64.toNat_ofNat', popcount_mod _ (by omega)]
    · rw [if_neg hn, popBytes_eq, Nat.zero_add, ih (n - 64) (by omega), UInt64.toNat_ofNat',
        popcount_mod _ (Nat.le_refl _), ← popcount_add, show 8 * 8 + (n - 64) = n by omega]

theorem sub_shiftRight_shiftLeft (s h : Nat) : s - (s >>> h <<< h) = s % 2 ^ h := by
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := Nat.mod_add_div s (2 ^ h)
  rw [Nat.mul_comm] at this
  omega

/-- The word-wise popcount equals the specification on every input. -/
theorem popcountFast_eq (n s : Nat) : popcountFast n s = popcount n s := by
  induction n using Nat.strongRecOn generalizing s with
  | _ n ih =>
    rw [popcountFast]
    by_cases hs : s = 0
    · rw [if_pos hs, hs, popcount_zero_right]
    rw [if_neg hs]
    by_cases hn : n ≤ 256
    · rw [if_pos hn]; exact popcountRun_eq n s
    · rw [if_neg hn]
      dsimp only
      rw [ih _ (by omega), ih _ (by omega), sub_shiftRight_shiftLeft, popcount_mod _ (Nat.le_refl _),
        ← popcount_add, show 64 * (n / 128) + (n - 64 * (n / 128)) = n by omega]

end CountCatcher
