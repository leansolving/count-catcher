/-!
# CountCatcherChecker.Popcount — word-wise popcount for part A's sum nodes, executable

The specification `popcount V s` (`Pog.lean`) tests the bits `0, …, V-1` of `s` one at a time;
on a big `Nat` each `testBit` shifts and allocates, so one call costs O(V²/64) and V allocations
(77 percent of part A on the 12x12 grid, 2026-10-01). Here the low 64 bits are read with
`UInt64.ofNat` (no allocation) and counted with a byte table. A short bitset is walked by shifting
right by 64; a long one is first halved at word boundaries, so the shifts copy O(n log n) words
for an `n`-word bitset instead of O(n²). A zero bitset ends the recursion (sparse supports).
`CountCatcherMath.popcountFast_eq` proves `popcountFast V s = popcount V s`.
-/

namespace CountCatcher

/-- Number of set bits of each byte: entry `i` is `(List.range 8).countP i.testBit`. -/
def popTable : Array Nat := Array.ofFn (n := 256) fun i => (List.range 8).countP i.val.testBit

/-- Add the set bits of the low `k` bytes of `w` to `acc`, one table lookup per byte. -/
def popBytes : Nat → UInt64 → Nat → Nat
  | 0, _, acc => acc
  | k + 1, w, acc => popBytes k (w >>> 8) (acc + popTable[(w &&& 255).toNat]!)

/-- Add the set bits among the low `n` bits of `w` to `acc`, one bit at a time (for the last,
    partial word). -/
def popBits : Nat → UInt64 → Nat → Nat
  | 0, _, acc => acc
  | n + 1, w, acc => popBits n (w >>> 1) (acc + (w &&& 1).toNat)

/-- Set bits among bits `0, …, n-1` of `s`, word by word from the low end. Each step shifts the
    rest of `s` (a copy), so this is for bitsets of a few words. -/
def popcountRun (n s : Nat) : Nat :=
  if s = 0 then 0
  else if n < 64 then popBits n (UInt64.ofNat s) 0
  else popBytes 8 (UInt64.ofNat s) 0 + popcountRun (n - 64) (s >>> 64)
termination_by n
decreasing_by omega

/-- Set bits among bits `0, …, n-1` of `s` (equal to `popcount n s`,
    `CountCatcherMath.popcountFast_eq`). Bitsets of more than four words are split at a word boundary
    near the middle: the low part is `s - (s >>> h <<< h)`, the high part `s >>> h`. -/
def popcountFast (n s : Nat) : Nat :=
  if s = 0 then 0
  else if n ≤ 256 then popcountRun n s
  else
    let h := 64 * (n / 128)
    let hi := s >>> h
    popcountFast h (s - (hi <<< h)) + popcountFast (n - h) hi
termination_by n
decreasing_by all_goals omega

end CountCatcher
