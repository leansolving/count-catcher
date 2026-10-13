/-!
# Direct baselines: unverified native counters, timing only

The direct alternative to the certificate route for the structured families: broken-profile
DP for domino tilings and for independent sets of the grid (`O(R C 2^C)` big-number
additions), bitmask backtracking for n-queens. Mathlib-free, compiled natively
(`lake build count-catcher-baselines`). Nothing here is proved.

Usage: .lake/build/bin/count-catcher-baselines domino|indep|queens N...
-/

/-- Domino tilings of the `R × C` board. Cells in row-major order; bit `c` of the profile
    says that the current cell of column `c` is already covered from above. -/
def dominoCount (R C : Nat) : Nat := Id.run do
  let full := 1 <<< C
  let mut dp : Array Nat := (Array.replicate full 0).set! 0 1
  for r in [0:R] do
    for c in [0:C] do
      let mut nd : Array Nat := Array.replicate full 0
      for m in [0:full] do
        let w := dp[m]!
        if w != 0 then
          if (m >>> c) &&& 1 == 1 then
            nd := nd.modify (m ^^^ (1 <<< c)) (· + w)
          else
            if r + 1 < R then
              nd := nd.modify (m ||| (1 <<< c)) (· + w)
            if c + 1 < C && (m >>> (c + 1)) &&& 1 == 0 then
              nd := nd.modify (m ||| (1 <<< (c + 1))) (· + w)
      dp := nd
  return dp[0]!

/-- Independent sets of the `R × C` grid (hard squares). Bit `c` of the profile: the last
    processed cell of column `c` is chosen. -/
def indepCount (R C : Nat) : Nat := Id.run do
  let full := 1 <<< C
  let mut dp : Array Nat := (Array.replicate full 0).set! 0 1
  for _ in [0:R] do
    for c in [0:C] do
      let mut nd : Array Nat := Array.replicate full 0
      for m in [0:full] do
        let w := dp[m]!
        if w != 0 then
          let off := if (m >>> c) &&& 1 == 1 then m ^^^ (1 <<< c) else m
          nd := nd.modify off (· + w)
          let upFree := (m >>> c) &&& 1 == 0
          let leftFree := c == 0 || (m >>> (c - 1)) &&& 1 == 0
          if upFree && leftFree then
            nd := nd.modify (m ||| (1 <<< c)) (· + w)
      dp := nd
  return dp.foldl (· + ·) 0

/-- n-queens solutions by bitmask backtracking over rows. -/
partial def queensGo (full cols d1 d2 : UInt64) : Nat :=
  if cols == full then 1 else Id.run do
    let mut avail := full &&& ~~~(cols ||| d1 ||| d2)
    let mut n := 0
    while avail != 0 do
      let bit := avail &&& (0 - avail)
      avail := avail ^^^ bit
      n := n + queensGo full (cols ||| bit) (((d1 ||| bit) <<< 1) &&& full) ((d2 ||| bit) >>> 1)
    return n

def queensCount (n : Nat) : Nat := queensGo ((1 <<< n.toUInt64) - 1) 0 0 0

def main (args : List String) : IO Unit := do
  match args with
  | fam :: ns =>
    for s in ns do
      let n := s.toNat!
      let t0 ← IO.monoNanosNow
      let v := match fam with
        | "domino" => dominoCount n n
        | "indep" => indepCount n n
        | _ => queensCount n
      IO.println s!"{fam} {n} count={v}"
      let t1 ← IO.monoNanosNow
      IO.println s!"{fam} {n} ms={(t1 - t0).toFloat / 1e6}"
  | [] => IO.println "usage: count-catcher-baselines domino|indep|queens N..."
