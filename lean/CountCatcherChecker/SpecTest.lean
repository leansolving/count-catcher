import CountCatcherChecker.Spec

/-! Sanity checks of the specification functions on corner cases of the counting convention.
    `#guard` evaluates by compilation: the spec functions use well-founded recursion and
    do not reduce in the kernel (relevant for a kernel-mode checker). -/

open Std.Sat CountCatcher

-- Unused universe variable: F = x over {x, y} has 2 models; root is the input literal x.
#guard modelCount 2 ⟨#[[(0, true)]]⟩ = 2
#guard (Pog.mk 2 #[]).countRoot (0, true) = 2

-- Unequal sum supports: x ∨ (¬x ∧ y) over {x, y} has 3 models.
-- var 2 := ¬x ∧ y, var 3 := x ∨ var 2
def pSum : Pog := ⟨2, #[.prod [(0, false), (1, true)], .sum (0, true) (2, true)]⟩
#guard pSum.countRoot (3, true) = 3
#guard modelCount 2 ⟨#[[(0, true), (1, true)]]⟩ = 3

-- Negative root with an unused variable: ¬(x ∧ y) over {x, y, z} has 6 models.
def pNeg : Pog := ⟨3, #[.prod [(0, true), (1, true)]]⟩
#guard pNeg.countRoot (3, false) = 6
#guard modelCount 3 ⟨#[[(0, false), (1, false)]]⟩ = 6

-- Internal negative edge: (¬(x ∧ y)) ∧ z over {x, y, z} has 3 models.
def pInner : Pog := ⟨3, #[.prod [(0, true), (1, true)], .prod [(3, false), (2, true)]]⟩
#guard pInner.countRoot (4, true) = 3

-- Constants: true is the empty product (2^V models), false its negation (0 models).
def pTrue : Pog := ⟨3, #[.prod []]⟩
#guard pTrue.countRoot (3, true) = 8
#guard pTrue.countRoot (3, false) = 0

-- x ∧ ¬x is excluded by WF.prod_disjoint: the supports of its arguments overlap.
def pBad : Pog := ⟨1, #[.prod [(0, true), (0, false)]]⟩
#guard pBad.supp 0 0 = true
#guard pBad.countRoot (1, true) = 1  -- the wrong count WF must prevent

-- Defining clauses in CPOG Table 2 order.
#guard pNeg.defs = [[(3, true), (0, false), (1, false)], [(3, false), (0, true)], [(3, false), (1, true)]]
