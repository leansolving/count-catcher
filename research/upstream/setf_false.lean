import LeanSAT.Upstream.ToStd

/-! Independent reproduction: the sorried lemma `Array.getElem?_setF'` is inconsistent.
Counterexample A = #[7], i = 3, j = 1, default = 9: `setF` pads positions 1 and 2 with the
default 9, so index 1 becomes readable after the update although it was out of bounds before. -/

example : (#[7] : Array Nat).setF 3 5 9 = #[7, 9, 9, 5] := by decide
example : ((#[7] : Array Nat).setF 3 5 9)[1]? = some 9 := by decide
example : (#[7] : Array Nat)[1]? = none := by decide

theorem getElem?_setF'_inconsistent : False := by
  have h : ((#[7] : Array Nat).setF 3 5 9)[1]? = (#[7] : Array Nat)[1]? :=
    Array.getElem?_setF' (#[7] : Array Nat) (i := 3) (j := 1) 5 9 (by decide)
  have h1 : ((#[7] : Array Nat).setF 3 5 9)[1]? = some 9 := by decide
  have h2 : (#[7] : Array Nat)[1]? = none := by decide
  rw [h1, h2] at h
  exact Option.noConfusion h

#print axioms getElem?_setF'_inconsistent
