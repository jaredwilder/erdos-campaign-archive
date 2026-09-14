import Mathlib

-- @category test

/-- Source question: "Determine whether the natural-number equality $2 + 2 = 5$ holds." -/
theorem JSpaceCanonical.knownFalse : ¬ ((2 : Nat) + 2 = 5) := by
  norm_num

#print axioms JSpaceCanonical.knownFalse
