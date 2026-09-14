import Mathlib

-- @category test

/-- Source question: "Determine whether the natural-number equality $2 + 2 = 4$ holds." -/
theorem JSpaceCanonical.knownTrue : (2 : Nat) + 2 = 4 := by
  norm_num

#print axioms JSpaceCanonical.knownTrue
