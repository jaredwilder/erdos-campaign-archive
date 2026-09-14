/-
  C5 avoidance: {1, 3, 9, 27, 81, 243, 729, 2187} (powers of 3, size 8)
  Relation: 5th finite difference coefficients [1, -5, 10, -10, 5, -1]
  For any 6 chosen elements a < b < c < d < e < f from the set:
    a - 5b + 10c - 10d + 5e - f ≠ 0
  C(8,6) = 28 six-tuples. All nonzero. Proven by CP-SAT, now formalized.
  No Mathlib — pure Lean 4.
-/

def c5 (a b c d e f : Int) : Int := a - 5*b + 10*c - 10*d + 5*e - f

theorem c5_powers_of_3_avoidance :
  -- All 28 ordered 6-element subsets of {1, 3, 9, 27, 81, 243, 729, 2187}
  c5 1 3 9 27 81 243 ≠ 0 ∧
  c5 1 3 9 27 81 729 ≠ 0 ∧
  c5 1 3 9 27 81 2187 ≠ 0 ∧
  c5 1 3 9 27 243 729 ≠ 0 ∧
  c5 1 3 9 27 243 2187 ≠ 0 ∧
  c5 1 3 9 27 729 2187 ≠ 0 ∧
  c5 1 3 9 81 243 729 ≠ 0 ∧
  c5 1 3 9 81 243 2187 ≠ 0 ∧
  c5 1 3 9 81 729 2187 ≠ 0 ∧
  c5 1 3 9 243 729 2187 ≠ 0 ∧
  c5 1 3 27 81 243 729 ≠ 0 ∧
  c5 1 3 27 81 243 2187 ≠ 0 ∧
  c5 1 3 27 81 729 2187 ≠ 0 ∧
  c5 1 3 27 243 729 2187 ≠ 0 ∧
  c5 1 3 81 243 729 2187 ≠ 0 ∧
  c5 1 9 27 81 243 729 ≠ 0 ∧
  c5 1 9 27 81 243 2187 ≠ 0 ∧
  c5 1 9 27 81 729 2187 ≠ 0 ∧
  c5 1 9 27 243 729 2187 ≠ 0 ∧
  c5 1 9 81 243 729 2187 ≠ 0 ∧
  c5 1 27 81 243 729 2187 ≠ 0 ∧
  c5 3 9 27 81 243 729 ≠ 0 ∧
  c5 3 9 27 81 243 2187 ≠ 0 ∧
  c5 3 9 27 81 729 2187 ≠ 0 ∧
  c5 3 9 27 243 729 2187 ≠ 0 ∧
  c5 3 9 81 243 729 2187 ≠ 0 ∧
  c5 3 27 81 243 729 2187 ≠ 0 ∧
  c5 9 27 81 243 729 2187 ≠ 0 := by native_decide
