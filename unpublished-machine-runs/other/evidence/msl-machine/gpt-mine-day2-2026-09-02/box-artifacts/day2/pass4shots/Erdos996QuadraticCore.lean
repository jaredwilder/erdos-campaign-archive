import Mathlib

set_option autoImplicit false

/-- Reusable quadratic atom: 2xy ≤ x²+y². -/
theorem erdos996_two_mul_le_sq_add_sq (x y : ℚ) :
    2 * x * y ≤ x ^ 2 + y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

-- axiom footprint
#print axioms erdos996_two_mul_le_sq_add_sq
