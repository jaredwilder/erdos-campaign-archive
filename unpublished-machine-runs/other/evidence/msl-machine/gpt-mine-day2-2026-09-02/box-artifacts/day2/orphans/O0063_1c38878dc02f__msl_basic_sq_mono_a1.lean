import Mathlib

set_option autoImplicit false


set_option maxHeartbeats 800000

theorem msl_basic_sq_mono_a1 (x : ℚ) (y : ℚ) (hx : 0 ≤ x) (hy : 0 ≤ y) : x ^ 2 ≤ y ^ 2 ↔ x ≤ y := by
  rw [sq, sq]
  constructor
  · intro h
    refine not_lt.mp fun hc => h.not_lt ?_
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hc.le hy) (mul_lt_mul_of_pos_right hc (hy.trans_lt hc))
  · intro h
    exact (mul_le_mul_of_nonneg_right h hx).trans (mul_le_mul_of_nonneg_left h hy)

-- axiom footprint
#print axioms msl_basic_sq_mono_a1
