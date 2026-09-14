import Mathlib

set_option autoImplicit false

/-- One-step deviation identity underlying the Pass-3 #243 reduction. -/
theorem erdos243_deviation_step
    (a b d : ℚ)
    (ha : a ≠ 0) (ha1 : a - 1 ≠ 0) (hb1 : b - 1 ≠ 0)
    (h : b - 1 = a * (a - 1) + d) :
    1 / a =
      1 / (a - 1) - 1 / (b - 1) - d / (a * (a - 1) * (b - 1)) := by
  field_simp [ha, ha1, hb1]
  nlinarith [h]

-- axiom footprint
#print axioms erdos243_deviation_step
