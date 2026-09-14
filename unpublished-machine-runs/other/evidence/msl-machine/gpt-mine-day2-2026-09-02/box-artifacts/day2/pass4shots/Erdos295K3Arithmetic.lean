import Mathlib

set_option autoImplicit false

/-- Exact arithmetic anchors for the #295 k(3)=5 finite result. -/
theorem erdos295_four_term_ceiling :
    (1 / 3 + 1 / 4 + 1 / 5 + 1 / 6 : ℚ) = 57 / 60 := by
  norm_num

theorem erdos295_four_term_ceiling_lt_one :
    (57 / 60 : ℚ) < 1 := by
  norm_num

theorem erdos295_five_term_witness :
    (1 / 3 + 1 / 4 + 1 / 5 + 1 / 6 + 1 / 20 : ℚ) = 1 := by
  norm_num

-- axiom footprint
#print axioms erdos295_four_term_ceiling
#print axioms erdos295_four_term_ceiling_lt_one
#print axioms erdos295_five_term_witness
