import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos985_campaign_001_R001_L1_a2r2  : (0 : ℚ) < 22 / 7 ∧ |((22 : ℚ) / 7)| < (3143 : ℚ) / 1000 := by
  constructor
  · norm_num
  · rw [abs_of_pos (by norm_num : (0 : ℚ) < 22 / 7)]
    norm_num

-- axiom footprint
#print axioms msl_fmz_erdos985_campaign_001_R001_L1_a2r2
