import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos985_campaign_001_R001_L1_a2r1  : |((22 : ℚ) / 7)| < (3143 : ℚ) / 1000 := by
  have h : (0 : ℚ) < 22 / 7 := by
    norm_num
  rw [abs_of_pos h]
  norm_num

-- axiom footprint
#print axioms msl_fmz_erdos985_campaign_001_R001_L1_a2r1
