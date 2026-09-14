import Mathlib

set_option autoImplicit false



def L1 : Prop := |(22 : ℚ) / 7| < (3143 : ℚ) / 1000

theorem msl_fmz_erdos985_campaign_001_R001_L1_a2r3  : L1 := by
  norm_num [L1, abs_of_pos]

-- axiom footprint
#print axioms L1
#print axioms msl_fmz_erdos985_campaign_001_R001_L1_a2r3
