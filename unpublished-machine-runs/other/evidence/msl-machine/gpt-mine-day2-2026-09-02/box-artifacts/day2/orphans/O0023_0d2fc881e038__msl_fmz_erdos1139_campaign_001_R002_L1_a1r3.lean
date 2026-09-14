import Mathlib

set_option autoImplicit false



abbrev L1Statement : Prop := ((1 : ℚ) / 3 + (1 : ℚ) / 6 = (1 : ℚ) / 2) ∧ ((1 : ℚ) / 2 < (1 : ℚ))

theorem msl_fmz_erdos1139_campaign_001_R002_L1_a1r3  : L1Statement := by
  unfold L1Statement
  norm_num

-- axiom footprint
#print axioms L1Statement
#print axioms msl_fmz_erdos1139_campaign_001_R002_L1_a1r3
