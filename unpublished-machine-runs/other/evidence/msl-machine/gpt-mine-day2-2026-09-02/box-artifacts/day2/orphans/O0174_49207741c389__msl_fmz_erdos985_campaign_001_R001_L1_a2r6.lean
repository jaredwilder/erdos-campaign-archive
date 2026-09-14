import Mathlib

set_option autoImplicit false



def L1 : Prop := (22 : ℕ) * 1000 < 7 * 3143

theorem msl_fmz_erdos985_campaign_001_R001_L1_a2r6  : L1 := by decide

-- axiom footprint
#print axioms L1
#print axioms msl_fmz_erdos985_campaign_001_R001_L1_a2r6
