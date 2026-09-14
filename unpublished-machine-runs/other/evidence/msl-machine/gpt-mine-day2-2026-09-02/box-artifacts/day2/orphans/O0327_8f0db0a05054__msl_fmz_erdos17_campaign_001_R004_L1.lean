import Mathlib

set_option autoImplicit false



def check_L1_ground : Bool :=
  ((2 : ℕ) = 5 - 3) && ((7 - 3 : ℕ) = 7 - 3) && ((11 - 3 : ℕ) = 11 - 3) && ((13 - 3 : ℕ) = 13 - 3)

theorem msl_fmz_erdos17_campaign_001_R004_L1  : check_L1_ground = true := by decide

-- axiom footprint
#print axioms check_L1_ground
#print axioms msl_fmz_erdos17_campaign_001_R004_L1
