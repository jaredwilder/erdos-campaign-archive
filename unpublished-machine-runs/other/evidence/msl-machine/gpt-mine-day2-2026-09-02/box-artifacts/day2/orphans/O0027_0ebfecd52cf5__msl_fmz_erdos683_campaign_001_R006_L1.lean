import Mathlib

set_option autoImplicit false


def check : Bool := (5 ^ 3 == 125) && (3 ^ 13 == 1594323) && (5 ^ 3 <= 3 ^ (10 + 3))

theorem msl_fmz_erdos683_campaign_001_R006_L1  : check = true := by decide

-- axiom footprint
#print axioms check
#print axioms msl_fmz_erdos683_campaign_001_R006_L1
