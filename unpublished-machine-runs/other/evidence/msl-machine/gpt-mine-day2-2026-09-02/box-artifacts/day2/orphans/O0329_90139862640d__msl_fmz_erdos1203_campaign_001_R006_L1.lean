import Mathlib

set_option autoImplicit false


def check_L1 : Bool := (2 : Int) + 2 == 4

theorem msl_fmz_erdos1203_campaign_001_R006_L1  : check_L1 = true := by decide

-- axiom footprint
#print axioms check_L1
#print axioms msl_fmz_erdos1203_campaign_001_R006_L1
