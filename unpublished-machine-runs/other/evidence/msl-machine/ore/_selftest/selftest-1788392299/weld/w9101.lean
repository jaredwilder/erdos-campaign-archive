import Mathlib
set_option autoImplicit false
def checkW : Bool := decide (2 + 2 = 4)

theorem msl_fmz_erdos9101_campaign_001_R001_L1 : checkW = true := by decide
theorem w9101_orphan : checkW = true := by decide
#print axioms checkW
