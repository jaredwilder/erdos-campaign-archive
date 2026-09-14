import Mathlib

set_option autoImplicit false


def reductionField : String := "none"
def reductionFieldIsNone : Bool := reductionField == "none"

theorem msl_fmz_erdos821_campaign_001_R005_L1  : reductionFieldIsNone = true := by decide

-- axiom footprint
#print axioms reductionField
#print axioms reductionFieldIsNone
#print axioms msl_fmz_erdos821_campaign_001_R005_L1
