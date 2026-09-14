import Mathlib

set_option autoImplicit false


def numer : Int := 355 * 33102 - 103993 * 113
def checkBound : Bool := numer > 0 && numer * 10000 < 113 * 33102

theorem msl_fmz_erdos247_campaign_001_R006_L1  : checkBound = true := by decide

-- axiom footprint
#print axioms numer
#print axioms checkBound
#print axioms msl_fmz_erdos247_campaign_001_R006_L1
