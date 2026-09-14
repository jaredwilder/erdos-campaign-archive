import Mathlib

set_option autoImplicit false


def ineq15 : Bool := decide ((15 : Nat) > 8)
def ineq51 : Bool := decide ((51 : Nat) > 32)
def ineq69 : Bool := decide ((69 : Nat) > 44)
def fracCheck : Bool := decide ((69 * 2 - 3 * 44 : Int) > 0)
def cert : Bool := ineq15 && ineq51 && ineq69 && fracCheck

theorem msl_fmz_erdos51_campaign_001_R007_L1_a2r2  : cert = true := by native_decide

-- axiom footprint
#print axioms ineq15
#print axioms ineq51
#print axioms ineq69
#print axioms fracCheck
#print axioms cert
#print axioms msl_fmz_erdos51_campaign_001_R007_L1_a2r2
