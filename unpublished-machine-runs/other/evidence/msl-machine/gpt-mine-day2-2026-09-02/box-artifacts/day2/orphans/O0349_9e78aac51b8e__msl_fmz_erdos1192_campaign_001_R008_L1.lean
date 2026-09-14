import Mathlib

set_option autoImplicit false


def check_r2 : Bool := (1009999 : Nat) * 100 <= 101 * 1000000
def check_r3 : Bool := (6299999 : Nat) * 10 <= 63 * 1000000
def check_r4 : Bool := (9799999 : Nat) * 5 <= 49 * 1000000
def check_scope : Bool := check_r2 && check_r3 && check_r4

theorem msl_fmz_erdos1192_campaign_001_R008_L1  : check_scope = true := by decide

-- axiom footprint
#print axioms check_r2
#print axioms check_r3
#print axioms check_r4
#print axioms check_scope
#print axioms msl_fmz_erdos1192_campaign_001_R008_L1
