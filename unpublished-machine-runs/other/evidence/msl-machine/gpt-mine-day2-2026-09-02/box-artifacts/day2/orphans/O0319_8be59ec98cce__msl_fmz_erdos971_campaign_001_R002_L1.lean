import Mathlib

set_option autoImplicit false


def scaffold_check (n : Int) : Bool := decide (n * n ≥ 0) && decide ((n * n = 0) ↔ (n = 0))
def check_range : List Int := [-3, -2, -1, 0, 1, 2, 3]
def check_witness : Bool := check_range.all scaffold_check

theorem msl_fmz_erdos971_campaign_001_R002_L1  : check_witness = true := by decide

-- axiom footprint
#print axioms scaffold_check
#print axioms check_range
#print axioms check_witness
#print axioms msl_fmz_erdos971_campaign_001_R002_L1
