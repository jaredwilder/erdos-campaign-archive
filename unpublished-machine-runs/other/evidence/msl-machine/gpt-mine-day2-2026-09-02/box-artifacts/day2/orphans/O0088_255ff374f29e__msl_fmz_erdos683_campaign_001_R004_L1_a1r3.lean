import Mathlib

set_option autoImplicit false


def check_cap_refuted : Bool := (5^120905 < 7^100000)

theorem msl_fmz_erdos683_campaign_001_R004_L1_a1r3  : check_cap_refuted = true := by native_decide

-- axiom footprint
#print axioms check_cap_refuted
#print axioms msl_fmz_erdos683_campaign_001_R004_L1_a1r3
