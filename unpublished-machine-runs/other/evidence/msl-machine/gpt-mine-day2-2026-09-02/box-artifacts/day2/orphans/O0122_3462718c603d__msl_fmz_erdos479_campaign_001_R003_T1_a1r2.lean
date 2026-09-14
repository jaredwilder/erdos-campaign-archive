import Mathlib

set_option autoImplicit false


def witnessOk (a : Nat) : Bool := (2^(2^a)) % (2^a) == 0
def check_range : Bool := (List.range 7).all (fun a => witnessOk a)

theorem msl_fmz_erdos479_campaign_001_R003_T1_a1r2  : check_range = true := by decide

-- axiom footprint
#print axioms witnessOk
#print axioms check_range
#print axioms msl_fmz_erdos479_campaign_001_R003_T1_a1r2
