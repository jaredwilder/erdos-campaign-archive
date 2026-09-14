import Mathlib

set_option autoImplicit false


def witnessOk (a : Nat) : Bool := (2^(2^a)) % (2^a) == 0
def check_range (N : Nat) : Bool := (List.range (N+1)).all (fun a => witnessOk a)

theorem msl_fmz_erdos479_campaign_001_R003_T1_a1r1  : check_range 64 = true := by decide

-- axiom footprint
#print axioms witnessOk
#print axioms check_range
#print axioms msl_fmz_erdos479_campaign_001_R003_T1_a1r1
