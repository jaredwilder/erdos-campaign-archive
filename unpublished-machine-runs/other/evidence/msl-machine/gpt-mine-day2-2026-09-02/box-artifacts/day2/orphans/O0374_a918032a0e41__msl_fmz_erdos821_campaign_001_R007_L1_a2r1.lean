import Mathlib

set_option autoImplicit false



def totientCheck (m : Nat) : Bool := Nat.Even (Nat.totient m)

def rangeCheck : Bool := (List.range 22).all (fun k => totientCheck (k + 3))

theorem msl_fmz_erdos821_campaign_001_R007_L1_a2r1  : rangeCheck = true := by decide

-- axiom footprint
#print axioms totientCheck
#print axioms rangeCheck
#print axioms msl_fmz_erdos821_campaign_001_R007_L1_a2r1
