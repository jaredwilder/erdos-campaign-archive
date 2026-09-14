import Mathlib

set_option autoImplicit false



def phi (m : Nat) : Nat := (List.range (m+1)).filter (fun k => k ≥ 1 ∧ Nat.Coprime k m) |>.length

def evenPhi (m : Nat) : Bool := phi m % 2 == 0

def rangeCheck : Bool := [3,4,5,6,7,8,9,10,11,12].all evenPhi

theorem msl_fmz_erdos821_campaign_001_R007_L1_a2r2  : rangeCheck = true := by decide

-- axiom footprint
#print axioms phi
#print axioms evenPhi
#print axioms rangeCheck
#print axioms msl_fmz_erdos821_campaign_001_R007_L1_a2r2
