import Mathlib

set_option autoImplicit false



def isSqf (k : Nat) : Bool := if k = 0 then false else (List.range k).all (fun d => let e := d + 2; k % (e * e) != 0)

def check (n : Nat) : Bool := ((List.range 8).filter (fun l => 2^l < n)).any (fun l => isSqf (n - 2^l))

theorem msl_fmz_erdos11_campaign_001_R007_L1_a2r1  : (List.range 127).all (fun i => check (2*i+3)) = true ∧ check 185 = true ∧ 185 = 57 + 2^7 ∧ isSqf 57 = true := by decide

-- axiom footprint
#print axioms isSqf
#print axioms check
#print axioms msl_fmz_erdos11_campaign_001_R007_L1_a2r1
