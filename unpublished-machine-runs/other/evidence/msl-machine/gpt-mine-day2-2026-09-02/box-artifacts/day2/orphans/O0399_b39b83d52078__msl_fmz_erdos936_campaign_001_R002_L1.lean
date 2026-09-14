import Mathlib

set_option autoImplicit false


def sq2 : Nat → Nat → Bool := fun k m => (2^(k+m) % 9) == (2^k % 9)
def check_periodicity : Bool := (List.range 6).all (fun k => sq2 k 6)
def check_tt : Bool := (List.range 12).all (fun n => ((2^n + 1) % 9 == 0) == (n % 6 == 3))

theorem msl_fmz_erdos936_campaign_001_R002_L1  : check_periodicity = true ∧ check_tt = true := by decide

-- axiom footprint
#print axioms sq2
#print axioms check_periodicity
#print axioms check_tt
#print axioms msl_fmz_erdos936_campaign_001_R002_L1
