import Mathlib

set_option autoImplicit false



def tau (n : Nat) : Nat := n.divisors.length
def check (k : Nat) : Bool := tau (2^k - 1) >= tau k
def checkRange (m : Nat) : Bool := (List.range m).all check

theorem msl_fmz_erdos893_campaign_001_R005_L1  : checkRange 200 = true := by decide

-- axiom footprint
#print axioms tau
#print axioms check
#print axioms checkRange
#print axioms msl_fmz_erdos893_campaign_001_R005_L1
