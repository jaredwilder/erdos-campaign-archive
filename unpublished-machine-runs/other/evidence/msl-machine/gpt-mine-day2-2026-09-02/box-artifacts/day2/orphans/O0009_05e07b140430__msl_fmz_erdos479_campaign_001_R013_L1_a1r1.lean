import Mathlib

set_option autoImplicit false


def primes40 : List Nat := [2,3,5,7,11,13,17,19,23,29,31,37]
def checkPrime (p : Nat) : Bool := (Nat.pow 2 p) % p == 2
def checkAll : Bool := primes40.all checkPrime

theorem msl_fmz_erdos479_campaign_001_R013_L1_a1r1  : checkAll = true := by decide

-- axiom footprint
#print axioms primes40
#print axioms checkPrime
#print axioms checkAll
#print axioms msl_fmz_erdos479_campaign_001_R013_L1_a1r1
