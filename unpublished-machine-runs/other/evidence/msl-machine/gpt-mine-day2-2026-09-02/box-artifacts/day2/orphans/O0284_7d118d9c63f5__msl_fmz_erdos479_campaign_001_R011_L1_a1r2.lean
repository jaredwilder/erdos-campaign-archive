import Mathlib

set_option autoImplicit false


def witnessCheck (p : Nat) : Bool := (Nat.pow 2 (3*p) - 8) % (3*p) == 0

def primes : List Nat := [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]

def checkRange : Bool := primes.all witnessCheck

theorem msl_fmz_erdos479_campaign_001_R011_L1_a1r2  : checkRange = true := by native_decide

-- axiom footprint
#print axioms witnessCheck
#print axioms primes
#print axioms checkRange
#print axioms msl_fmz_erdos479_campaign_001_R011_L1_a1r2
