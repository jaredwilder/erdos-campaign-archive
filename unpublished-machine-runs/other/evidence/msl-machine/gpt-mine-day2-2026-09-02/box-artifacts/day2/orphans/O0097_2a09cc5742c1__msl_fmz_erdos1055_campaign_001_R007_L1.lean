import Mathlib

set_option autoImplicit false


-- Narrowed fragment: primality of 37/73/1021 by trial division against the
-- fixed, complete list of candidate divisors d with 2 ≤ d ≤ √n (n ≤ 1021, √1021 < 32),
-- plus the two exact integer inequalities. Fully explicit, no recursion, no underflow.
def divisors : List Nat := [2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]

def primeByDiv : Nat → Bool
  | n => (divisors.filter (fun d => d * d ≤ n)).all (fun d => n % d != 0)

def check_L1 : Bool :=
  primeByDiv 37 && primeByDiv 73 && primeByDiv 1021
  && 73^4 < 37^5
  && 73^6 < 1021^5

theorem msl_fmz_erdos1055_campaign_001_R007_L1  : check_L1 = true := by decide

-- axiom footprint
#print axioms divisors
#print axioms primeByDiv
#print axioms check_L1
#print axioms msl_fmz_erdos1055_campaign_001_R007_L1
