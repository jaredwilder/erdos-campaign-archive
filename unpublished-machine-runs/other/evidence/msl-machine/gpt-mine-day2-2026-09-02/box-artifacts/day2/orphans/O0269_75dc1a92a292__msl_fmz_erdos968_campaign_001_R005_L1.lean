import Mathlib

set_option autoImplicit false


def isPrime : Nat → Bool
  | 0 => false | 1 => false
  | n => (List.range (n-2)).all fun k => n % (k+2) != 0

-- Concrete instance of the gap event in L1: with p_30 = 113 and p_31 = 127
-- (the 30th and 31st primes), the gap 127 − 113 = 14 satisfies
-- p_31 − p_30 > p_30 / 30, i.e. 30 * 14 = 420 > 113.
def witnessCheck : Bool :=
  isPrime 113 && isPrime 127 && (127 - 113 = 14) && (30 * (127 - 113) > 113)

theorem msl_fmz_erdos968_campaign_001_R005_L1  : witnessCheck = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms witnessCheck
#print axioms msl_fmz_erdos968_campaign_001_R005_L1
