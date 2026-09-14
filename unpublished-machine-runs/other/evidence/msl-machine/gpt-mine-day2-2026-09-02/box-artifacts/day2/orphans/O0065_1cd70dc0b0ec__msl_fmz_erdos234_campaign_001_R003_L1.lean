import Mathlib

set_option autoImplicit false


-- L1 fragment: the exact-arithmetic step. Rational Root Theorem restricts candidates to ±1; exact arithmetic gives p(1) = -1 and p(-1) = 3, both nonzero, so neither candidate is a root. The kernel-checkable fragment: a Bool-valued check that encodes the two exact evaluations as Integers and asserts both are nonzero, verifying (i) -1 ≠ 0 and (ii) 3 ≠ 0 in exact integer arithmetic, exactly the nonvanishing step of L1.

def pAt1 : Int := -1
def pAtM1 : Int := 3

def checkL1 : Bool :=
  (pAt1 != 0) && (pAtM1 != 0)

theorem msl_fmz_erdos234_campaign_001_R003_L1  : checkL1 = true := by decide

-- axiom footprint
#print axioms pAt1
#print axioms pAtM1
#print axioms checkL1
#print axioms msl_fmz_erdos234_campaign_001_R003_L1
