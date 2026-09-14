import Mathlib

set_option autoImplicit false


def r1 : Q := 49/144 - 1/3
def r2 : Q := 9/25 - 1/3
def checkL1 : Bool :=
  r1 = 5/144 ∧ r1 > 0 ∧ r2 = 2/75 ∧ r2 > 0

theorem msl_fmz_erdos510_campaign_001_R011_L1_a1r1  : checkL1 = true := by decide

-- axiom footprint
#print axioms r1
#print axioms r2
#print axioms checkL1
#print axioms msl_fmz_erdos510_campaign_001_R011_L1_a1r1
