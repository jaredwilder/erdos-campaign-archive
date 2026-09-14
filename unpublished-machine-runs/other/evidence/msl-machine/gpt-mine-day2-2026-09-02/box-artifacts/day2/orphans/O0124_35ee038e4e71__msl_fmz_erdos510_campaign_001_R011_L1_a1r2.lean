import Mathlib

set_option autoImplicit false


def d1 : Rat := 49/144 - 1/3
def d2 : Rat := 9/25 - 1/3
def checkL1 : Bool :=
  d1 = 1/144 ∧ d1 > 0 ∧ d2 = 2/75 ∧ d2 > 0

theorem msl_fmz_erdos510_campaign_001_R011_L1_a1r2  : checkL1 = true := by decide

-- axiom footprint
#print axioms d1
#print axioms d2
#print axioms checkL1
#print axioms msl_fmz_erdos510_campaign_001_R011_L1_a1r2
