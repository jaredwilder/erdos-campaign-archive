import Mathlib

set_option autoImplicit false


def mod11 (x : Nat) : Nat := x % 11
def checkL1 : Bool :=
  let prod := 4 * 5 * 6
  prod = 120 && mod11 prod = 10 && mod11 prod != 1

theorem msl_fmz_erdos445_campaign_001_R003_L1  : checkL1 = true := by decide

-- axiom footprint
#print axioms mod11
#print axioms checkL1
#print axioms msl_fmz_erdos445_campaign_001_R003_L1
