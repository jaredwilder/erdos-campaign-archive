import Mathlib

set_option autoImplicit false


def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

def sumFacts (S : List Nat) : Nat := S.map fact |>.sum

def checkL1 : Bool :=
  sumFacts [1, 4] == 25 && sumFacts [2, 3] == 8

theorem w25 : 25 = fact 1 + fact 4 := by decide
theorem w8 : 8 = fact 2 + fact 3 := by decide

theorem msl_fmz_erdos1108_campaign_001_R001_L1  : checkL1 = true := by decide

-- axiom footprint
#print axioms fact
#print axioms sumFacts
#print axioms checkL1
#print axioms w25
#print axioms w8
#print axioms msl_fmz_erdos1108_campaign_001_R001_L1
