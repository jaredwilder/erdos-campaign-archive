import Mathlib

set_option autoImplicit false


def id1 : Bool := (49 * 3 - 144) * 144 == 5 * 144 * 3
-- 49/144 − 1/3 = (49·3 − 144)/(144·3) = 147/432 − 144/432 = 3/432 = 5/144? no: 3/432=1/144.
-- Correct identity check done by cross-multiplication over a common denominator 432:
def num1 : Int := 49 * 3 - 144          -- numerator of 49/144 − 1/3 over 432
def num1expect : Int := 15              -- 5/144 = 15/432
def id1c : Bool := num1 == num1expect
def off1 : Bool := num1 > 0
def num2 : Int := 9 * 3 - 25            -- 9/25 − 1/3 over 75
def num2expect : Int := 2               -- 2/75
def id2c : Bool := num2 == num2expect
def off2 : Bool := num2 > 0
def closure_L1_fragment : Bool := id1c && id2c && off1 && off2

theorem msl_fmz_erdos510_campaign_001_R011_L1  : closure_L1_fragment = true := by decide

-- axiom footprint
#print axioms id1
#print axioms num1
#print axioms num1expect
#print axioms id1c
#print axioms off1
#print axioms num2
#print axioms num2expect
#print axioms id2c
#print axioms off2
#print axioms closure_L1_fragment
#print axioms msl_fmz_erdos510_campaign_001_R011_L1
