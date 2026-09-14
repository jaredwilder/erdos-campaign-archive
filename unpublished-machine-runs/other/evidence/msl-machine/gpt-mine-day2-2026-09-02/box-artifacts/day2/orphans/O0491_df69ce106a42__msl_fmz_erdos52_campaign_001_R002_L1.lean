import Mathlib

set_option autoImplicit false


-- Narrowed fragment: only Nat arithmetic, fully explicit setEnumeration, no closures over Int, no map lambdas.
def sumsetA : List Nat := [0,1,2,3,4,5,6,1,2,3,4,5,6,7,2,3,4,5,6,7,8,4,5,6,7,8]
-- A = [0,1,2,3,4]; A+A enumerated explicitly above.
def prodsetA : List Nat := [0,0,0,0,0,0,1,2,3,4,0,2,4,6,8,0,3,6,9,12,0,4,8,12,16]
-- A*A enumerated explicitly above.
def sumsetD : List Nat := [0,2,4,6,8,2,4,6,8,10,4,6,8,10,12,6,8,10,12,14,8,10,12,14,16]
-- 2A = [0,2,4,6,8]; 2A+2A enumerated explicitly above.
def nodupCount : List Nat → Nat
  | [] => 0
  | x :: xs => (if xs.contains x then 0 else 1) + nodupCount xs
def sumCardA : Nat := nodupCount sumsetA
def prodCardA : Nat := nodupCount prodsetA
def sumCardD : Nat := nodupCount sumsetD
def checkFour : Bool :=
  (sumCardA ≥ 9) && (prodCardA ≥ 9) && (sumCardD ≥ 9) && (prodCardD ≥ 5)
def prodCardD : Nat := nodupCount [0,4,16,8,0,16,32,4,0,8,16,24,0,12,24,0,16,32,0,0,16,32,0,8,16]
-- 2A·2A enumerated explicitly above.

theorem msl_fmz_erdos52_campaign_001_R002_L1  : checkFour = true := by decide

-- axiom footprint
#print axioms sumsetA
#print axioms prodsetA
#print axioms sumsetD
#print axioms nodupCount
#print axioms sumCardA
#print axioms prodCardA
#print axioms sumCardD
#print axioms checkFour
#print axioms prodCardD
#print axioms msl_fmz_erdos52_campaign_001_R002_L1
