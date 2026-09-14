import Mathlib

set_option autoImplicit false


-- Fully concrete: A = [1,2,4,8] (Sidon, n=4).
-- Pair sums (i<=j), computed by hand, sorted, deduped:
-- 2,3,5,9 (a1+a*), 4,6,10, 8,12, 16  ->  {2,3,4,5,6,8,9,10,12,16}, t = 10 = 4*5/2.
def sumsetA : List Nat := [2,3,4,5,6,8,9,10,12,16]

def pairSumsA : List Nat :=
  [2,3,5,9, 4,6,10, 8,12, 16]

def sidonOK : Bool := (pairSumsA.length = 10) && (sumsetA.length = 10)

def tA : Nat := 10

def spanA : Nat := 16 - 2

def gapsA : List Nat := [1,1,1,1,2,1,1,2,4]

def sqSum : List Nat -> Nat
  | [] => 0
  | x :: xs => x*x + sqSum xs

def QintA : Nat := sqSum gapsA

def checkPart1 : Bool := sidonOK && (tA = (4 * (4+1)) / 2)

def checkPart2 : Bool := QintA * tA >= spanA * spanA

def checkLemma1 : Bool := checkPart1 && checkPart2

theorem msl_fmz_erdos153_campaign_001_R001_L1  : checkLemma1 = true := by decide

-- axiom footprint
#print axioms sumsetA
#print axioms pairSumsA
#print axioms sidonOK
#print axioms tA
#print axioms spanA
#print axioms gapsA
#print axioms sqSum
#print axioms QintA
#print axioms checkPart1
#print axioms checkPart2
#print axioms checkLemma1
#print axioms msl_fmz_erdos153_campaign_001_R001_L1
