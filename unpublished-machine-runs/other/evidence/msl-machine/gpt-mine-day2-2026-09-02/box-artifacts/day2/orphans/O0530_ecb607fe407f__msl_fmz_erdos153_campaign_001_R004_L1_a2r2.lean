import Mathlib

set_option autoImplicit false


-- Explicit pair sums of A = [0,1,4,10] over pairs i<=j, listed literally
-- (0+0,0+1,0+4,0+10,1+1,1+4,1+10,4+4,4+10,10+10)
def sumsA : List Nat := [0, 1, 4, 10, 2, 5, 11, 8, 14, 20]

def sortedSumsA : List Nat := [0, 1, 2, 4, 5, 8, 10, 11, 14, 20]

def allDistinct : Bool :=
  sumsA.length == (sumsA.eraseDups).length

def tIsTen : Bool := sumsA.length == 10

def pairsFormula : Bool := 4 * (4 + 1) / 2 == 10

def checkL1 : Bool := allDistinct && tIsTen && pairsFormula

theorem msl_fmz_erdos153_campaign_001_R004_L1_a2r2  : checkL1 = true ∧ sumsA.length = 10 ∧ (sumsA.eraseDups).length = 10 := by decide

-- axiom footprint
#print axioms sumsA
#print axioms sortedSumsA
#print axioms allDistinct
#print axioms tIsTen
#print axioms pairsFormula
#print axioms checkL1
#print axioms msl_fmz_erdos153_campaign_001_R004_L1_a2r2
