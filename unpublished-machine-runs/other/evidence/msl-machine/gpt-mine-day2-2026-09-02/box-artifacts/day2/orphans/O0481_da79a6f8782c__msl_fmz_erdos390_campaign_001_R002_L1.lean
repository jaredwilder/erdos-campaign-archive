import Mathlib

set_option autoImplicit false


def prods : List Nat → List Nat
  | [] => [1]
  | x :: xs => prods xs ++ (prods xs).map (fun p => p * x)

-- n = 6: 6! = 720, p*(6) = 5 (largest prime ≤ 6), 2*p* = 10.
-- Lower bound: any factorization 720 = a1 < ... < ak = m with all ai > 6 and m ≤ 9
-- would need parts from [7, 8, 9] alone; enumerate all subsequence products.
def noFactorizationWithMLe9 : Bool :=
  !((prods [7, 8, 9]).contains 720)

-- Tightness witness: 720 = 8 · 9 · 10 with 6 < 8 < 9 < 10 = m = 2 * p*(6).
def witnessProduct : Nat := 8 * 9 * 10
def tightWitness : Bool :=
  (witnessProduct == 720) && (10 == 2 * 5)

def lemmaL1check : Bool :=
  noFactorizationWithMLe9 && tightWitness

theorem msl_fmz_erdos390_campaign_001_R002_L1  : lemmaL1check = true := by decide

-- axiom footprint
#print axioms prods
#print axioms noFactorizationWithMLe9
#print axioms witnessProduct
#print axioms tightWitness
#print axioms lemmaL1check
#print axioms msl_fmz_erdos390_campaign_001_R002_L1
