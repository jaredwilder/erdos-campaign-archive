import Mathlib

set_option autoImplicit false


def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else (List.range (n - 2 + 1)).all (fun d => d + 2 = n ∨ n % (d + 2) ≠ 0)

def primesInWindow (n : Nat) : List Nat :=
  (List.range (2*n/3 + 1)).filter (fun p => isPrime p && p > n/2)

def scaledSum (n scale : Nat) : Nat :=
  (primesInWindow n).foldl (fun acc p => acc + scale / p) 0

def checkL1 (n scale bound : Nat) : Bool :=
  scaledSum n scale ≤ bound

theorem msl_fmz_erdos726_campaign_001_R001_L1  : checkL1 1000 1000000 200000 = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms primesInWindow
#print axioms scaledSum
#print axioms checkL1
#print axioms msl_fmz_erdos726_campaign_001_R001_L1
