import Mathlib

set_option autoImplicit false


def ceilDiv (n p : Nat) : Nat := (n + p - 1) / p

def primes100 : List Nat :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]

def doubleCountSum100 : Nat :=
  primes100.foldl (fun acc p => acc + ceilDiv 100 p) 0

def checkLemmaL1 : Bool :=
  doubleCountSum100 == 194 && doubleCountSum100 < 200

theorem msl_fmz_erdos689_campaign_001_R004_L1  : checkLemmaL1 = true := by decide

-- axiom footprint
#print axioms ceilDiv
#print axioms primes100
#print axioms doubleCountSum100
#print axioms checkLemmaL1
#print axioms msl_fmz_erdos689_campaign_001_R004_L1
