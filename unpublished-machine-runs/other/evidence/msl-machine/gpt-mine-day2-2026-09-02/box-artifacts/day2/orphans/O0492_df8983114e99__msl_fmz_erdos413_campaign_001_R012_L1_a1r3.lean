import Mathlib

set_option autoImplicit false


def omega (n : Nat) : Nat := (Nat.factorization n).support.length

def ratioLE1 (n m : Nat) : Bool := n - m <= omega m

def checkRange (N : Nat) : Bool :=
  (List.range (N - 2)).all fun i =>
    let n := i + 3
    (List.range n).all fun m => ratioLE1 n m

def checkAttainment : Bool := ratioLE1 5 4 && omega 4 == 1

theorem msl_fmz_erdos413_campaign_001_R012_L1_a1r3  : checkRange 50 = true && checkAttainment = true := by decide

-- axiom footprint
#print axioms omega
#print axioms ratioLE1
#print axioms checkRange
#print axioms checkAttainment
#print axioms msl_fmz_erdos413_campaign_001_R012_L1_a1r3
