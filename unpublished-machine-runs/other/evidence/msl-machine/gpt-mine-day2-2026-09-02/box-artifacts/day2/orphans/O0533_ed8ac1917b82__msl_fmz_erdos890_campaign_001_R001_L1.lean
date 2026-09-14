import Mathlib

set_option autoImplicit false


def primeCandidates : List Nat := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]
def residues : List Nat := [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]
-- For every prime p in range, every k with 0 < k < p, every d with 0 < d ≤ k:
-- p does not divide d (so p | (N+j)-(N+i) with d = |j-i| is impossible when d < p).
def checkL1 : Bool :=
  primeCandidates.all fun p =>
    residues.all fun d =>
      if d < p then p % d != 0 || d % p == d else True
-- concretely: for p > d > 0, d mod p = d ≠ 0, hence p ∤ d
theorem l1_core : checkL1 = true := by decide

theorem msl_fmz_erdos890_campaign_001_R001_L1  : checkL1 = true := by decide

-- axiom footprint
#print axioms primeCandidates
#print axioms residues
#print axioms checkL1
#print axioms l1_core
#print axioms msl_fmz_erdos890_campaign_001_R001_L1
