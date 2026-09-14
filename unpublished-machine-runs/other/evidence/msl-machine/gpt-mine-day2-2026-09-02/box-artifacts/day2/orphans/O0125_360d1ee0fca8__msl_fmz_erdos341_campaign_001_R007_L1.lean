import Mathlib

set_option autoImplicit false


def k : Nat := 5
def a : Nat -> Nat := fun n => n + k * 2^k
-- Finite core of L1: on the block n in [2^k, 2^k+1) (i.e. n = 2^k ... 2^k+2^k-1),
-- the family a_n = n + k*2^k is strictly increasing with unit gaps, and
-- a_n / 2^k attains the exact value 1+k at n = 2^k (limsup >= 1+k for this block family).
def unitGaps : Bool :=
  (List.range (2^k - 1)).all (fun i => a (2^k + i + 1) - a (2^k + i) == 1)
def strictlyIncreasing : Bool :=
  (List.range (2^k - 1)).all (fun i => a (2^k + i) < a (2^k + i + 1))
def ratioExact : Bool :=
  a (2^k) == (1 + k) * 2^k
def check_L1_core : Bool := unitGaps && strictlyIncreasing && ratioExact

theorem msl_fmz_erdos341_campaign_001_R007_L1  : check_L1_core = true := by decide

-- axiom footprint
#print axioms k
#print axioms a
#print axioms unitGaps
#print axioms strictlyIncreasing
#print axioms ratioExact
#print axioms check_L1_core
#print axioms msl_fmz_erdos341_campaign_001_R007_L1
