import Mathlib

set_option autoImplicit false



-- Exact rational arithmetic encoded over Int (no floats, no Real).
-- check : for x = k/10 (k ∈ ℤ), verify |x^2 - 2| ≤ 2 ↔ -2 ≤ x ≤ 2,
-- i.e. |k^2 - 200| ≤ 200 ↔ -20 ≤ k ≤ 20, on the sample set.
def checkK (k : Int) : Bool :=
  (decide (abs (k*k - 200) ≤ 200)) == (decide (-20 ≤ k ∧ k ≤ 20))

def sampleK : List Int := [-30, -20, -1, 0, 1, 20, 30]

def check_slice : Bool := sampleK.all checkK

theorem msl_fmz_erdos509_campaign_001_R002_L1  : check_slice = true := by decide

-- axiom footprint
#print axioms checkK
#print axioms sampleK
#print axioms check_slice
#print axioms msl_fmz_erdos509_campaign_001_R002_L1
