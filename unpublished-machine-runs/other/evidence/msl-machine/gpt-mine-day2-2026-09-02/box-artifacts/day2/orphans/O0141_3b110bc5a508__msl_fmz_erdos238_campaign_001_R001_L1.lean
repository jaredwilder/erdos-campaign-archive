import Mathlib

set_option autoImplicit false


def smallPrimes : List Nat := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

def gapsEvenGe2 (ps : List Nat) : Bool :=
  match ps with
  | [] => true
  | p :: rest =>
    match rest with
    | [] => true
    | q :: _ => ((q - p) % 2 == 0) && ((q - p) >= 2) && gapsEvenGe2 rest

def check_gaps : Bool := gapsEvenGe2 smallPrimes

theorem msl_fmz_erdos238_campaign_001_R001_L1  : check_gaps = true := by decide

-- axiom footprint
#print axioms smallPrimes
#print axioms gapsEvenGe2
#print axioms check_gaps
#print axioms msl_fmz_erdos238_campaign_001_R001_L1
