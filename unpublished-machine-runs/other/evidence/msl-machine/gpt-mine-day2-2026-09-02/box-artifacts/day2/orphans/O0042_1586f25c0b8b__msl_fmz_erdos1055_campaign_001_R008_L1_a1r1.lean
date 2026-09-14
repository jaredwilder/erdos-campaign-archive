import Mathlib

set_option autoImplicit false


def isPrime : Nat → Bool
  | 0 => false | 1 => false | 2 => true
  | n => Id.run do
    let mut ok := true
    let mut d := 2
    while d*d <= n do
      if n % d == 0 then ok := false
      d := d + 1
    return ok

def is23Smooth : Nat → Bool
  | 0 => false
  | 1 => true
  | n =>
    let rec strip (m k : Nat) : Nat :=
      if m % 2 == 0 then strip (m/2) k else m
    def strip3 (m : Nat) : Nat :=
      if m % 3 == 0 then strip3 (m/3) else m
    strip3 (strip n 0) == 1

def class1Candidate (p : Nat) : Bool := isPrime p && is23Smooth (p+1)

def check : Bool :=
  class1Candidate 2 && class1Candidate 3 && class1Candidate 7 && class1Candidate 23

theorem msl_fmz_erdos1055_campaign_001_R008_L1_a1r1  : check = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms is23Smooth
#print axioms class1Candidate
#print axioms check
#print axioms msl_fmz_erdos1055_campaign_001_R008_L1_a1r1
