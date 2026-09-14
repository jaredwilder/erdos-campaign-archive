import Mathlib

set_option autoImplicit false


def divides (d n : Nat) : Bool := n % d == 0

def isPrimeTrial : Nat -> List Nat -> Bool
  | _, [] => true
  | n, d :: ds => if d * d > n then true else if divides d n then false else isPrimeTrial n ds

def trialDivisors : List Nat := (List.range 30).map (fun i => i + 2)

def check1021Prime : Bool := isPrimeTrial 1021 trialDivisors

def check1020Factorization : Bool :=
  2^2 * 3 * 5 * 17 == 1020
  && 1020 % 2 == 0 && 1020 % 3 == 0 && 1020 % 5 == 0 && 1020 % 17 == 0
  && 1020 % 7 != 0 && 1020 % 11 != 0 && 1020 % 13 != 0 && 1020 % 19 != 0
  && 1020 % 23 != 0 && 1020 % 29 != 0 && 1020 % 31 != 0

def checkBreakFalse : Bool := check1021Prime && check1020Factorization

theorem msl_fmz_erdos1055_campaign_001_R006_L1_a3r2  : checkBreakFalse = true := by decide

-- axiom footprint
#print axioms divides
#print axioms isPrimeTrial
#print axioms trialDivisors
#print axioms check1021Prime
#print axioms check1020Factorization
#print axioms checkBreakFalse
#print axioms msl_fmz_erdos1055_campaign_001_R006_L1_a3r2
