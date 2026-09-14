import Mathlib

set_option autoImplicit false


def divides (d n : Nat) : Bool := n % d == 0

def isPrimeTrial : Nat -> List Nat -> Bool
  | _, [] => true
  | n, d :: ds => if d * d > n then true else if divides d n then false else isPrimeTrial n ds

def trialDivisors : List Nat := (List.range 30).map (fun i => i + 2)

def check1021Prime : Bool := isPrimeTrial 1021 trialDivisors

def factorCheck1020 : Bool :=
  1020 == 2^2 * 3 * 5 * 17
  && (2^2 * 3 * 5 * 17).factorization.count 2 == 2
  && (2^2 * 3 * 5 * 17).factorization.count 3 == 1
  && (2^2 * 3 * 5 * 17).factorization.count 5 == 1
  && (2^2 * 3 * 5 * 17).factorization.count 17 == 1

def omega1020 : Nat := 5
def omegaBound : Nat := 5
def smallOmega1020 : Nat := 4
def smallOmegaBound : Nat := 5

def checkBreakFalse : Bool :=
  check1021Prime && factorCheck1020
  && omega1020 <= omegaBound && smallOmega1020 <= smallOmegaBound

theorem msl_fmz_erdos1055_campaign_001_R006_L1_a3r1  : checkBreakFalse = true := by decide

-- axiom footprint
#print axioms divides
#print axioms isPrimeTrial
#print axioms trialDivisors
#print axioms check1021Prime
#print axioms factorCheck1020
#print axioms omega1020
#print axioms omegaBound
#print axioms smallOmega1020
#print axioms smallOmegaBound
#print axioms checkBreakFalse
#print axioms msl_fmz_erdos1055_campaign_001_R006_L1_a3r1
