import Mathlib

set_option autoImplicit false


def divisorsAllFail : Nat -> Nat -> Nat -> Bool | _, _, 0 => True | n, b, k => (n % k != 0) && divisorsAllFail n b (k-1)

def check1021prime : Bool := divisorsAllFail 1021 31 31

def check1020 : Bool :=
  (2 * 2 * 3 * 5 * 17 == 1020)
  && (1020 / 2 == 510) && (510 / 2 == 255) && (255 / 3 == 85)
  && (85 / 5 == 17) && (17 / 17 == 1)
  && (17 % 2 != 0) && (17 % 3 != 0) && (17 % 5 != 0) && (17 % 7 != 0)
  && (17 % 11 != 0) && (17 % 13 != 0)

def checkPrime7 : Bool := (7 % 2 != 0) && (7 % 3 != 0) && (2*2 > 7)

def checkPrime73 : Bool :=
  (73 % 2 != 0) && (73 % 3 != 0) && (73 % 5 != 0) && (73 % 7 != 0)
  && (8*8 > 73)

def check1022 : Bool :=
  (2 * 7 * 73 == 1022) && (1022 / 2 == 511) && (511 / 7 == 73)
  && (73 / 73 == 1) && checkPrime7 && checkPrime73

def check1021Break : Bool :=
  check1021prime && check1020 && check1022

theorem msl_fmz_erdos1055_campaign_001_R006_L1  : check1021Break = true := by decide

-- axiom footprint
#print axioms divisorsAllFail
#print axioms check1021prime
#print axioms check1020
#print axioms checkPrime7
#print axioms checkPrime73
#print axioms check1022
#print axioms check1021Break
#print axioms msl_fmz_erdos1055_campaign_001_R006_L1
