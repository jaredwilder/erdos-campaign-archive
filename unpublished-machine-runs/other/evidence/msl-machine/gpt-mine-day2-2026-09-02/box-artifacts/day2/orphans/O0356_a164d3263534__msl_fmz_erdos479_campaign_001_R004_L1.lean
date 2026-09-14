import Mathlib

set_option autoImplicit false


def primes : List Nat := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
def checkPair (j p : Nat) : Bool :=
  let n := 2^j * p
  (2^n) % n == (2^(2^j)) % n
def checkAll : Bool :=
  (List.range 7).all (fun j => primes.all (fun p => checkPair j p))

theorem msl_fmz_erdos479_campaign_001_R004_L1  : checkAll = true := by decide

-- axiom footprint
#print axioms primes
#print axioms checkPair
#print axioms checkAll
#print axioms msl_fmz_erdos479_campaign_001_R004_L1
