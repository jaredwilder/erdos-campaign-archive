import Mathlib

set_option autoImplicit false


-- Powerfulness of m is decided against its complete prime factorization,
-- given explicitly as (prime, exponent) pairs, all computed by hand trial division.
-- isPowerfulFactorization: m is powerful iff every prime exponent is >= 2.

def Factorization := List (Nat × Nat)

def exponentsAtLeastTwo (f : Factorization) : Bool :=
  f.all (fun pe => pe.2 >= 2)

-- Factorizations obtained by exact trial division:
--   9    = 3^2
--   25   = 5^2
--   121  = 11^2
--   5041 = 71^2
-- (Primality of 3, 5, 11, 71: none is divisible by any prime <= its square root:
--  3: none <2; 5: none <3; 11: not by 2,3; 71: not by 2,3,5,7. Encoded below.)

def prime3 : Bool := !(2 <= 3 && 3 % 2 == 0)
def prime5 : Bool := !(2 <= 5 && 5 % 2 == 0) && !(3 <= 5 && 5 % 3 == 0)
def prime11 : Bool := !(2 <= 11 && 11 % 2 == 0) && !(3 <= 11 && 11 % 3 == 0)
def prime71 : Bool :=
  !(2 <= 71 && 71 % 2 == 0) && !(3 <= 71 && 71 % 3 == 0) &&
  !(5 <= 71 && 71 % 5 == 0) && !(7 <= 71 && 71 % 7 == 0)

def recon : Factorization -> Nat
  | [] => 1
  | (p, e) :: rest => p ^ e * recon rest

def f9 : Factorization   := [(3, 2)]
def f25 : Factorization  := [(5, 2)]
def f121 : Factorization := [(11, 2)]
def f5041 : Factorization := [(71, 2)]

def checkWitnesses : Bool :=
  prime3 && prime5 && prime11 && prime71 &&
  exponentsAtLeastTwo f9 && recon f9 == 9 &&
  exponentsAtLeastTwo f25 && recon f25 == 25 &&
  exponentsAtLeastTwo f121 && recon f121 == 121 &&
  exponentsAtLeastTwo f5041 && recon f5041 == 5041

theorem msl_fmz_erdos936_campaign_001_R001_L1  : checkWitnesses = true := by decide

-- axiom footprint
#print axioms Factorization
#print axioms exponentsAtLeastTwo
#print axioms prime3
#print axioms prime5
#print axioms prime11
#print axioms prime71
#print axioms recon
#print axioms f9
#print axioms f25
#print axioms f121
#print axioms f5041
#print axioms checkWitnesses
#print axioms msl_fmz_erdos936_campaign_001_R001_L1
