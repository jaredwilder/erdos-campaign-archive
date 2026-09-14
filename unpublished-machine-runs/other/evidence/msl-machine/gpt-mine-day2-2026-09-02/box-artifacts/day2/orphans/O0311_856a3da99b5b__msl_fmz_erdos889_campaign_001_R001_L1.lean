import Mathlib

set_option autoImplicit false


def divides (d m : Nat) : Bool := m % d == 0

def isPrime (n : Nat) : Bool :=
  n ≥ 2 && ((List.range (n+1)).filter (fun d => d ≥ 2 && divides d n)).length == 1

def countPrimeFactorsGt (n k : Nat) : Nat :=
  (List.range (n+1)).filter (fun d => d > k && divides d n && isPrime d) |>.length

-- v(n,k) counts prime factors of n+k exceeding k
def v (n : Nat) (k : Nat) : Nat := countPrimeFactorsGt (n+k) k

def check_L1 : Bool := v 1 0 == 0

theorem msl_fmz_erdos889_campaign_001_R001_L1  : check_L1 = true := by decide

-- axiom footprint
#print axioms divides
#print axioms isPrime
#print axioms countPrimeFactorsGt
#print axioms v
#print axioms check_L1
#print axioms msl_fmz_erdos889_campaign_001_R001_L1
