import Mathlib

set_option autoImplicit false


def isPrime (n : Nat) : Bool :=
  n >= 2 && ((List.range (n - 2)).all (fun d => n % (d + 2) != 0))

def primeSquareReps (n : Nat) : Nat :=
  ((List.range (n + 1)).filterFun (fun p => isPrime p)).filterFun (fun p =>
    ((List.range (n + 1)).filterFun (fun q => isPrime q && p <= q && p * p + q * q == n)).length > 0).length
-- count of unordered pairs {p, q} of primes with p^2 + q^2 = n, p <= q:
def countReps (n : Nat) : Nat :=
  ((List.range (Nat.sqrt n + 1)).filter (fun p => isPrime p &&
    let r := n - p * p
    Nat.sqrt r * Nat.sqrt r == r && isPrime (Nat.sqrt r) && p <= Nat.sqrt r)).length

def check650 : Bool := countReps 650 == 2

theorem msl_fmz_erdos979_campaign_001_R002_L1_a1r1  : check650 = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms primeSquareReps
#print axioms countReps
#print axioms check650
#print axioms msl_fmz_erdos979_campaign_001_R002_L1_a1r1
