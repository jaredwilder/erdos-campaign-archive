import Mathlib

set_option autoImplicit false


def isPrime (n : Nat) : Bool :=
  n ≥ 2 && (List.range (n - 2)).all (fun i => n % (i + 2) != 0)

def largestPrimeFactor (n : Nat) : Nat :=
  (List.range n).reverse.find? (fun d => d ≥ 2 && n % d == 0 && isPrime d) |>.getD 0

def pFactor (p k : Nat) : Nat :=
  (List.range (k + 1)).foldl (fun acc i => acc * (p * p + i)) 1

/-- Decidable core of L1: the per-prime condition 'p is prime and p equals
    the largest prime divisor of ∏_{0 ≤ i ≤ k} (p² + i)', evaluated on
    explicit instances. -/
def perPrimeCondition (p k : Nat) : Bool :=
  isPrime p && largestPrimeFactor (pFactor p k) == p

def check_L1_instances : Bool :=
  perPrimeCondition 2 0 && perPrimeCondition 3 0 &&
  perPrimeCondition 5 0 && perPrimeCondition 7 0

theorem msl_fmz_erdos383_campaign_001_R013_L1  : check_L1_instances = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms largestPrimeFactor
#print axioms pFactor
#print axioms perPrimeCondition
#print axioms check_L1_instances
#print axioms msl_fmz_erdos383_campaign_001_R013_L1
