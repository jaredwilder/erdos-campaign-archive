import Mathlib

set_option autoImplicit false


def isComposite (n : Nat) : Bool :=
  (List.range n).any (fun d => 1 < d && n % d == 0)

/-- least prime divisor of n, computed by search over d = 2..n (total for n >= 2) -/
def leastPrimeDiv (n : Nat) : Nat :=
  match (List.range (n + 1)).filter (fun d => 1 < d && n % d == 0) with
  | d :: _ => d
  | [] => 0

/-- F(n): max of m + leastPrimeDiv(m) over composite m < n; 0 if no such m. -/
def Fval (n : Nat) : Nat :=
  ((List.range n).filter isComposite).foldl
    (fun acc m => max acc (m + leastPrimeDiv m)) 0

/-- L1 fragment: at n = 5, m = n-1 = 4 is composite and 4 + p(4) = 6 = 5 + 1,
    so F(5) >= 6 = 5 + 1. -/
def checkL1 : Bool :=
  isComposite 4 && leastPrimeDiv 4 == 2 &&
  4 + leastPrimeDiv 4 == 5 + 1 && Fval 5 >= 5 + 1

theorem msl_fmz_erdos385_campaign_001_R003_L1  : checkL1 = true := by decide

-- axiom footprint
#print axioms isComposite
#print axioms leastPrimeDiv
#print axioms Fval
#print axioms checkL1
#print axioms msl_fmz_erdos385_campaign_001_R003_L1
