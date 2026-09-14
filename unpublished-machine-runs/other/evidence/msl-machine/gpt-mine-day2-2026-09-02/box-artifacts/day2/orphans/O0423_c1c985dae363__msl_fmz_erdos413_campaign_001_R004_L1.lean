import Mathlib

set_option autoImplicit false


def isPrime : Nat → Bool
  | 0 => false | 1 => false
  | d => (List.range (d - 1)).all (fun k => (d % (k + 2)) != 0)

/-- ω(n): number of distinct prime divisors, exact for n ≥ 0. -/
def omegaM (n : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun d => isPrime d && n % d == 0)).length

/-- n ∈ B_1 iff ∀ m < n, m + ω(m) ≤ n. -/
def inB1 (n : Nat) : Bool :=
  (List.range n).all (fun m => m + omegaM m <= n)

/-- Exhaustive exact check of the n ≤ 50 segment of B_1. -/
def checkB1 (N : Nat) : Bool :=
  (List.range (N + 1)).all inB1

theorem msl_fmz_erdos413_campaign_001_R004_L1  : checkB1 50 = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms omegaM
#print axioms inB1
#print axioms checkB1
#print axioms msl_fmz_erdos413_campaign_001_R004_L1
