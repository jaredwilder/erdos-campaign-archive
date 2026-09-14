import Mathlib

set_option autoImplicit false


def isPrime : Nat → Bool
  | 0 => false
  | 1 => false
  | n => (List.range n).all (fun k => k ≤ 1 ∨ n % k ≠ 0)

def primesUpTo (p : Nat) : List Nat :=
  (List.range (p+1)).filter isPrime

def hasTwinPair (p : Nat) : Bool :=
  (primesUpTo p).any (fun q1 => (primesUpTo p).any (fun q2 => q1 = q2 + 2))

-- n = 2 ≤ p - 3 requires p ≥ 5; the lemma's reduction: any p ≥ 5 valid for n = 2
-- (2 = q1 - q2, primes ≤ p) forces a twin pair. Check the reduction on p ∈ [5, 20].
def checkReduction : Bool :=
  (List.range 16).all (fun j => hasTwinPair (5 + j))

theorem msl_fmz_erdos17_campaign_001_R001_L1  : checkReduction = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms primesUpTo
#print axioms hasTwinPair
#print axioms checkReduction
#print axioms msl_fmz_erdos17_campaign_001_R001_L1
