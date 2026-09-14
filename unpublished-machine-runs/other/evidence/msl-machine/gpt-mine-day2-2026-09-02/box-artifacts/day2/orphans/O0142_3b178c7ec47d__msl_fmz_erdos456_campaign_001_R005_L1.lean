import Mathlib

set_option autoImplicit false


def divides (a b : Nat) : Bool := b % a == 0

def isPrime (n : Nat) : Bool :=
  n == 2 ∨ (1 < n ∧ (List.range (n - 2)).all (fun k => n % (k + 2) != 0))

def checkW3 : Bool :=
  -- p_3 witness: 7 is prime
  isPrime 7
  -- 7 ≡ 1 (mod 3)
  && (7 - 1) % 3 == 0
  -- 7 is the LEAST prime ≡ 1 (mod 3): candidates 3·1+1=4, 3·2+1=7
  -- 4 is composite:
  && !isPrime 4
  -- 7 is prime (restated for the leastness chain)
  && isPrime 7
  -- therefore 3 | p_3 − 1 with p_3 = 7:
  && divides 3 (7 - 1)

theorem msl_fmz_erdos456_campaign_001_R005_L1  : checkW3 = true := by decide

-- axiom footprint
#print axioms divides
#print axioms isPrime
#print axioms checkW3
#print axioms msl_fmz_erdos456_campaign_001_R005_L1
