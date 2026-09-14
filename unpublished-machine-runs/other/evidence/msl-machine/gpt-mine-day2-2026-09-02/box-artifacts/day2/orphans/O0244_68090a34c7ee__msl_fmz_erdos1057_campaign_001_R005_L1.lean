import Mathlib

set_option autoImplicit false


-- Decidable core of Korselt's criterion, checked on explicit factorizations.
-- No primality search, no List.range over large n: pure bounded Nat arithmetic.

def korseltTest (n : Nat) (primes : List Nat) : Bool :=
  -- given the prime factorization p1*p2*...*pk of composite squarefree n,
  -- require each p | n (divisibility) and each (p - 1) | (n - 1)
  primes.all (fun p => n % p == 0) &&
  primes.all (fun p => (n - 1) % (p - 1) == 0) &&
  -- squarefree-ness: no p^2 divides n
  primes.all (fun p => n % (p * p) != 0)

def checkKorseltInstances : Bool :=
  -- Carmichael numbers satisfy the criterion:
  korseltTest 561 [3, 11, 17] &&
  korseltTest 1105 [5, 13, 17] &&
  korseltTest 1729 [7, 13, 19] &&
  korseltTest 2465 [5, 17, 29] &&
  korseltTest 6601 [7, 23, 41] &&
  -- non-Carmichael composites fail it:
  -- 341 = 11 * 31: 340 % 30 = 10 != 0
  !korseltTest 341 [11, 31] &&
  -- 15 = 3 * 5: 14 % 4 = 2 != 0
  !korseltTest 15 [3, 5] &&
  -- 21 = 3 * 7: 20 % 6 = 2 != 0
  !korseltTest 21 [3, 7] &&
  -- non-squarefree composite 45 = 3^2 * 5: 45 % 9 = 0, fails squarefree clause
  !korseltTest 45 [3, 5]

theorem msl_fmz_erdos1057_campaign_001_R005_L1  : checkKorseltInstances = true := by decide

-- axiom footprint
#print axioms korseltTest
#print axioms checkKorseltInstances
#print axioms msl_fmz_erdos1057_campaign_001_R005_L1
