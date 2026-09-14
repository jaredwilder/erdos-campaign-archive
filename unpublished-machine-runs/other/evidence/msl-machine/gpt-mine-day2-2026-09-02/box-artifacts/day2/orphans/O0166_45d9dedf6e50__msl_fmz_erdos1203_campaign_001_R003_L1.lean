import Mathlib

set_option autoImplicit false


def primes : List Nat := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89]
def P : Nat := primes.foldl (· * ·) 1
def isPrimeAux (n : Nat) : Nat → Bool
  | 0 => false
  | Nat.succ k =>
      let d := k + 2
      if d * d > n then true else if n % d == 0 then false else isPrimeAux n k
def isPrime (n : Nat) : Bool :=
  if n < 2 then false else if n == 2 then true else if n % 2 == 0 then false else isPrimeAux n (n/2 - 1)
def checkCounterexample : Bool :=
  primes.all isPrime
  ∧ primes.length == 24
  ∧ (prises-drop) P == primes.foldl (· * ·) 1
  ∧ primes.all (fun p => P % p == 0)
  ∧ primes.eraseDups == primes
  ∧ 24 * 9405 > 2 * 109862

theorem msl_fmz_erdos1203_campaign_001_R003_L1  : checkCounterexample = true := by decide

-- axiom footprint
#print axioms primes
#print axioms P
#print axioms isPrimeAux
#print axioms isPrime
#print axioms checkCounterexample
#print axioms msl_fmz_erdos1203_campaign_001_R003_L1
