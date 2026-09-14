import Mathlib

set_option autoImplicit false


def isPrime (n : Nat) : Bool :=
  n >= 2 && ((List.range n).drop 2).all (fun d => n % d != 0)

def primes : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
   157, 163, 167, 173, 179, 181, 191, 193, 197, 199]

-- L1's primality/indexing recheck: every listed entry is prime, and the list is
-- EXACTLY the primes below 200 (no omission, no intrusion) in 1-indexed order.
def primeTableCheck : Bool :=
  primes.all isPrime && ((List.range 200).filter isPrime) == primes

def p (k : Nat) : Nat := primes.getD (k - 1) 0

-- f(n) = min over 1 <= i < n of (p_{n+i} + p_{n-i}), exact Nat minimization
def f (n : Nat) : Nat :=
  ((List.range n).drop 1).foldl
    (fun acc i => Nat.min acc (p (n + i) + p (n - i)))
    (p (n + 1) + p (n - 1))

-- -6 <= f(n) - 2 p_n <= +2 for all 2 <= n <= 20, in exact Nat arithmetic
def boundCheck : Bool :=
  ((List.range 21).drop 2).all
    (fun n => (2 * p n <= f n + 6) && (f n <= 2 * p n + 2))

def check_L1_fragment : Bool := primeTableCheck && boundCheck

theorem msl_fmz_erdos454_campaign_001_R010_L1  : check_L1_fragment = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms primes
#print axioms primeTableCheck
#print axioms p
#print axioms f
#print axioms boundCheck
#print axioms check_L1_fragment
#print axioms msl_fmz_erdos454_campaign_001_R010_L1
