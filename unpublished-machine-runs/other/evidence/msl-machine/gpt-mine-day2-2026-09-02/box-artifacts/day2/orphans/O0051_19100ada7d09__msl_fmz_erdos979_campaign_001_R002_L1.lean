import Mathlib

set_option autoImplicit false



def primes1mod4 : List Nat := [5, 13, 17, 29, 37, 41, 53, 61, 73, 89]
def N : Nat := primes1mod4.foldl (· * ·) 1
-- count unordered multiset representations {a,b} with a^2+b^2 = n, a,b prime is NOT needed for the classical bound; we count the divisor-theorem reps
partial def reps (n : Nat) : List (Nat × Nat) :=
  (List.range (n+1)).filterMap (fun a =>
    let b2 := n - a*a
    if a*a <= n && Nat.sqrt b2 * Nat.sqrt b2 == b2 && Nat.sqrt b2 >= a then some (a, Nat.sqrt b2) else none)
def checkReps : Bool := (reps N).length >= 2^(List.length primes1mod4 - 1)

theorem msl_fmz_erdos979_campaign_001_R002_L1  : checkReps = true := by decide

-- axiom footprint
#print axioms primes1mod4
#print axioms N
#print axioms reps
#print axioms checkReps
#print axioms msl_fmz_erdos979_campaign_001_R002_L1
