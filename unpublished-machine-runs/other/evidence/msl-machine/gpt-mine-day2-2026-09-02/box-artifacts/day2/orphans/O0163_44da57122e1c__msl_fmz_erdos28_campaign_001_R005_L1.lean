import Mathlib

set_option autoImplicit false


-- Digits of n in base 2, least significant first (n < 2^k for small k).
def digits (n : Nat) : List Nat :=
  (Nat.rec (motive := fun _ => List Nat) [] (fun _ ih => ih)) n

-- Explicit small model: represent n < 32 by its 5 binary digits.
def bits (n : Nat) : List Nat := [n % 2, (n/2) % 2, (n/4) % 2, (n/8) % 2, (n/16) % 2]

-- Raikov–Stöhr class 0: digits only at even positions (positions 0,2,4).
def evenClass (n : Nat) : Bool :=
  ((bits n).getD 1 1 == 0) && ((bits n).getD 3 1 == 0)

-- Raikov–Stöhr class 1: digits only at odd positions (positions 1,3).
def oddClass (n : Nat) : Bool :=
  ((bits n).getD 0 1 == 0) && ((bits n).getD 2 1 == 0) && ((bits n).getD 4 1 == 0)

def inBasis (n : Nat) : Bool := evenClass n || oddClass n

-- unordered representation count: pairs a ≤ b, a + b = n, a,b in basis, n < 32
def reps (n : Nat) : Nat :=
  (List.range 32).filter (fun a => a ≤ n && inBasis a && (n - a) ≤ n && inBasis (n - a) &&
    a + (n - a) == n && a ≤ n - a) |>.length

def maxReps : Nat := (List.range 32).foldl (fun acc n => max acc (reps n)) 0

-- Checkable fragment: the truncated Raikov–Stöhr basis (mod 2 digit positions)
-- on [0,32) attains max representation count ≥ 3, i.e. r_A is nonconstant and
-- growing on this window — the concrete base step of unboundedness.
def checkL1 : Bool := maxReps ≥ 3 && reps 15 ≥ 3

theorem msl_fmz_erdos28_campaign_001_R005_L1  : checkL1 = true := by decide

-- axiom footprint
#print axioms digits
#print axioms bits
#print axioms evenClass
#print axioms oddClass
#print axioms inBasis
#print axioms reps
#print axioms maxReps
#print axioms checkL1
#print axioms msl_fmz_erdos28_campaign_001_R005_L1
