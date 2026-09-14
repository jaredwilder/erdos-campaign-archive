import Mathlib

set_option autoImplicit false


def divides (a b : Nat) : Bool := b % a == 0

def isPrime : Nat → Bool
  | 0 => false | 1 => false
  | n => (List.range (n - 2)).all (fun d => !(divides (d + 2) n))

def t2 (p : Nat) : Nat :=
  (List.range (p + 1)).find? (fun m => m ≥ 1 && divides p (m * (m + 1))) |>.getD 0

def check : Bool :=
  ((List.range 100).filter isPrime).filter (fun p => p > 2)
    |>.all (fun p => t2 p == p - 1)

theorem msl_fmz_erdos394_campaign_001_R001_L1  : check = true := by decide

-- axiom footprint
#print axioms divides
#print axioms isPrime
#print axioms t2
#print axioms check
#print axioms msl_fmz_erdos394_campaign_001_R001_L1
