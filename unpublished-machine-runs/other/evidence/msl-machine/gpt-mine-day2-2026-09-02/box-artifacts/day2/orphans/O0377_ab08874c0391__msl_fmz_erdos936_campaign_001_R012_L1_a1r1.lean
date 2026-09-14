import Mathlib

set_option autoImplicit false


def isPrime (n : Nat) : Bool := n ≥ 2 ∧ (List.range (n+1)).all (fun k => k ≤ 1 ∨ k*k > n ∨ n % k ≠ 0)

def isPowerful (m : Nat) : Bool :=
  (List.range (m+1)).all (fun p => p ≤ 1 ∨ m % p ≠ 0 ∨ m % (p*p) == 0)

def powerfulIdx (f : Nat → Nat) (N : Nat) : List Nat :=
  (List.range (N+1)).filter (fun n => n ≥ 1 ∧ isPowerful (f n))

def checkLemmaL1 : Prop :=
  powerfulIdx (fun n => 2^n + 1) 12 = [3]
  ∧ powerfulIdx (fun n => 2^n - 1) 12 = [1]
  ∧ powerfulIdx (fun n => n ! + 1) 12 = [4, 5, 7]

theorem msl_fmz_erdos936_campaign_001_R012_L1_a1r1  : checkLemmaL1 := by native_decide

-- axiom footprint
#print axioms isPrime
#print axioms isPowerful
#print axioms powerfulIdx
#print axioms checkLemmaL1
#print axioms msl_fmz_erdos936_campaign_001_R012_L1_a1r1
