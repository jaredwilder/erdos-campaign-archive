import Mathlib

set_option autoImplicit false


def isPrime (n : Nat) : Bool :=
  if n < 2 then false else (List.range (n+1)).all (fun k => k < 2 || k*k > n || n % k != 0)

def isPowerful (m : Nat) : Bool :=
  (List.range (m+2)).all (fun p => !(isPrime p) || m % p != 0 || m % (p*p) == 0)

def powCheck (f : Nat → Nat) (N : Nat) : List Nat :=
  (List.range (N+1)).filter (fun n => n ≥ 1 && isPowerful (f n))

def checkL1 : Prop :=
  powCheck (fun n => 2^n + 1) 12 = [3]
  ∧ powCheck (fun n => 2^n - 1) 12 = [1]
  ∧ powCheck (fun n => n! + 1) 12 = [4, 5, 7]

theorem msl_fmz_erdos936_campaign_001_R012_L1_a1r2  : checkL1 := by native_decide

-- axiom footprint
#print axioms isPrime
#print axioms isPowerful
#print axioms powCheck
#print axioms checkL1
#print axioms msl_fmz_erdos936_campaign_001_R012_L1_a1r2
