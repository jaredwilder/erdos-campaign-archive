import Mathlib

set_option autoImplicit false


def isPrime (n : Nat) : Bool := n >= 2 && (List.range (n-2) |>.all (fun d => n % (d+2) != 0))

def witnessCheck (p : Nat) : Bool := (Nat.pow 2 (3*p) - 8) % (3*p) == 0

def checkRange : Bool :=
  (List.range 96 |>.filter (fun d => isPrime (d+3)))
    |>.all (fun p => witnessCheck p)

theorem msl_fmz_erdos479_campaign_001_R011_L1_a1r1  : checkRange = true := by native_decide

-- axiom footprint
#print axioms isPrime
#print axioms witnessCheck
#print axioms checkRange
#print axioms msl_fmz_erdos479_campaign_001_R011_L1_a1r1
