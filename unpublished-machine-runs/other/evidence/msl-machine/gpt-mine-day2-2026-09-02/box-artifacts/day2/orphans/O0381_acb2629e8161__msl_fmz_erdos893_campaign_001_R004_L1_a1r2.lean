import Mathlib

set_option autoImplicit false


def tau (m : Nat) : Nat := (List.range (m+2)).filter (fun d => m % d == 0) |>.length

def countOdd (m : Nat) : Nat := (List.range (m+2)).filter (fun d => d % 2 == 1 && m % d == 0) |>.length

def checkK (k : Nat) : Bool := tau (2^k - 1) == countOdd (2^k - 1)

def checkAll (n : Nat) : Bool := (List.range (n+1)).all (fun k => checkK k)

theorem msl_fmz_erdos893_campaign_001_R004_L1_a1r2  : checkAll 8 = true := by decide

-- axiom footprint
#print axioms tau
#print axioms countOdd
#print axioms checkK
#print axioms checkAll
#print axioms msl_fmz_erdos893_campaign_001_R004_L1_a1r2
