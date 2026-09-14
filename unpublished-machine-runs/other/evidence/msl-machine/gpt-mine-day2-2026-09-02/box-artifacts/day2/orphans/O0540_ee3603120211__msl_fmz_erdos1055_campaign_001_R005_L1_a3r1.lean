import Mathlib

set_option autoImplicit false


def isPrime (n : Nat) : Bool := n ≥ 2 && (List.range (n-1)).all (fun d => d = 0 || d = 1 || n % (d+1) != 0)
def is23Smooth (n : Nat) : Bool := (n > 0) && ((List.range 60).any (fun a => (List.range 60).any (fun b => 2^a * 3^b = n)))
def class1PrimesUpTo199 : List Nat := (List.range 198).filter (fun p => isPrime (p+2) && is23Smooth (p+2)) |>.map (fun p => p+2)
def expected : List Nat := [2,3,5,7,11,13,17,19,23,31,47,53,71,107]
def check : Bool := class1PrimesUpTo199 = expected && (expected.all (fun p => isPrime p && is23Smooth (p+1))) && (List.range 198).map (fun p => p+2) |>.filter (fun p => isPrime p && is23Smooth (p+1)) |>.length = 14

theorem msl_fmz_erdos1055_campaign_001_R005_L1_a3r1  : check = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms is23Smooth
#print axioms class1PrimesUpTo199
#print axioms expected
#print axioms check
#print axioms msl_fmz_erdos1055_campaign_001_R005_L1_a3r1
