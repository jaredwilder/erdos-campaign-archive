import Mathlib

set_option autoImplicit false


def isPrime (n : Nat) : Bool := n ≥ 2 && (List.range (n+1)).all (fun d => d < 2 || d*d > n || n % d != 0)
def is23Smooth (n : Nat) : Bool := n > 0 && ((List.range 8).any (fun a => (List.range 5).any (fun b => 2^a * 3^b = n)))
def expected : List Nat := [2,3,5,7,11,13,17,19,23,31,47,53,71,107]
def computed : List Nat := (List.range 198).filter (fun m => isPrime (m+2) && is23Smooth (m+1))
def check : Bool := computed = expected && expected.all (fun p => isPrime p && is23Smooth (p+1)) && computed.length = 14

theorem msl_fmz_erdos1055_campaign_001_R005_L1_a3r2  : check = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms is23Smooth
#print axioms expected
#print axioms computed
#print axioms check
#print axioms msl_fmz_erdos1055_campaign_001_R005_L1_a3r2
