import Mathlib

set_option autoImplicit false


def isPrime (n : Nat) : Bool :=
  n >= 2 && (List.range n).drop 2 |>.all (fun d => d * d > n || n % d != 0)

def countReps (n : Nat) : Nat :=
  (List.range (Nat.sqrt n + 1)).filter (fun p =>
    isPrime p &&
    let r := n - p * p
    let q := Nat.sqrt r
    q * q == r && isPrime q && p <= q) |>.length

def check650 : Bool := countReps 650 == 2

theorem msl_fmz_erdos979_campaign_001_R002_L1_a1r2  : check650 = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms countReps
#print axioms check650
#print axioms msl_fmz_erdos979_campaign_001_R002_L1_a1r2
