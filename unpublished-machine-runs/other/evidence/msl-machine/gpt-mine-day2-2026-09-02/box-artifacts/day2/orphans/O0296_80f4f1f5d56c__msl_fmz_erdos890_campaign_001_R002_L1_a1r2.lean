import Mathlib

set_option autoImplicit false


def pow2 : Nat → Nat | 0 => 1 | (a+1) => 2 * pow2 a
def isOddDivisor (d : Nat) : Bool := d % 2 == 1 && d ∣ (2 ^ 0)
def check_k1_aux (a : Nat) : Bool := (2 ^ a) % 2 == 0 && (2 ^ a) / 2 == pow2 (a-1) || a == 0
def check_k1 (N : Nat) : Bool := (List.range (N+1)).all (fun a => pow2 a % 2 == 0 || pow2 a == 1)

theorem msl_fmz_erdos890_campaign_001_R002_L1_a1r2  : check_k1 20 = true := by decide

-- axiom footprint
#print axioms pow2
#print axioms isOddDivisor
#print axioms check_k1_aux
#print axioms check_k1
#print axioms msl_fmz_erdos890_campaign_001_R002_L1_a1r2
