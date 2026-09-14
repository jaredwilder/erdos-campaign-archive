import Mathlib

set_option autoImplicit false


def parityOk (n : Nat) (k : Nat) : Bool := (2 ^ n + k) % 2 == 1

def checkL1 : Bool :=
  (List.range 63).all fun i =>
    let n := i + 2
    n % 2 == 0 && ([-7, -5, -3, 3, 5, 7].all fun j => parityOk n (Nat.natAbs j))

theorem msl_fmz_erdos479_campaign_001_R012_L1_a1r2  : checkL1 = true := by decide

-- axiom footprint
#print axioms parityOk
#print axioms checkL1
#print axioms msl_fmz_erdos479_campaign_001_R012_L1_a1r2
