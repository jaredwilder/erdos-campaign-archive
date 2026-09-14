import Mathlib

set_option autoImplicit false


def bval (N : Nat) : Nat := ((2*N + 1 + Nat.sqrt (8*N+1)) / 2)

def checkvals : Bool :=
  (List.range 8).all fun N =>
    let b := bval N
    (2*b - 1)^2 >= 8*N + 1 &&
    (2*(b+1) - 1)^2 < 8*N + 1 &&
    match N with
    | 0 => b = 1 | 1 => b = 2 | 2 => b = 2 | 3 => b = 3
    | 4 => b = 3 | 5 => b = 4 | 6 => b = 4 | 7 => b = 4

theorem msl_fmz_erdos170_campaign_001_R016_L1_a1r1  : checkvals = true := by decide

-- axiom footprint
#print axioms bval
#print axioms checkvals
#print axioms msl_fmz_erdos170_campaign_001_R016_L1_a1r1
