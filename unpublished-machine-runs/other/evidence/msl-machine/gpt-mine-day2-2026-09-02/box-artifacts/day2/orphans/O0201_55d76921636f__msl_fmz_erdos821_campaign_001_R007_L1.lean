import Mathlib

set_option autoImplicit false


def tot (m : Nat) : Nat :=
  (List.range m).filter (fun k => Nat.gcd (k+1) m == 1) |>.length

def evenPhiUpTo (bound : Nat) : Bool :=
  (List.range (bound - 2)).all (fun i =>
    let m := i + 3
    (tot m % 2) == 0)

def checkL1 : Bool := evenPhiUpTo 24

theorem msl_fmz_erdos821_campaign_001_R007_L1  : checkL1 = true := by native_decide

-- axiom footprint
#print axioms tot
#print axioms evenPhiUpTo
#print axioms checkL1
#print axioms msl_fmz_erdos821_campaign_001_R007_L1
