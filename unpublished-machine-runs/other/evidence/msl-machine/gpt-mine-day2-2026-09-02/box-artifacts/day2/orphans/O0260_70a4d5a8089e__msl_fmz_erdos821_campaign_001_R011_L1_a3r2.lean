import Mathlib

set_option autoImplicit false


def phi (m : Nat) : Nat := (List.range (m+1)).filter (fun a => Nat.gcd a m == 1) |>.length

def checkEvenPhi (bound : Nat) : Bool :=
  (List.range (bound - 2)).all (fun i =>
    let m := i + 3
    phi m % 2 == 0)

theorem msl_fmz_erdos821_campaign_001_R011_L1_a3r2  : checkEvenPhi 100 = true := by decide

-- axiom footprint
#print axioms phi
#print axioms checkEvenPhi
#print axioms msl_fmz_erdos821_campaign_001_R011_L1_a3r2
