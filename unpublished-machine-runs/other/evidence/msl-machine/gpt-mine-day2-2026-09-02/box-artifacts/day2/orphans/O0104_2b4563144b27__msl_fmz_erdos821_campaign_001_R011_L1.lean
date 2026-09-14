import Mathlib

set_option autoImplicit false


def phi : Nat → Nat
  | n => (List.range (n+1)).filter (fun a => Nat.gcd a n = 1) |>.length

def check_even_upto (bound : Nat) : Bool :=
  (List.range (bound - 2)).all (fun k =>
    let m := k + 3
    phi m % 2 = 0)

def check_witness : Bool := check_even_upto 10000

theorem msl_fmz_erdos821_campaign_001_R011_L1  : check_witness = true := by native_decide

-- axiom footprint
#print axioms phi
#print axioms check_even_upto
#print axioms check_witness
#print axioms msl_fmz_erdos821_campaign_001_R011_L1
