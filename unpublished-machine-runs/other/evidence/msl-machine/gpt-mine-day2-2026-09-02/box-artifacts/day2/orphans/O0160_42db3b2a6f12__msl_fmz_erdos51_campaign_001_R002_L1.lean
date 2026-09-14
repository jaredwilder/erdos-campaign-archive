import Mathlib

set_option autoImplicit false


def phi (n : Nat) : Nat := (List.range n).filter (fun d => Nat.gcd d n == 1) |>.length
def check_L1 : Bool :=
  phi 15 == 8 && phi 30 == 8
  && (List.range 15).all (fun m => phi m != 8)

theorem msl_fmz_erdos51_campaign_001_R002_L1  : check_L1 = true := by decide

-- axiom footprint
#print axioms phi
#print axioms check_L1
#print axioms msl_fmz_erdos51_campaign_001_R002_L1
